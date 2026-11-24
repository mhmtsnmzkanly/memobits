//! Type checks for primitives and fixed arrays. Executable IR supports arrays of primitive,
//! struct/tuple, enum and nested-array elements (literal, repetition, indexing, element, row and
//! whole-array assignment, array parameters, results and `if`/block results), subject to backend
//! storage gates for owning values.
//! Name resolution across modules and ownership checking are separate passes.
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;

use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, Span};
use memobits_ir::{
    Access as IrAccess, ErrorAncestry, FunctionId, LocalId, ParameterType, Primitive, Signature,
    Type as IrType, TypeId,
};
use memobits_project::Project;
use memobits_resolve::Resolution;
use memobits_syntax::{
    Access, Block, Expr, ExprKind, FieldInit, FieldPattern, GenericParameter, GenericParameterKind,
    ItemKind, MatchArm, Module, Parameter, Pattern, PatternKind, Statement, StatementKind,
    TupleBinding, Type, WhereBound,
};

mod arrays;
mod interfaces;
mod lists;
mod operations;
mod patterns;
mod templates;
mod typetable;
use interfaces::qualified_interface;
use memobits_syntax::templates::{self as registry, Template};
use operations::{floating, int_limit, integer, numeric};
use patterns::ConstructorNames;
use templates::ResolvedArgument;
use typetable::{StructInfo, TypeTable, VariantInfo};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum CheckMode {
    Types,
    Execution,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty {
    Primitive(&'static str),
    String,
    List(Box<Ty>),
    Array(Box<Ty>, u32),
    /// A struct, by index in the type table, with its name for messages.
    Struct(u32, Rc<str>),
    /// A tuple occurrence with recursively scoped aliases. The id remains the
    /// canonical identity of its ordered element types.
    Tuple(u32, Rc<str>, TupleAliases),
    /// An enum, by index in the same table as structs, with its name.
    Enum(u32, Rc<str>),
    Reference {
        access: IrAccess,
        inner: Box<Ty>,
        origin: ReferenceOrigin,
    },
    Function(Vec<FunctionParameter>, Box<Ty>),
    Never,
    Error,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct TupleAliases {
    pub(super) labels: Vec<Option<String>>,
    pub(super) nested: Vec<Option<Box<TupleAliases>>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum ReferenceOrigin {
    Binding(usize),
    Temporary,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct FunctionParameter {
    access: IrAccess,
    ty: Ty,
}
#[derive(Clone)]
struct ExtensionCandidate {
    module: String,
    span: Span,
    visible: bool,
    local: bool,
    target: Ty,
    interface: Option<String>,
    associated_types: HashMap<String, Ty>,
    methods: HashMap<String, (Access, Vec<FunctionParameter>, Ty, Span, FunctionId)>,
    public_methods: HashSet<String>,
    generic_target: Option<Type>,
    generic_parameters: Vec<GenericParameter>,
    generic_methods: Vec<memobits_syntax::InterfaceMethod>,
    declaration_imports: HashMap<String, String>,
}

#[derive(Clone)]
struct GenericFunctionTemplate {
    module: String,
    name: String,
    span: Span,
    generic_parameters: Vec<GenericParameter>,
    bounds: Vec<WhereBound>,
    bound_interfaces: Vec<String>,
    parameters: Vec<Parameter>,
    result: Option<Type>,
}

#[derive(Clone)]
struct GenericSpecialization {
    template: GenericFunctionTemplate,
    substitution: HashMap<String, Ty>,
    const_substitution: HashMap<String, u32>,
    evidence: Vec<GenericEvidence>,
    signature: Signature,
    id: FunctionId,
    key: String,
}

#[derive(Clone)]
struct GenericMethodSpecialization {
    module: String,
    extension_span: Span,
    method: memobits_syntax::InterfaceMethod,
    target: Ty,
    substitution: HashMap<String, Ty>,
    const_substitution: HashMap<String, u32>,
    id: FunctionId,
    key: String,
}

#[derive(Clone)]
struct GenericEvidence {
    interface: String,
    candidate: ExtensionCandidate,
}

#[derive(Default)]
struct SpecializationRegistry {
    next_id: u32,
    by_key: HashMap<String, FunctionId>,
    requests: Vec<GenericSpecialization>,
    method_requests: Vec<GenericMethodSpecialization>,
    method_by_key: HashMap<String, FunctionId>,
}
const UNIT: Ty = Ty::Primitive("Unit");
const BOOL: Ty = Ty::Primitive("bool");
const I32: Ty = Ty::Primitive("i32");
const F64: Ty = Ty::Primitive("f64");
const U8: Ty = Ty::Primitive("u8");
const U32: Ty = Ty::Primitive("u32");
fn ir_access(access: Access) -> IrAccess {
    match access {
        Access::Owned => IrAccess::Owned,
        Access::Borrow => IrAccess::Borrow,
        Access::Share => IrAccess::Share,
    }
}

fn is_plain_type_parameter(ty: &Type, name: &str) -> bool {
    ty.path == [name] && ty.arguments.is_empty()
}

fn is_associated_projection(ty: &Type, name: &str) -> bool {
    ty.path.len() == 2 && ty.path[0] == name && ty.arguments.is_empty()
}

fn supported_generic_function(template: &GenericFunctionTemplate) -> bool {
    if template.bounds.len() > 1
        || template.bounds.iter().any(|bound| {
            bound.parameter
                != template
                    .generic_parameters
                    .first()
                    .map_or("", |p| p.name.as_str())
                || !bound.interface.arguments.is_empty()
        })
    {
        return false;
    }
    let (type_name, const_name, array_mode) = match template.generic_parameters.as_slice() {
        [generic] if matches!(generic.kind, GenericParameterKind::Type) => {
            (&generic.name, None, false)
        }
        [generic, constant]
            if matches!(generic.kind, GenericParameterKind::Type)
                && matches!(&constant.kind, GenericParameterKind::Const(ty) if ty.path == ["u32"] && ty.arguments.is_empty()) =>
        {
            (&generic.name, Some(constant.name.as_str()), true)
        }
        _ => return false,
    };
    if template.parameters.is_empty() {
        return false;
    }
    if template.parameters.iter().any(|parameter| {
        parameter.access != Access::Owned
            || (if array_mode {
                !is_array_generic_pattern(&parameter.ty, type_name, const_name.unwrap())
                    && !is_associated_projection(&parameter.ty, type_name)
                    && (type_mentions_parameter(&parameter.ty, type_name)
                        || type_mentions_const(&parameter.ty, const_name.unwrap()))
            } else {
                type_mentions_parameter(&parameter.ty, type_name)
                    && !is_plain_type_parameter(&parameter.ty, type_name)
                    && !is_associated_projection(&parameter.ty, type_name)
            })
    }) {
        return false;
    }
    if !template.parameters.iter().any(|parameter| {
        if array_mode {
            is_array_generic_pattern(&parameter.ty, type_name, const_name.unwrap())
        } else {
            is_plain_type_parameter(&parameter.ty, type_name)
        }
    }) {
        return false;
    }
    let Some(result) = &template.result else {
        return false;
    };
    let valid_result = if array_mode {
        is_array_generic_pattern(result, type_name, const_name.unwrap())
    } else {
        is_plain_type_parameter(result, type_name)
            || is_associated_projection(result, type_name)
            || !type_mentions_parameter(result, type_name)
    };
    if !valid_result {
        return false;
    }
    valid_result
}

fn is_array_generic_pattern(ty: &Type, type_name: &str, const_name: &str) -> bool {
    ty.path.as_slice() == ["array"]
        && matches!(ty.arguments.as_slice(), [memobits_syntax::TypeArgument::Type(element), memobits_syntax::TypeArgument::Const(length)]
            if is_plain_type_parameter(element, type_name) && length == const_name)
}

fn type_mentions_const(ty: &Type, name: &str) -> bool {
    ty.arguments.iter().any(|argument| match argument {
        memobits_syntax::TypeArgument::Const(found) => found == name,
        memobits_syntax::TypeArgument::Type(ty) => type_mentions_const(ty, name),
        memobits_syntax::TypeArgument::TupleField { ty, .. } => type_mentions_const(ty, name),
        memobits_syntax::TypeArgument::Reference { referent, .. } => {
            type_mentions_const(referent, name)
        }
        memobits_syntax::TypeArgument::Integer(_) => false,
    })
}

fn type_mentions_parameter(ty: &Type, name: &str) -> bool {
    ((ty.path.as_slice() == [name] || ty.path.first().is_some_and(|segment| segment == name))
        && ty.arguments.is_empty())
        || ty.arguments.iter().any(|argument| match argument {
            memobits_syntax::TypeArgument::Type(ty) => type_mentions_parameter(ty, name),
            memobits_syntax::TypeArgument::TupleField { ty, .. } => {
                type_mentions_parameter(ty, name)
            }
            memobits_syntax::TypeArgument::Reference { referent, .. } => {
                type_mentions_parameter(referent, name)
            }
            _ => false,
        })
}
fn access_name(access: IrAccess) -> &'static str {
    match access {
        IrAccess::Owned => "owned",
        IrAccess::Borrow => "borrow",
        IrAccess::Share => "share",
    }
}
fn read_type(ty: Ty) -> Ty {
    match ty {
        Ty::Reference { inner, .. } => *inner,
        other => other,
    }
}
fn with_tuple_aliases(ty: Ty, aliases: Option<&TupleAliases>) -> Ty {
    match (ty, aliases) {
        (Ty::Tuple(id, name, _), Some(aliases)) => Ty::Tuple(id, name, aliases.clone()),
        (ty, _) => ty,
    }
}
fn compatible(actual: &Ty, expected: &Ty) -> bool {
    match (actual, expected) {
        (
            Ty::Reference {
                access: actual_access,
                inner: actual_inner,
                ..
            },
            Ty::Reference {
                access: expected_access,
                inner: expected_inner,
                ..
            },
        ) => {
            compatible(actual_inner, expected_inner)
                && match expected_access {
                    IrAccess::Owned => false,
                    IrAccess::Borrow => {
                        matches!(actual_access, IrAccess::Borrow | IrAccess::Share)
                    }
                    IrAccess::Share => *actual_access == IrAccess::Share,
                }
        }
        (Ty::Tuple(actual, _, _), Ty::Tuple(expected, _, _)) => actual == expected,
        _ => {
            actual == expected
                || matches!(actual, Ty::Error | Ty::Never)
                || matches!(expected, Ty::Error)
        }
    }
}
fn reference_access_matches(actual: &Ty, access: IrAccess) -> bool {
    matches!(
        (access, actual),
        (
            IrAccess::Borrow,
            Ty::Reference {
                access: IrAccess::Borrow | IrAccess::Share,
                ..
            },
        ) | (
            IrAccess::Share,
            Ty::Reference {
                access: IrAccess::Share,
                ..
            },
        ) | (_, Ty::Error | Ty::Never)
    )
}
/// Most uncovered example patterns a non-exhaustive `match` names.
const MAX_MISSING_PATTERNS: usize = 4;

/// A pattern as written, for diagnostics.
fn render_pattern(pattern: &Pattern) -> String {
    match &pattern.kind {
        PatternKind::Wildcard => "_".into(),
        PatternKind::Binding(name) => name.clone(),
        PatternKind::Variant { path, slots } if slots.is_empty() => path.join("::"),
        PatternKind::Variant { path, slots } => format!(
            "{}({})",
            path.join("::"),
            slots
                .iter()
                .map(render_pattern)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        PatternKind::Tuple(elements) if elements.len() == 1 => {
            format!("({},)", render_pattern(&elements[0]))
        }
        PatternKind::Tuple(elements) => format!(
            "({})",
            elements
                .iter()
                .map(render_pattern)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn name(ty: &Ty) -> String {
    match ty {
        Ty::Primitive(s) => s.to_string(),
        Ty::String => "string".into(),
        Ty::List(element) => format!("List<{}>", name(element)),
        Ty::Array(element, count) => format!("array<{}, {count}>", name(element)),
        Ty::Struct(_, name) | Ty::Tuple(_, name, _) | Ty::Enum(_, name) => name.to_string(),
        Ty::Function(..) => "function".into(),
        Ty::Reference { access, inner, .. } => {
            format!("{} {}", access_name(*access), name(inner))
        }
        Ty::Never => "never".into(),
        Ty::Error => "unknown".into(),
    }
}
/// The named local at the root of a projection chain: any mix of indexing and
/// field access such as `a[i].pts[j].x`.
fn place_root(expr: &Expr) -> Option<&Vec<String>> {
    match &expr.kind {
        ExprKind::Path(path) => Some(path),
        ExprKind::Index { base, .. } | ExprKind::Field { base, .. } => place_root(base),
        _ => None,
    }
}
fn constant_index(expr: &Expr) -> Option<i128> {
    match &expr.kind {
        ExprKind::Number(raw)
            if raw
                .bytes()
                .all(|byte| byte.is_ascii_digit() || byte == b'_') =>
        {
            raw.replace('_', "").parse().ok()
        }
        ExprKind::Unary { operator, operand } if operator == "-" => {
            constant_index(operand)?.checked_neg()
        }
        _ => None,
    }
}
fn diagnostic(number: u16, span: Span, message: impl Into<String>) -> Diagnostic {
    let mut d = Diagnostic::new(
        DiagnosticCode::new(Category::Type, number).unwrap(),
        Severity::Error,
        message,
    );
    d.span = Some(span);
    d
}
#[derive(Clone, Copy)]
struct Flow {
    falls: bool,
    breaks: bool,
}
impl Flow {
    const NEXT: Self = Self {
        falls: true,
        breaks: false,
    };
    const STOP: Self = Self {
        falls: false,
        breaks: false,
    };
    fn then(self, next: Self) -> Self {
        Self {
            falls: self.falls && next.falls,
            breaks: self.breaks || (self.falls && next.breaks),
        }
    }
}
fn flow_block(block: &Block) -> Flow {
    let mut flow = Flow::NEXT;
    for statement in &block.statements {
        flow = flow.then(match &statement.kind {
            StatementKind::Binding { value, .. }
            | StatementKind::Destructure { value, .. }
            | StatementKind::TupleDestructure { value, .. }
            | StatementKind::Expression(value) => flow_expr(value),
            StatementKind::Assign { target, value, .. } => flow_expr(target).then(flow_expr(value)),
            StatementKind::Return(value) => value
                .as_ref()
                .map_or(Flow::STOP, flow_expr)
                .then(Flow::STOP),
            StatementKind::Loop(body) => Flow {
                falls: flow_block(body).breaks,
                breaks: false,
            },
            StatementKind::ForEach { items, .. } => flow_expr(items),
            StatementKind::Break => Flow {
                falls: false,
                breaks: true,
            },
            StatementKind::Continue => Flow::STOP,
        });
    }
    if let Some(tail) = &block.tail {
        flow = flow.then(flow_expr(tail));
    }
    flow
}
fn flow_expr(expr: &Expr) -> Flow {
    match &expr.kind {
        ExprKind::Number(_)
        | ExprKind::StringLiteral(_)
        | ExprKind::CharLiteral(_)
        | ExprKind::Bool(_)
        | ExprKind::Path(_) => Flow::NEXT,
        ExprKind::Array(elements) => elements
            .iter()
            .fold(Flow::NEXT, |flow, element| flow.then(flow_expr(element))),
        ExprKind::Tuple(elements) => elements.iter().fold(Flow::NEXT, |flow, element| {
            flow.then(flow_expr(&element.value))
        }),
        ExprKind::RepeatArray { value, count } => {
            if count.raw.bytes().all(|byte| byte == b'0' || byte == b'_') {
                Flow::NEXT
            } else {
                flow_expr(value)
            }
        }
        ExprKind::Index { base, index } => flow_expr(base).then(flow_expr(index)),
        ExprKind::Unary { operand, .. } | ExprKind::Cast { value: operand, .. } => {
            flow_expr(operand)
        }
        ExprKind::Binary {
            operator,
            left,
            right,
        } => {
            let left_flow = flow_expr(left);
            let right_flow = flow_expr(right);
            if matches!(operator.as_str(), "&&" | "||") {
                Flow {
                    falls: left_flow.falls,
                    breaks: left_flow.breaks || (left_flow.falls && right_flow.breaks),
                }
            } else {
                left_flow.then(right_flow)
            }
        }
        ExprKind::Call {
            callee, arguments, ..
        } => arguments
            .iter()
            .fold(flow_expr(callee), |flow, arg| flow.then(flow_expr(arg))),
        ExprKind::Field { base, .. } => flow_expr(base),
        ExprKind::Struct { fields, .. } => fields
            .iter()
            .fold(Flow::NEXT, |flow, field| flow.then(flow_expr(&field.value))),
        ExprKind::Block(block) => flow_block(block),
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let condition = flow_expr(condition);
            let then_flow = flow_block(then_branch);
            let else_flow = else_branch.as_ref().map_or(Flow::NEXT, |e| flow_expr(e));
            condition.then(Flow {
                falls: then_flow.falls || else_flow.falls,
                breaks: then_flow.breaks || else_flow.breaks,
            })
        }
        ExprKind::Match { scrutinee, arms } => {
            let scrutinee = flow_expr(scrutinee);
            let mut falls = arms.is_empty();
            let mut breaks = false;
            for arm in arms {
                let arm_flow = flow_expr(&arm.body);
                falls |= arm_flow.falls;
                breaks |= arm_flow.breaks;
            }
            scrutinee.then(Flow { falls, breaks })
        }
    }
}

/// An expression identity within one checked function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExprId(pub u32);

/// A type fact produced by successful checking. `None` means the expression
/// never yields a value (for example, a block that returns).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpressionFact {
    pub id: ExprId,
    pub span: Span,
    pub ty: Option<IrType>,
    /// Used only while lowering the same borrowed syntax tree.
    pub(crate) node_addr: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalFact {
    pub id: LocalId,
    pub name: String,
    pub ty: IrType,
    /// Parameter access mode; it does not represent permission to rebind.
    pub access: IrAccess,
    /// Whether the local binding itself can be reassigned.
    pub mutable: bool,
    pub span: Span,
    pub(crate) node_addr: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathTarget {
    Local(LocalId),
    Function(FunctionId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PathUse {
    pub expression: ExprId,
    pub target: PathTarget,
    /// Access of a local binding use; function references have no access mode.
    pub access: Option<IrAccess>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SelectedCall {
    pub expression: ExprId,
    pub function: FunctionId,
    pub receiver_access: Access,
    pub signature: Signature,
}

/// A construction of an enum variant. `expression` is the path expression of a
/// unit variant, or the call expression of a payload variant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VariantUse {
    pub expression: ExprId,
    /// Absent when a diverging payload prevents inference of the enum type.
    pub enum_id: Option<TypeId>,
    /// Index into the enum's variants.
    pub variant: u32,
}

/// A checked `match`. `expression` is the match expression; `arms` follow the
/// source order of its arms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatchFact {
    pub expression: ExprId,
    /// The scrutinee is matched in place (a reference, or an element or field
    /// place): nothing is consumed and aggregate payload bindings are borrows.
    pub borrowed: bool,
    pub arms: Vec<MatchArmFact>,
}

impl MatchPattern {
    /// The binding locals of this pattern, in source order.
    pub fn collect_bindings(&self, into: &mut Vec<LocalId>) {
        match self {
            MatchPattern::Wildcard => {}
            MatchPattern::Bind(local) => into.extend(*local),
            MatchPattern::Variant { args, .. } | MatchPattern::Tuple(args) => {
                for arg in args {
                    arg.collect_bindings(into);
                }
            }
        }
    }
}

/// One arm: its checked pattern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatchArmFact {
    pub pattern: MatchPattern,
}

/// A checked pattern at any depth. The type each node matches is implied by
/// the scrutinee type and the declarations, so lowering walks both together.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MatchPattern {
    /// `_`: matches anything and binds nothing.
    Wildcard,
    /// A binding: matches anything and binds it to a new local.
    Bind(Option<LocalId>),
    /// A variant of the enum at this position, with one sub-pattern per
    /// payload value.
    Variant {
        variant: u32,
        args: Vec<MatchPattern>,
    },
    /// A tuple, with one sub-pattern per element.
    Tuple(Vec<MatchPattern>),
}

/// Local-to-this-expression tuple alias resolutions used by lowering.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TupleProjectionFact {
    pub(crate) node_addr: usize,
    pub slot: u32,
}

/// Destination slot for each tuple initializer element, in source order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TupleInitializerFact {
    pub(crate) node_addr: usize,
    pub slots: Vec<u32>,
}

/// Facts are indexed by function, then by fresh expression/local identities.
/// The syntax module is deliberately not relabeled as checked syntax.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionFacts {
    pub id: FunctionId,
    pub span: Span,
    /// Original module and declaration name. A specialized function keeps
    /// this source identity while receiving its own collision-free IR name.
    pub(crate) source_module: String,
    pub(crate) source_name: String,
    pub(crate) specialization_key: Option<String>,
    pub signature: Signature,
    pub locals: Vec<LocalFact>,
    pub expressions: Vec<ExpressionFact>,
    pub path_uses: Vec<PathUse>,
    /// Enum variant constructions: a unit variant path or a payload call.
    pub variant_uses: Vec<VariantUse>,
    pub explicit_drops: Vec<ExprId>,
    pub explicit_asserts: Vec<ExprId>,
    pub explicit_replaces: Vec<ExprId>,
    pub explicit_swaps: Vec<ExprId>,
    /// Interface extension selected for each explicitly constrained call.
    pub selected_calls: Vec<SelectedCall>,
    /// User-defined binary operator implementations selected for lowering.
    pub selected_operators: Vec<SelectedCall>,
    /// User-defined compound assignments selected for statement lowering.
    pub selected_assignments: Vec<SelectedCall>,
    /// `match` expressions over owned enums, with the pattern facts lowering needs.
    pub matches: Vec<MatchFact>,
    pub tuple_projections: Vec<TupleProjectionFact>,
    pub tuple_initializers: Vec<TupleInitializerFact>,
    next_expr: u32,
}

/// One declared struct field with its IR type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldFact {
    pub name: String,
    pub ty: IrType,
}

/// One declared enum variant with its payload types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantFact {
    pub name: String,
    pub payload: Vec<IrType>,
}

/// A checked struct or enum definition. `module` is the resolver's module name
/// (`""` for a standalone module); the type's `TypeId` is its index in
/// `TypedModule::types`. A struct has `fields`; an enum (`is_enum`) has
/// `variants`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeFact {
    pub module: String,
    pub name: String,
    pub span: Span,
    pub is_enum: bool,
    pub error_ancestry: Option<ErrorAncestry>,
    pub entry_outcome: Option<memobits_ir::EntryOutcome>,
    pub fields: Vec<FieldFact>,
    pub variants: Vec<VariantFact>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedModule {
    pub functions: Vec<FunctionFacts>,
    pub types: Vec<TypeFact>,
}

fn type_facts(table: &TypeTable) -> Vec<TypeFact> {
    let unit = || IrType::Primitive(Primitive::Unit);
    table
        .definitions()
        .iter()
        .enumerate()
        .map(|(id, info)| TypeFact {
            module: info.module.clone(),
            name: info.name.clone(),
            span: info.span,
            is_enum: info.is_enum,
            error_ancestry: table.error_ancestry(id as u32),
            entry_outcome: match table.enum_template(id as u32).map(|template| template.id) {
                Some(registry::TemplateId::Result) => Some(memobits_ir::EntryOutcome::Result),
                _ => None,
            },
            fields: info
                .fields
                .iter()
                .map(|field| FieldFact {
                    name: field.name.clone(),
                    ty: ir_type(&field.ty).unwrap_or_else(unit),
                })
                .collect(),
            variants: info
                .variants
                .iter()
                .map(|variant| VariantFact {
                    name: variant.name.clone(),
                    payload: variant
                        .payload
                        .iter()
                        .map(|ty| ir_type(ty).unwrap_or_else(unit))
                        .collect(),
                })
                .collect(),
        })
        .collect()
}

fn ir_type(ty: &Ty) -> Option<IrType> {
    Some(match ty {
        Ty::Primitive(name) => IrType::Primitive(match *name {
            "Unit" => Primitive::Unit,
            "bool" => Primitive::Bool,
            "char" => Primitive::Char,
            "i8" => Primitive::I8,
            "i16" => Primitive::I16,
            "i32" => Primitive::I32,
            "i64" => Primitive::I64,
            "u8" => Primitive::U8,
            "u16" => Primitive::U16,
            "u32" => Primitive::U32,
            "u64" => Primitive::U64,
            "f32" => Primitive::F32,
            "f64" => Primitive::F64,
            _ => return None,
        }),
        Ty::Function(parameters, result) => IrType::Function(Signature {
            parameters: parameters
                .iter()
                .map(|p| {
                    Some(ParameterType {
                        access: p.access,
                        ty: ir_type(&p.ty)?,
                    })
                })
                .collect::<Option<Vec<_>>>()?,
            result: Box::new(ir_type(result)?),
        }),
        Ty::Reference { access, inner, .. } => IrType::Reference {
            access: *access,
            inner: Box::new(ir_type(inner)?),
        },
        Ty::List(element) => IrType::List(Box::new(ir_type(element)?)),
        Ty::Array(element, len) => IrType::Array {
            element: Box::new(ir_type(element)?),
            len: *len,
        },
        Ty::Struct(id, _) | Ty::Tuple(id, _, _) => IrType::Struct(TypeId(*id)),
        Ty::Enum(id, _) => IrType::Enum(TypeId(*id)),
        Ty::String => IrType::String,
        Ty::Never | Ty::Error => return None,
    })
}

#[derive(Clone)]
struct Binding {
    ty: Ty,
    /// Rebinding mutability, independent of parameter access.
    mutable: bool,
    /// Parameter access mode retained for future call/loan checking.
    access: IrAccess,
    id: Option<LocalId>,
    origin: usize,
}
struct Checker {
    /// `[build] alloc`: heap-producing string operations are errors when false.
    alloc: bool,
    diagnostics: Vec<Diagnostic>,
    lowering: bool,
    /// Addresses of expressions in an owned-value position (binding initialiser,
    /// `=` right-hand side, return/tail value, owned aggregate argument, array
    /// element) that may be a whole aggregate: array and struct literals,
    /// repetitions, named locals, and the tails of `if`/block expressions in
    /// such a position.
    allowed_arrays: HashSet<usize>,
    concat_destination: Option<usize>,
    share_field_assignment: bool,
    parameter_origins: HashSet<usize>,
    temporary_borrow_argument: Option<usize>,
    /// Field reads that already failed; they are not also reported as extractions.
    failed_fields: HashSet<usize>,
    /// Address of the path expression currently checked as an index or field base.
    index_base: usize,
    /// Module whose names and field visibility are being checked.
    module: String,
    table: Rc<TypeTable>,
    /// Concrete semantic substitutions for a generic function body. These are
    /// populated only by call-site inference; declaration spelling is never
    /// used to guess a runtime argument type.
    generic_types: HashMap<String, Ty>,
    generic_consts: HashMap<String, u32>,
    generic_evidence: Vec<GenericEvidence>,
    generic_functions: HashMap<String, GenericFunctionTemplate>,
    specialization_registry: Option<Rc<RefCell<SpecializationRegistry>>>,
    generic_path_targets: HashMap<usize, (FunctionId, Ty)>,
    functions: HashMap<String, Ty>,
    function_ids: HashMap<String, FunctionId>,
    facts: Option<FunctionFacts>,
    qualified_functions: HashMap<String, Ty>,
    qualified_function_ids: HashMap<String, FunctionId>,
    imports: HashMap<String, String>,
    extension_candidates: Vec<ExtensionCandidate>,
    scopes: Vec<HashMap<String, Binding>>,
    result: Ty,
}
impl Checker {
    fn specialize_inherent_candidate(
        &mut self,
        candidate: &ExtensionCandidate,
        receiver: &Ty,
    ) -> Option<ExtensionCandidate> {
        let target = candidate.generic_target.as_ref()?;
        let (Ty::Struct(id, _) | Ty::Enum(id, _)) = receiver else {
            return None;
        };
        let key = self
            .table
            .generic_definition_key(&candidate.module, target)?;
        if self.table.generic_origin(*id).as_deref() != Some(key.as_str()) {
            return None;
        }
        let arguments = self.table.generic_arguments(*id)?;
        if arguments.len() != candidate.generic_parameters.len() {
            return None;
        }
        let mut substitution = HashMap::new();
        let mut const_substitution = HashMap::new();
        for (parameter, argument) in candidate.generic_parameters.iter().zip(arguments) {
            match (&parameter.kind, argument) {
                (GenericParameterKind::Type, ResolvedArgument::Type(ty)) => {
                    substitution.insert(parameter.name.clone(), ty);
                }
                (GenericParameterKind::Const(_), ResolvedArgument::Integer(value)) => {
                    const_substitution.insert(parameter.name.clone(), value);
                }
                _ => return None,
            }
        }
        let mut type_checker = Checker {
            alloc: self.alloc,
            module: candidate.module.clone(),
            table: Rc::clone(&self.table),
            generic_types: substitution.clone(),
            generic_consts: const_substitution.clone(),
            imports: candidate.declaration_imports.clone(),
            ..checker()
        };
        let mut specialized = candidate.clone();
        specialized.target = receiver.clone();
        specialized.generic_target = None;
        specialized.methods.clear();
        for method in &candidate.generic_methods {
            let parameters: Vec<_> = method
                .parameters
                .iter()
                .map(|parameter| FunctionParameter {
                    access: ir_access(parameter.access),
                    ty: type_checker.type_path(&parameter.ty),
                })
                .collect();
            let result = method
                .result
                .as_ref()
                .map(|ty| type_checker.type_path(ty))
                .unwrap_or(UNIT);
            let base_id = candidate.methods.get(&method.name).map(|entry| entry.4)?;
            let identity = format!(
                "{}:{}:{}:{receiver:?}",
                candidate.module, candidate.span.start, method.name
            );
            let id = if let Some(registry) = &self.specialization_registry {
                let mut registry = registry.borrow_mut();
                if let Some(id) = registry.method_by_key.get(&identity) {
                    *id
                } else {
                    let id = FunctionId(registry.next_id);
                    registry.next_id += 1;
                    registry.method_by_key.insert(identity.clone(), id);
                    registry.method_requests.push(GenericMethodSpecialization {
                        module: candidate.module.clone(),
                        extension_span: candidate.span,
                        method: method.clone(),
                        target: receiver.clone(),
                        substitution: substitution.clone(),
                        const_substitution: const_substitution.clone(),
                        id,
                        key: identity,
                    });
                    id
                }
            } else {
                base_id
            };
            specialized.methods.insert(
                method.name.clone(),
                (method.receiver, parameters, result, method.span, id),
            );
        }
        for error in type_checker.diagnostics {
            self.diagnostics.push(error);
        }
        Some(specialized)
    }

    fn generic_identity_call(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        arguments: &[Expr],
        expected: Option<&Ty>,
    ) -> Ty {
        let ExprKind::Path(path) = &callee.kind else {
            unreachable!("guarded generic function path")
        };
        let template = if path.len() == 1 {
            self.generic_functions.get(&path[0]).cloned()
        } else {
            let expanded = self.imports.get(&path[0]).map_or_else(
                || path.join("::"),
                |target| format!("{}::{}", target, path[1..].join("::")),
            );
            self.generic_functions
                .get(expanded.strip_prefix("self::").unwrap_or(&expanded))
                .cloned()
        };
        let Some(template) = template else {
            return Ty::Error;
        };
        if !supported_generic_function(&template) {
            self.error(
                7,
                template.span,
                format!(
                    "generic function '{}::{}' uses a generic form outside the supported unconstrained direct-type-parameter specialization subset",
                    template.module, template.name
                ),
            );
            for argument in arguments {
                self.expr(argument, None);
            }
            return Ty::Error;
        }
        if arguments.len() != template.parameters.len() {
            self.error(
                10,
                expr.span,
                format!(
                    "expected {} arguments, found {}",
                    template.parameters.len(),
                    arguments.len()
                ),
            );
            for argument in arguments {
                self.expr(argument, None);
            }
            return Ty::Error;
        }
        let type_name = &template.generic_parameters[0].name;
        let const_name = match &template.generic_parameters[1..] {
            [constant] => Some(constant.name.as_str()),
            _ => None,
        };
        let generic_index = template
            .parameters
            .iter()
            .position(|parameter| {
                is_plain_type_parameter(&parameter.ty, type_name)
                    || const_name.is_some_and(|const_name| {
                        is_array_generic_pattern(&parameter.ty, type_name, const_name)
                    })
            })
            .expect("supported generic template contains an inference parameter");
        // Check every written argument before the inference argument in source
        // order. Generic-shaped parameters cannot receive a concrete expected
        // type yet, so infer their expression type and validate it after the
        // specialization has been formed.
        let mut checked_argument_types = vec![None; arguments.len()];
        let mut diverges = false;
        for index in 0..generic_index {
            let argument = &arguments[index];
            let parameter = &template.parameters[index];
            let is_generic_shape = type_mentions_parameter(&parameter.ty, type_name)
                || const_name.is_some_and(|name| type_mentions_const(&parameter.ty, name));
            if !is_generic_shape {
                let expected = self.type_path(&parameter.ty);
                if matches!(
                    expected,
                    Ty::String
                        | Ty::List(_)
                        | Ty::Array(..)
                        | Ty::Struct(..)
                        | Ty::Tuple(..)
                        | Ty::Enum(..)
                ) {
                    self.allow_array_value(argument);
                }
                let actual = self.expr(argument, Some(&expected));
                self.ensure(&actual, &expected, argument.span);
                diverges |= actual == Ty::Never;
                checked_argument_types[index] = Some(actual);
            } else {
                self.allow_array_value(argument);
                let actual = self.expr(argument, None);
                diverges |= actual == Ty::Never;
                checked_argument_types[index] = Some(actual);
            }
        }
        self.allow_array_value(&arguments[generic_index]);
        let actual = self.expr(&arguments[generic_index], None);
        if actual == Ty::Error {
            return Ty::Error;
        }
        let mut substitution = HashMap::new();
        let mut const_substitution = HashMap::new();
        let array_pattern = const_name.is_some_and(|const_name| {
            is_array_generic_pattern(
                &template.parameters[generic_index].ty,
                type_name,
                const_name,
            )
        });
        let inferred = if actual == Ty::Never {
            // A diverging argument has no value type to infer from. A
            // surrounding expected result can still select the specialization
            // (as with an ordinary diverging call); without one, report the
            // actual unresolved type instead of silently producing Error.
            match expected.filter(|ty| !matches!(ty, Ty::Error | Ty::Never)) {
                Some(Ty::Array(element, length)) if array_pattern => {
                    substitution.insert(type_name.clone(), element.as_ref().clone());
                    const_substitution.insert(
                        const_name
                            .expect("array pattern has a const parameter")
                            .to_owned(),
                        *length,
                    );
                    true
                }
                Some(ty) if !array_pattern => {
                    substitution.insert(type_name.clone(), ty.clone());
                    true
                }
                _ => false,
            }
        } else if array_pattern {
            let const_name = const_name.expect("array pattern has a const parameter");
            match &actual {
                Ty::Array(element, length) => {
                    substitution.insert(type_name.clone(), element.as_ref().clone());
                    const_substitution.insert(const_name.to_owned(), *length);
                    true
                }
                _ => false,
            }
        } else {
            infer_direct_type_parameter(
                &HashSet::from([type_name.clone()]),
                &template.parameters[generic_index].ty,
                &actual,
                &mut substitution,
            )
            .is_ok()
        };
        if !inferred {
            self.error(
                2,
                arguments[generic_index].span,
                if actual == Ty::Never {
                    "cannot infer the generic function type from a diverging argument without an expected result type"
                } else {
                    "cannot infer a consistent type for the generic function parameter"
                },
            );
            return Ty::Error;
        }
        let mut specialization_evidence = Vec::new();
        for (bound_index, bound) in template.bounds.iter().enumerate() {
            let interface = &template.bound_interfaces[bound_index];
            let target = substitution.get(&bound.parameter).unwrap_or(&actual);
            let forwarded = self
                .generic_evidence
                .iter()
                .find(|evidence| {
                    evidence.interface == *interface && evidence.candidate.target == *target
                })
                .cloned();
            let candidate = if let Some(evidence) = forwarded {
                evidence.candidate
            } else {
                let matching = self
                    .extension_candidates
                    .iter()
                    .filter(|candidate| {
                        candidate.visible
                            && candidate.target == *target
                            && candidate.interface.as_deref() == Some(interface.as_str())
                    })
                    .cloned()
                    .collect::<Vec<_>>();
                if matching.is_empty() {
                    self.error(7, expr.span, format!("no visible implementation of '{interface}' for {} satisfies generic bound", name(target)));
                    return Ty::Error;
                }
                if matching.len() > 1 {
                    let locations = matching
                        .iter()
                        .map(|candidate| {
                            format!(
                                "{}:{}..{}",
                                candidate.module, candidate.span.start, candidate.span.end
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    self.error(
                        7,
                        expr.span,
                        format!(
                            "ambiguous generic evidence for '{interface}'; candidates: {locations}"
                        ),
                    );
                    return Ty::Error;
                }
                matching[0].clone()
            };
            specialization_evidence.push(GenericEvidence {
                interface: interface.clone(),
                candidate,
            });
        }
        let previous_generic_evidence =
            std::mem::replace(&mut self.generic_evidence, specialization_evidence.clone());
        diverges |= actual == Ty::Never;
        let previous_generic_types =
            std::mem::replace(&mut self.generic_types, substitution.clone());
        let previous_generic_consts =
            std::mem::replace(&mut self.generic_consts, const_substitution.clone());
        let parameter_types = template
            .parameters
            .iter()
            .map(|parameter| FunctionParameter {
                access: ir_access(parameter.access),
                ty: self.type_path(&parameter.ty),
            })
            .collect::<Vec<_>>();
        let result = template
            .result
            .as_ref()
            .map(|result| self.type_path(result))
            .unwrap_or(UNIT);
        self.generic_types = previous_generic_types;
        self.generic_consts = previous_generic_consts;
        self.generic_evidence = previous_generic_evidence;
        if result == Ty::Error
            || parameter_types
                .iter()
                .any(|parameter| parameter.ty == Ty::Error)
        {
            return Ty::Error;
        }
        for (index, (argument, parameter)) in arguments.iter().zip(&parameter_types).enumerate() {
            if index < generic_index {
                if let Some(actual) = &checked_argument_types[index] {
                    self.ensure(actual, &parameter.ty, argument.span);
                }
                continue;
            }
            if index == generic_index {
                self.ensure(&actual, &parameter.ty, argument.span);
                continue;
            }
            if matches!(
                parameter.ty,
                Ty::String
                    | Ty::List(_)
                    | Ty::Array(..)
                    | Ty::Struct(..)
                    | Ty::Tuple(..)
                    | Ty::Enum(..)
            ) {
                self.allow_array_value(argument);
            }
            let argument_ty = self.expr(argument, Some(&parameter.ty));
            self.ensure(&argument_ty, &parameter.ty, argument.span);
            diverges |= argument_ty == Ty::Never;
        }
        let function_ty = Ty::Function(parameter_types, Box::new(result.clone()));
        let Some(IrType::Function(signature)) = ir_type(&function_ty) else {
            self.error(
                7,
                expr.span,
                "generic specialization has a type outside the executable function subset",
            );
            return Ty::Error;
        };
        if let Some(expected) = expected {
            self.ensure(&result, expected, expr.span);
        }
        let result = result;
        let evidence_key = specialization_evidence
            .iter()
            .map(|evidence| {
                format!(
                    "{}@{}..{}",
                    evidence.candidate.module,
                    evidence.candidate.span.start,
                    evidence.candidate.span.end
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        let key = format!(
            "{}::{}@{}..{}<{function_ty:?}>[{evidence_key}]",
            template.module, template.name, template.span.start, template.span.end
        );
        let registry = self
            .specialization_registry
            .as_ref()
            .expect("generic specialization registry is present")
            .clone();
        let specialization_id = {
            let mut registry = registry.borrow_mut();
            if let Some(id) = registry.by_key.get(&key).copied() {
                id
            } else {
                let id = FunctionId(registry.next_id);
                registry.next_id += 1;
                registry.by_key.insert(key.clone(), id);
                registry.requests.push(GenericSpecialization {
                    template: template.clone(),
                    substitution,
                    const_substitution,
                    evidence: specialization_evidence,
                    signature,
                    id,
                    key,
                });
                id
            }
        };
        self.generic_path_targets.insert(
            callee as *const Expr as usize,
            (specialization_id, function_ty),
        );
        self.expr(callee, None);
        if diverges {
            Ty::Never
        } else {
            result
        }
    }

    fn contains_reference(&self, ty: &Ty, visited: &mut HashSet<u32>) -> bool {
        match ty {
            Ty::Reference { .. } => true,
            Ty::Array(element, _) => self.contains_reference(element, visited),
            Ty::Struct(id, _) | Ty::Tuple(id, _, _) | Ty::Enum(id, _) => {
                if !visited.insert(*id) {
                    return false;
                }
                let info = self.table.info(*id);
                info.fields
                    .iter()
                    .any(|field| self.contains_reference(&field.ty, visited))
                    || info
                        .variants
                        .iter()
                        .flat_map(|variant| &variant.payload)
                        .any(|payload| self.contains_reference(payload, visited))
            }
            _ => false,
        }
    }

    fn contains_string_owner(&self, ty: &Ty, visited: &mut HashSet<u32>) -> bool {
        match ty {
            Ty::String => true,
            Ty::Array(element, _) => self.contains_string_owner(element, visited),
            Ty::Struct(id, _) | Ty::Tuple(id, _, _) | Ty::Enum(id, _) => {
                if !visited.insert(*id) {
                    return false;
                }
                let info = self.table.info(*id);
                info.fields
                    .iter()
                    .any(|field| self.contains_string_owner(&field.ty, visited))
                    || info
                        .variants
                        .iter()
                        .flat_map(|variant| &variant.payload)
                        .any(|payload| self.contains_string_owner(payload, visited))
            }
            _ => false,
        }
    }

    fn contains_list(&self, ty: &Ty, visited: &mut HashSet<u32>) -> bool {
        match ty {
            Ty::List(_) => true,
            Ty::Array(element, _) => self.contains_list(element, visited),
            Ty::Struct(id, _) | Ty::Tuple(id, _, _) | Ty::Enum(id, _) => {
                if !visited.insert(*id) {
                    return false;
                }
                let info = self.table.info(*id);
                info.fields
                    .iter()
                    .any(|field| self.contains_list(&field.ty, visited))
                    || info
                        .variants
                        .iter()
                        .flat_map(|variant| &variant.payload)
                        .any(|payload| self.contains_list(payload, visited))
            }
            _ => false,
        }
    }

    fn tuple_has_unsupported_nested_string_owner(&self, ty: &Ty) -> bool {
        let Ty::Tuple(id, _, _) = ty else {
            return false;
        };
        self.table.info(*id).fields.iter().any(|field| {
            field.ty != Ty::String
                && self.contains_string_owner(&field.ty, &mut HashSet::new())
                && !self.supported_nested_string_tuple(&field.ty, &mut HashSet::new())
        })
    }

    /// A nominal struct that holds String storage directly or through a nested
    /// struct but is not admitted by the shared `memobits_ir` transport rule.
    fn struct_has_unsupported_nested_string_owner(&self, ty: &Ty) -> bool {
        let Ty::Struct(id, _) = ty else {
            return false;
        };
        let info = self.table.info(*id);
        info.module != "\0tuple"
            && info.fields.iter().any(|field| {
                field.ty == Ty::String
                    || (matches!(field.ty, Ty::Struct(..) | Ty::Array(..))
                        && self.contains_string_owner(&field.ty, &mut HashSet::new()))
            })
            && !self.admitted_string_owner_struct(*id)
    }

    /// Shared-rule classification of a nominal struct id (see
    /// `memobits_ir::is_nominal_string_owner`).
    fn admitted_string_owner_struct(&self, id: u32) -> bool {
        memobits_ir::is_nominal_string_owner(&TyOwnerModel(&self.table), id)
    }

    fn supported_nested_string_tuple(&self, ty: &Ty, visited: &mut HashSet<u32>) -> bool {
        let Ty::Tuple(id, _, _) = ty else {
            return false;
        };
        let info = self.table.info(*id);
        if info.module != "\0tuple" || !visited.insert(*id) {
            return false;
        }
        let supported = info.fields.iter().all(|field| {
            field.ty == Ty::String
                || !self.contains_string_owner(&field.ty, &mut HashSet::new())
                || self.supported_nested_string_tuple(&field.ty, visited)
        });
        visited.remove(id);
        supported
    }

    fn error(&mut self, n: u16, span: Span, message: impl Into<String>) {
        self.diagnostics.push(diagnostic(n, span, message));
    }
    /// TE004: a write through a projection chain (`a[i].x`, `l.pts[j]`) needs
    /// the root binding to be a `var` owner or a share reference.
    fn check_place_writable(&mut self, target: &Expr, root: &str, binding: &Binding) {
        let writable = binding.mutable || binding.access == IrAccess::Share;
        let aggregate = |ty: &Ty| match ty {
            Ty::Array(..) => Some("an element of immutable array"),
            Ty::List(_) => Some("an element of immutable List"),
            Ty::Struct(..) | Ty::Tuple(..) => Some("a field of immutable struct"),
            _ => None,
        };
        match &binding.ty {
            ty @ (Ty::Array(..) | Ty::List(_) | Ty::Struct(..) | Ty::Tuple(..) | Ty::Enum(..))
                if !writable =>
            {
                let what = aggregate(ty).expect("aggregate root");
                self.error(
                    4,
                    target.span,
                    format!("cannot assign to {what} binding '{root}'; declare it with var"),
                );
            }
            Ty::Reference {
                access: IrAccess::Borrow,
                inner,
                ..
            } if matches!(
                inner.as_ref(),
                Ty::Array(..) | Ty::List(_) | Ty::Struct(..) | Ty::Tuple(..) | Ty::Enum(..)
            ) =>
            {
                self.error(
                    4,
                    target.span,
                    format!("cannot assign through borrow binding '{root}'"),
                )
            }
            Ty::Reference {
                access: IrAccess::Share,
                inner,
                ..
            } if matches!(
                inner.as_ref(),
                Ty::Array(..) | Ty::List(_) | Ty::Struct(..) | Ty::Tuple(..) | Ty::Enum(..)
            ) && !writable =>
            {
                self.error(
                    4,
                    target.span,
                    format!("cannot assign through immutable share binding '{root}'"),
                )
            }
            _ => {}
        }
    }
    fn type_path(&mut self, ty: &Type) -> Ty {
        if ty.path.first().is_some_and(|part| part == "\0enum") {
            return self.inline_enum_type(ty);
        }
        if ty.path.len() == 2 {
            if let Some(target) = self.generic_types.get(&ty.path[0]).cloned() {
                let matches = self
                    .generic_evidence
                    .iter()
                    .filter(|evidence| {
                        evidence.candidate.target == target
                            && evidence
                                .candidate
                                .associated_types
                                .contains_key(&ty.path[1])
                    })
                    .collect::<Vec<_>>();
                if matches.len() == 1 {
                    return matches[0].candidate.associated_types[&ty.path[1]].clone();
                }
                self.error(
                    8,
                    ty.span,
                    format!(
                        "associated type projection '{}' is unresolved in this generic context",
                        ty.path.join("::")
                    ),
                );
                return Ty::Error;
            }
        }
        if ty.path.len() == 1 && ty.arguments.is_empty() {
            if let Some(concrete) = self.generic_types.get(&ty.path[0]) {
                return concrete.clone();
            }
        }
        if ty.path.as_slice() == ["array"] {
            if let [memobits_syntax::TypeArgument::Type(element), memobits_syntax::TypeArgument::Const(length)] =
                ty.arguments.as_slice()
            {
                if let (Some(element), Some(length)) = (
                    self.generic_types.get(&element.path.join("::")),
                    self.generic_consts.get(length),
                ) {
                    return Ty::Array(Box::new(element.clone()), *length);
                }
                if let Some(length) = self.generic_consts.get(length).copied() {
                    let element = self.type_path(element);
                    return Ty::Array(Box::new(element), length);
                }
            }
        }
        let ty = &self.substitute_generic_arguments(ty);
        self.report_type_resolution(ty, self.table.resolve(&self.module, ty))
    }
    /// Splices the active generic substitution into the arguments of a written
    /// nominal type, so `Pair<Wrap<T>>` inside a specialized body names the
    /// concrete instance.
    fn substitute_generic_arguments(&self, ty: &Type) -> Type {
        if ty.arguments.is_empty()
            || (self.generic_types.is_empty() && self.generic_consts.is_empty())
        {
            return ty.clone();
        }
        self.table
            .substitute_generic_arguments(ty, &self.generic_types, &self.generic_consts)
    }
    fn inline_enum_type(&mut self, ty: &Type) -> Ty {
        if ty.path.len() < 2 {
            self.error(2, ty.span, "anonymous enum types need at least one variant");
            return Ty::Error;
        }
        let mut seen = HashSet::new();
        let mut payload_specs = HashMap::new();
        for argument in &ty.arguments {
            let memobits_syntax::TypeArgument::TupleField {
                label: Some(variant),
                ty: payload,
            } = argument
            else {
                self.error(
                    2,
                    ty.span,
                    "anonymous enum payloads must be associated with a variant name",
                );
                return Ty::Error;
            };
            if payload_specs
                .insert(variant.as_str(), payload.as_ref())
                .is_some()
            {
                self.error(
                    2,
                    ty.span,
                    format!("anonymous enum variant '{variant}' has duplicate payload metadata"),
                );
                return Ty::Error;
            }
        }

        let mut variants = Vec::with_capacity(ty.path.len() - 1);
        for variant in &ty.path[1..] {
            if !seen.insert(variant) {
                self.error(
                    2,
                    ty.span,
                    format!("anonymous enum variant '{variant}' is declared more than once"),
                );
                return Ty::Error;
            }
            let mut payload_types = Vec::new();
            if let Some(payload) = payload_specs.remove(variant.as_str()) {
                if payload.path.as_slice() != ["\0tuple"] || payload.arguments.is_empty() {
                    self.error(
                        2,
                        payload.span,
                        format!("invalid payload list for anonymous enum variant '{variant}'"),
                    );
                    return Ty::Error;
                }
                for argument in &payload.arguments {
                    let memobits_syntax::TypeArgument::Type(payload_ty) = argument else {
                        self.error(
                            17,
                            payload.span,
                            "anonymous enum payloads require owned value types",
                        );
                        return Ty::Error;
                    };
                    let resolved = self.type_path(payload_ty);
                    if resolved == Ty::Error {
                        return Ty::Error;
                    }
                    if self.contains_reference(&resolved, &mut HashSet::new()) {
                        self.error(
                            17,
                            payload_ty.span,
                            "anonymous enum payloads cannot contain references in this slice",
                        );
                        return Ty::Error;
                    }
                    payload_types.push(resolved);
                }
            }
            variants.push(VariantInfo {
                name: variant.clone(),
                payload: payload_types,
            });
        }
        if !payload_specs.is_empty() {
            self.error(
                2,
                ty.span,
                "anonymous enum payload metadata names an undeclared variant",
            );
            return Ty::Error;
        }
        self.table.instantiate_anonymous_enum(&variants, ty.span)
    }
    fn cast_u8_to_u32(&mut self, source: Ty, span: Span) -> Ty {
        if read_type(source) == U8 {
            U32
        } else {
            self.error(7, span, "this cast requires a u8 value and the target u32");
            Ty::Error
        }
    }
    fn report_type_resolution(
        &mut self,
        ty: &Type,
        resolved: Result<Ty, typetable::TypeFailure>,
    ) -> Ty {
        match resolved {
            Ok(resolved) => resolved,
            Err(failure) => {
                // A failure inside an alias target is reported at the alias.
                if failure.span.source == ty.span.source
                    && failure.span.start >= ty.span.start
                    && failure.span.end <= ty.span.end
                {
                    self.error(failure.code, failure.span, failure.message);
                }
                Ty::Error
            }
        }
    }
    fn ensure(&mut self, actual: &Ty, expected: &Ty, span: Span) {
        // A primitive read through a reference is copied implicitly.
        if let (Ty::Reference { inner, .. }, Ty::Primitive(_)) = (actual, expected) {
            if matches!(inner.as_ref(), Ty::Primitive(_)) {
                return self.ensure(inner, expected, span);
            }
        }
        if matches!(actual, Ty::Reference { .. })
            && !matches!(expected, Ty::Reference { .. } | Ty::Error)
        {
            self.error(
                17,
                span,
                "reference values cannot escape into an owned value or return",
            );
        }
        if !compatible(actual, expected) {
            self.error(
                2,
                span,
                format!("expected {}, found {}", name(expected), name(actual)),
            );
        }
    }
    fn register_local(
        &mut self,
        name: &str,
        ty: &Ty,
        mutable: bool,
        access: IrAccess,
        span: Span,
        node_addr: usize,
    ) -> Option<LocalId> {
        let ty = ir_type(ty)?;
        let facts = self.facts.as_mut()?;
        let id = LocalId(facts.locals.len() as u32);
        facts.locals.push(LocalFact {
            id,
            name: name.to_string(),
            ty,
            access,
            mutable,
            span,
            node_addr,
        });
        Some(id)
    }
    fn lookup(&self, key: &str) -> Option<&Binding> {
        self.scopes.iter().rev().find_map(|scope| scope.get(key))
    }
    /// `let P { x, y: alias } := value;`. The whole value is consumed; each
    /// field binds a new owned local of the field's type.
    fn destructure(
        &mut self,
        statement: &Statement,
        mutable: bool,
        path: &[String],
        fields: &[FieldPattern],
        value: &Expr,
    ) {
        let pattern_type = Type {
            span: statement.span,
            path: path.to_vec(),
            arguments: Vec::new(),
        };
        let target = self.type_path(&pattern_type);
        let table = Rc::clone(&self.table);
        let info_storage = match &target {
            Ty::Struct(id, _) | Ty::Tuple(id, _, _) => Some(table.info(*id)),
            Ty::Error => None,
            other => {
                self.error(
                    23,
                    statement.span,
                    format!("'{}' is not a struct type", name(other)),
                );
                None
            }
        };
        let info = info_storage.as_ref();
        self.allow_array_value(value);
        let inferred = self.expr(value, Some(&target));
        self.reject_extraction(value, &inferred);
        if matches!(inferred, Ty::Reference { .. }) {
            self.error(
                2,
                value.span,
                "cannot destructure a reference; destructuring consumes an owned struct value",
            );
        } else {
            self.ensure(&inferred, &target, value.span);
        }
        let mut seen: Vec<&str> = Vec::new();
        let mut bound: Vec<&str> = Vec::new();
        let mut bindings = Vec::new();
        for pattern in fields {
            let declared =
                info.and_then(|info| info.fields.iter().find(|field| field.name == pattern.field));
            if let Some(info) = info {
                if declared.is_none() {
                    self.error(
                        23,
                        pattern.span,
                        format!("struct '{}' has no field '{}'", info.name, pattern.field),
                    );
                }
            }
            if seen.contains(&pattern.field.as_str()) {
                self.error(
                    23,
                    pattern.span,
                    format!(
                        "field '{}' is named more than once in the pattern",
                        pattern.field
                    ),
                );
            }
            if bound.contains(&pattern.binding.as_str()) {
                self.error(
                    23,
                    pattern.span,
                    format!(
                        "binding '{}' is introduced more than once in the pattern",
                        pattern.binding
                    ),
                );
            }
            seen.push(&pattern.field);
            bound.push(&pattern.binding);
            let ty = declared.map_or(Ty::Error, |field| field.ty.clone());
            bindings.push((pattern, ty));
        }
        if let Some(info) = info {
            let missing: Vec<&str> = info
                .fields
                .iter()
                .filter(|field| !seen.contains(&field.name.as_str()))
                .map(|field| field.name.as_str())
                .collect();
            if !missing.is_empty() {
                self.error(
                    23,
                    statement.span,
                    format!(
                        "destructuring of '{}' must name every field; missing: {}",
                        info.name,
                        missing.join(", ")
                    ),
                );
            }
            self.check_field_visibility(info, "destructure", statement.span);
        }
        // The bindings start after the initialiser, like `let`.
        for (pattern, ty) in bindings {
            let addr = pattern as *const FieldPattern as usize;
            let id = self.register_local(
                &pattern.binding,
                &ty,
                mutable,
                IrAccess::Owned,
                pattern.span,
                addr,
            );
            self.scopes.last_mut().unwrap().insert(
                pattern.binding.clone(),
                Binding {
                    ty,
                    mutable,
                    access: IrAccess::Owned,
                    id,
                    origin: addr,
                },
            );
        }
    }
    fn destructure_tuple(
        &mut self,
        statement: &Statement,
        mutable: bool,
        elements: &[TupleBinding],
        value: &Expr,
    ) {
        self.allow_array_value(value);
        let inferred = self.expr(value, None);
        self.reject_extraction(value, &inferred);
        let table = Rc::clone(&self.table);
        let fields = match &inferred {
            Ty::Tuple(id, _, _) => Some(table.info(*id).fields),
            Ty::Error => None,
            Ty::Reference { .. } => {
                self.error(
                    2,
                    value.span,
                    "cannot destructure a reference; destructuring consumes an owned tuple value",
                );
                None
            }
            other => {
                self.error(
                    23,
                    statement.span,
                    format!("'{}' is not a tuple type", name(other)),
                );
                None
            }
        };
        if fields.is_some() {
            if self.contains_string_owner(&inferred, &mut HashSet::new())
                && !matches!(&value.kind, ExprKind::Path(path)
                    if path.len() == 1
                        && self.lookup(&path[0]).is_some_and(|binding|
                            binding.access == IrAccess::Owned
                                && matches!(&binding.ty, Ty::Tuple(..))))
            {
                self.error(
                    17,
                    value.span,
                    "String-owning tuple destructuring requires a named owned tuple local",
                );
            }
            if self.tuple_has_unsupported_nested_string_owner(&inferred) {
                self.error(
                    17,
                    statement.span,
                    "tuple destructuring cannot move nested String-owning aggregates other than tuples in this slice",
                );
            }
            self.bind_tuple_patterns(
                elements,
                &inferred,
                mutable,
                statement.span,
                &mut HashSet::new(),
            );
        }
    }
    fn bind_tuple_patterns(
        &mut self,
        elements: &[TupleBinding],
        tuple_ty: &Ty,
        mutable: bool,
        span: Span,
        seen: &mut HashSet<String>,
    ) {
        let Ty::Tuple(id, _, _) = tuple_ty else {
            self.error(
                23,
                span,
                format!("nested tuple pattern cannot match '{}'", name(tuple_ty)),
            );
            return;
        };
        let table = Rc::clone(&self.table);
        let fields = table.info(*id).fields;
        if elements.len() != fields.len() {
            self.error(
                23,
                span,
                format!(
                    "tuple destructuring expects {} bindings, found {}",
                    fields.len(),
                    elements.len()
                ),
            );
        }
        for (index, element) in elements.iter().enumerate() {
            let ty = fields
                .get(index)
                .map_or(Ty::Error, |field| field.ty.clone());
            let addr = element as *const TupleBinding as usize;
            if let Some(nested) = &element.nested {
                let local_name = format!("__tuple_pattern_{addr}");
                self.register_local(
                    &local_name,
                    &ty,
                    mutable,
                    IrAccess::Owned,
                    element.span,
                    addr,
                );
                self.bind_tuple_patterns(nested, &ty, mutable, element.span, seen);
                continue;
            }
            if element.binding == "_" {
                let local_name = format!("__tuple_discard_{addr}");
                self.register_local(
                    &local_name,
                    &ty,
                    mutable,
                    IrAccess::Owned,
                    element.span,
                    addr,
                );
                continue;
            }
            if !seen.insert(element.binding.clone()) {
                self.error(
                    23,
                    element.span,
                    format!(
                        "binding '{}' is introduced more than once in the tuple pattern",
                        element.binding
                    ),
                );
            }
            let id = self.register_local(
                &element.binding,
                &ty,
                mutable,
                IrAccess::Owned,
                element.span,
                addr,
            );
            self.scopes.last_mut().unwrap().insert(
                element.binding.clone(),
                Binding {
                    ty,
                    mutable,
                    access: IrAccess::Owned,
                    id,
                    origin: addr,
                },
            );
        }
    }
    fn block(&mut self, block: &Block, expected: Option<&Ty>) -> (Ty, bool) {
        self.scopes.push(HashMap::new());
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Binding {
                    mutable,
                    name,
                    annotation,
                    value,
                } => {
                    let annotation = annotation.as_ref().map(|ty| {
                        if ty.path.first().is_some_and(|part| part == "\0enum") {
                            self.type_path(ty)
                        } else {
                            let ty = &self.substitute_generic_arguments(ty);
                            self.report_type_resolution(
                                ty,
                                self.table.resolve_local(&self.module, ty),
                            )
                        }
                    });
                    self.allow_array_value(value);
                    let previous = self.concat_destination;
                    self.concat_destination = Some(value as *const Expr as usize);
                    let inferred = self.expr(value, annotation.as_ref());
                    self.concat_destination = previous;
                    self.reject_extraction(value, &inferred);
                    if let Some(ann) = &annotation {
                        self.ensure(&inferred, ann, value.span);
                    }
                    let ty = annotation.unwrap_or(inferred);
                    if *mutable && self.table.is_borrow_option(&ty) {
                        self.error(
                            17,
                            statement.span,
                            "(borrow T)? requires an immutable local binding",
                        );
                    }
                    let id = self.register_local(
                        name,
                        &ty,
                        *mutable,
                        IrAccess::Owned,
                        statement.span,
                        statement as *const _ as usize,
                    );
                    self.scopes.last_mut().unwrap().insert(
                        name.clone(),
                        Binding {
                            ty,
                            mutable: *mutable,
                            access: IrAccess::Owned,
                            id,
                            origin: statement as *const _ as usize,
                        },
                    );
                }
                StatementKind::Destructure {
                    mutable,
                    path,
                    fields,
                    value,
                } => self.destructure(statement, *mutable, path, fields, value),
                StatementKind::TupleDestructure {
                    mutable,
                    elements,
                    value,
                } => self.destructure_tuple(statement, *mutable, elements, value),
                StatementKind::Assign {
                    target,
                    operator,
                    value,
                } => {
                    let target_ty = match &target.kind {
                        ExprKind::Path(path) if path.len() == 1 => {
                            match self.lookup(&path[0]).cloned() {
                                Some(binding) => {
                                    self.allow_array_value(target);
                                    self.expr(target, None);
                                    match &binding.ty {
                                        Ty::Reference {
                                            access: IrAccess::Share,
                                            inner,
                                            ..
                                        } if binding.mutable
                                            || binding.access == IrAccess::Share =>
                                        {
                                            inner.as_ref().clone()
                                        }
                                        Ty::Reference {
                                            access: IrAccess::Share,
                                            inner,
                                            ..
                                        } => {
                                            self.error(
                                                4,
                                                target.span,
                                                format!(
                                                    "cannot mutate through immutable share binding '{}'",
                                                    path[0]
                                                ),
                                            );
                                            inner.as_ref().clone()
                                        }
                                        Ty::Reference {
                                            access: IrAccess::Borrow,
                                            inner,
                                            ..
                                        } => {
                                            self.error(
                                                4,
                                                target.span,
                                                format!(
                                                    "cannot mutate through borrow binding '{}'",
                                                    path[0]
                                                ),
                                            );
                                            inner.as_ref().clone()
                                        }
                                        _ if binding.access == IrAccess::Share => binding.ty,
                                        _ if !binding.mutable => {
                                            self.error(
                                                4,
                                                target.span,
                                                format!(
                                                    "cannot assign to immutable binding '{}'",
                                                    path[0]
                                                ),
                                            );
                                            binding.ty
                                        }
                                        _ => binding.ty,
                                    }
                                }
                                None => {
                                    self.error(
                                        5,
                                        target.span,
                                        format!("unknown local binding '{}'", path[0]),
                                    );
                                    Ty::Error
                                }
                            }
                        }
                        ExprKind::Index { .. } | ExprKind::Field { .. } => {
                            // Reads the place (privacy, existence, bounds of constant
                            // indices) and yields its type.
                            let place = self.expr(target, None);
                            match place_root(target) {
                                Some(path) if path.len() == 1 => {
                                    if let Some(binding) = self.lookup(&path[0]).cloned() {
                                        self.check_place_writable(target, &path[0], &binding);
                                    }
                                }
                                _ => self.error(
                                    6,
                                    target.span,
                                    "assignment through an element or field requires a place rooted at a named local array or struct",
                                ),
                            }
                            place
                        }
                        _ => {
                            self.expr(target, None);
                            self.error(6, target.span, "assignment target must be a local binding");
                            Ty::Error
                        }
                    };
                    if operator == "=" {
                        self.allow_array_value(value);
                    }
                    let previous = self.concat_destination;
                    let previous_share_field = self.share_field_assignment;
                    let share_field_target = match &target.kind {
                        ExprKind::Field { base, .. } if target_ty == Ty::String => {
                            matches!(&base.kind, ExprKind::Path(path) if path.len() == 1
                            && self.scopes.iter().rev()
                                .find_map(|scope| scope.get(&path[0]))
                                .is_some_and(|binding| {
                                    self.parameter_origins.contains(&binding.origin)
                                        && binding.access == IrAccess::Share
                                        && matches!(read_type(binding.ty.clone()), Ty::Struct(..) | Ty::Tuple(..))
                                }))
                        }
                        _ => false,
                    };
                    let concat_target = match &target.kind {
                        ExprKind::Path(path) if path.len() == 1 => {
                            self.lookup(&path[0]).is_some_and(|binding| {
                                (binding.mutable && binding.ty == Ty::String)
                                    || (binding.access == IrAccess::Share
                                        && target_ty == Ty::String)
                            })
                        }
                        ExprKind::Field { base, .. } if target_ty == Ty::String => {
                            // The outermost scope contains function parameters.
                            matches!(&base.kind, ExprKind::Path(path) if path.len() == 1
                            && self.scopes.iter().rev()
                                .find_map(|scope| scope.get(&path[0]))
                                .is_some_and(|binding| {
                                    matches!(read_type(binding.ty.clone()), Ty::Struct(..) | Ty::Tuple(..))
                                        && ((binding.mutable
                                            && binding.access == IrAccess::Owned
                                            && !self.parameter_origins.contains(&binding.origin))
                                            || (binding.access == IrAccess::Share
                                                && self.parameter_origins.contains(&binding.origin)))
                                }))
                        }
                        ExprKind::Index { .. } => target_ty == Ty::String,
                        _ => false,
                    };
                    if operator == "=" && concat_target {
                        self.concat_destination = Some(value as *const Expr as usize);
                        self.share_field_assignment = share_field_target;
                    }
                    if matches!(
                        operator.as_str(),
                        "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>="
                    ) && matches!(target_ty, Ty::Struct(..) | Ty::Enum(..))
                    {
                        self.allow_array_value(value);
                    }
                    let rhs_expected = if matches!(
                        operator.as_str(),
                        "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>="
                    ) && matches!(target_ty, Ty::Struct(..) | Ty::Enum(..))
                    {
                        let (interface_name, method_name) = match operator.as_str() {
                            "+=" => ("AddAssign", "add_assign"),
                            "-=" => ("SubAssign", "sub_assign"),
                            "*=" => ("MulAssign", "mul_assign"),
                            "/=" => ("DivAssign", "div_assign"),
                            "%=" => ("RemAssign", "rem_assign"),
                            "&=" => ("BitAndAssign", "bitand_assign"),
                            "|=" => ("BitOrAssign", "bitor_assign"),
                            ">>=" => ("ShrAssign", "shr_assign"),
                            "<<=" => ("ShlAssign", "shl_assign"),
                            _ => ("BitXorAssign", "bitxor_assign"),
                        };
                        let interface = qualified_interface(
                            &self.module,
                            &self.imports,
                            &Type {
                                span: statement.span,
                                path: vec!["core".into(), "ops".into(), interface_name.into()],
                                arguments: Vec::new(),
                            },
                        );
                        self.generic_evidence
                            .iter()
                            .find(|evidence| {
                                evidence.interface == interface
                                    && evidence.candidate.target == target_ty
                                    && evidence.candidate.methods.contains_key(method_name)
                            })
                            .map(|evidence| &evidence.candidate)
                            .or_else(|| {
                                self.extension_candidates.iter().find(|c| {
                                    c.interface.as_deref() == Some(interface.as_str())
                                        && c.target == target_ty
                                        && c.methods.contains_key(method_name)
                                        && c.visible
                                        && (c.local || c.public_methods.contains(method_name))
                                })
                            })
                            .and_then(|candidate| candidate.associated_types.get("Rhs"))
                            .cloned()
                            .unwrap_or_else(|| target_ty.clone())
                    } else {
                        target_ty.clone()
                    };
                    let value_ty = self.expr(value, Some(&rhs_expected));
                    self.concat_destination = previous;
                    self.share_field_assignment = previous_share_field;
                    if operator == "=" {
                        self.reject_extraction(value, &value_ty);
                    }
                    if matches!(value_ty, Ty::Reference { .. }) {
                        self.error(
                            17,
                            value.span,
                            "reference handle rebinding is not supported",
                        );
                    }
                    if operator == "=" {
                        self.ensure(&value_ty, &target_ty, value.span);
                    } else {
                        if matches!(
                            operator.as_str(),
                            "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>="
                        ) && matches!(target_ty, Ty::Struct(..) | Ty::Enum(..))
                        {
                            let (interface_name, method_name) = match operator.as_str() {
                                "+=" => ("AddAssign", "add_assign"),
                                "-=" => ("SubAssign", "sub_assign"),
                                "*=" => ("MulAssign", "mul_assign"),
                                "/=" => ("DivAssign", "div_assign"),
                                "%=" => ("RemAssign", "rem_assign"),
                                "&=" => ("BitAndAssign", "bitand_assign"),
                                "|=" => ("BitOrAssign", "bitor_assign"),
                                ">>=" => ("ShrAssign", "shr_assign"),
                                "<<=" => ("ShlAssign", "shl_assign"),
                                _ => ("BitXorAssign", "bitxor_assign"),
                            };
                            let interface = qualified_interface(
                                &self.module,
                                &self.imports,
                                &Type {
                                    span: statement.span,
                                    path: vec!["core".into(), "ops".into(), interface_name.into()],
                                    arguments: Vec::new(),
                                },
                            );
                            let matching = self
                                .generic_evidence
                                .iter()
                                .find(|evidence| {
                                    evidence.interface == interface
                                        && evidence.candidate.target == target_ty
                                        && evidence.candidate.methods.contains_key(method_name)
                                })
                                .map(|evidence| vec![evidence.candidate.clone()])
                                .unwrap_or_else(|| {
                                    self.extension_candidates
                                        .iter()
                                        .filter(|c| {
                                            c.interface.as_deref() == Some(interface.as_str())
                                                && c.target == target_ty
                                                && c.methods.contains_key(method_name)
                                        })
                                        .cloned()
                                        .collect::<Vec<_>>()
                                });
                            let applicable = matching
                                .iter()
                                .filter(|c| {
                                    c.visible && (c.local || c.public_methods.contains(method_name))
                                })
                                .cloned()
                                .collect::<Vec<_>>();
                            if applicable.len() > 1 {
                                self.error(
                                    7,
                                    statement.span,
                                    format!(
                                        "ambiguous {interface_name} implementation for `{operator}`"
                                    ),
                                );
                            } else if let Some(candidate) = applicable.first() {
                                let (receiver_access, parameters, result, _, function) =
                                    candidate.methods[method_name].clone();
                                if receiver_access != Access::Share
                                    || parameters.len() != 1
                                    || parameters[0].access != IrAccess::Owned
                                    || (parameters[0].ty != value_ty && value_ty != Ty::Never)
                                    || result != UNIT
                                {
                                    self.error(7, statement.span, format!("{interface_name} requires a share receiver, an owned matching Rhs, and Unit result"));
                                } else if let Some(facts) = self.facts.as_mut() {
                                    let Some(expression) = facts
                                        .expressions
                                        .iter()
                                        .find(|fact| {
                                            fact.node_addr == target as *const Expr as usize
                                        })
                                        .map(|fact| fact.id)
                                    else {
                                        continue;
                                    };
                                    if let Some(IrType::Function(signature)) =
                                        ir_type(&Ty::Function(
                                            vec![
                                                FunctionParameter {
                                                    access: IrAccess::Share,
                                                    ty: target_ty.clone(),
                                                },
                                                parameters[0].clone(),
                                            ],
                                            Box::new(UNIT.clone()),
                                        ))
                                    {
                                        facts.selected_assignments.push(SelectedCall {
                                            expression,
                                            function,
                                            receiver_access,
                                            signature,
                                        });
                                    } else {
                                        self.error(7, statement.span, format!("{interface_name} signature cannot be represented by the current IR"));
                                    }
                                }
                            } else {
                                self.error(
                                    7,
                                    statement.span,
                                    if matching.is_empty() {
                                        format!("no visible {interface_name} implementation for this target type")
                                    } else {
                                        format!("matching {interface_name} implementation is private or inactive")
                                    },
                                );
                            }
                        } else {
                            if matches!(operator.as_str(), "<<=" | ">>=")
                                && target_ty == U32
                                && crate::constants::shift_assignment_count_out_of_range(value)
                            {
                                self.diagnostics.push(
                                    crate::constants::shift_assignment_count_error(value.span),
                                );
                            }
                            if matches!(operator.as_str(), "&=" | "|=" | "^=" | "<<=" | ">>=")
                                && target_ty != U32
                            {
                                self.error(
                                    7,
                                    target.span,
                                    "primitive bitwise compound assignment currently requires u32",
                                );
                            } else if !matches!(operator.as_str(), "&=" | "|=" | "^=")
                                && !numeric(&target_ty)
                            {
                                self.error(
                                    7,
                                    target.span,
                                    "compound assignment requires a numeric binding",
                                );
                            }
                            self.ensure(&value_ty, &target_ty, value.span);
                            if operator == "%=" && !integer(&target_ty) {
                                self.error(7, statement.span, "remainder requires integers");
                            }
                            if matches!(operator.as_str(), "<<=" | ">>=") && !integer(&target_ty) {
                                self.error(7, statement.span, "shift requires integers");
                            }
                        }
                    }
                }
                StatementKind::Expression(expr) => {
                    let previous = self.concat_destination;
                    self.concat_destination = Some(expr as *const Expr as usize);
                    let ty = self.expr(expr, None);
                    self.concat_destination = previous;
                    if matches!(
                        ty,
                        Ty::String | Ty::Array(..) | Ty::Struct(..) | Ty::Tuple(..) | Ty::Enum(..)
                    ) {
                        self.reject_extraction(expr, &ty);
                    }
                }
                StatementKind::Return(value) => {
                    if let Some(value) = value {
                        self.allow_array_value(value);
                    }
                    let actual = value
                        .as_ref()
                        .map(|e| self.expr(e, Some(&self.result.clone())))
                        .unwrap_or(UNIT.clone());
                    if let Some(value) = value {
                        self.reject_extraction(value, &actual);
                    }
                    self.ensure(
                        &actual,
                        &self.result.clone(),
                        value.as_ref().map_or(statement.span, |e| e.span),
                    );
                }
                StatementKind::Loop(body) => {
                    self.block(body, None);
                }
                StatementKind::ForEach {
                    binding,
                    items,
                    body,
                } => {
                    self.allow_array_value(items);
                    let ty = match read_type(self.expr(items, None)) {
                        Ty::Array(element, _) if numeric(&element) || *element == BOOL => *element,
                        Ty::Array(element, _)
                            if place_root(items).is_some()
                                && !matches!(*element, Ty::Primitive(_) | Ty::Reference { .. }) =>
                        {
                            // Non-copyable elements are lent read-only for each
                            // iteration, like List elements.
                            let origin = match place_root(items) {
                                Some(path) if path.len() == 1 => self
                                    .lookup(&path[0])
                                    .map_or(ReferenceOrigin::Temporary, |binding| {
                                        ReferenceOrigin::Binding(binding.origin)
                                    }),
                                _ => ReferenceOrigin::Temporary,
                            };
                            Ty::Reference {
                                access: IrAccess::Borrow,
                                inner: element,
                                origin,
                            }
                        }
                        Ty::List(element) if self.list_read_receiver(items) => {
                            if matches!(*element, Ty::Primitive(_)) {
                                *element
                            } else {
                                // Non-copyable elements are lent read-only for the
                                // iteration; the list is loaned for the whole loop.
                                let origin = match place_root(items) {
                                    Some(path) if path.len() == 1 => self
                                        .lookup(&path[0])
                                        .map_or(ReferenceOrigin::Temporary, |binding| {
                                            ReferenceOrigin::Binding(binding.origin)
                                        }),
                                    _ => ReferenceOrigin::Temporary,
                                };
                                Ty::Reference {
                                    access: IrAccess::Borrow,
                                    inner: element,
                                    origin,
                                }
                            }
                        }
                        Ty::String if matches!(&items.kind, ExprKind::Path(path) if path.len() == 1) => {
                            Ty::Primitive("char")
                        }
                        Ty::String => {
                            self.error(
                                17,
                                items.span,
                                "string iteration requires a named string local or parameter",
                            );
                            Ty::Error
                        }
                        Ty::List(_) => {
                            self.error(17, items.span, "List iteration requires a local binding or a direct internal List call");
                            Ty::Error
                        }
                        Ty::Never | Ty::Error => Ty::Error,
                        _ => {
                            self.error(17, items.span, "loop iteration requires a fixed array with numeric or bool elements, or a List<u8> or List<u32>, or a named string");
                            Ty::Error
                        }
                    };
                    let origin = statement as *const Statement as usize;
                    let id = self.register_local(
                        binding,
                        &ty,
                        false,
                        IrAccess::Owned,
                        statement.span,
                        origin,
                    );
                    self.scopes.push(HashMap::from([(
                        binding.clone(),
                        Binding {
                            ty,
                            mutable: false,
                            access: IrAccess::Owned,
                            id,
                            origin,
                        },
                    )]));
                    self.block(body, None);
                    self.scopes.pop();
                }
                StatementKind::Break | StatementKind::Continue => {}
            }
        }
        let tail_ty = if let Some(tail) = &block.tail {
            let ty = self.expr(tail, expected);
            self.reject_extraction(tail, &ty);
            ty
        } else {
            UNIT.clone()
        };
        self.scopes.pop();
        let flow = flow_block(block);
        (if flow.falls { tail_ty } else { Ty::Never }, !flow.falls)
    }
    fn expr(&mut self, expr: &Expr, expected: Option<&Ty>) -> Ty {
        let id = self.facts.as_mut().map(|facts| {
            let id = ExprId(facts.next_expr);
            facts.next_expr += 1;
            id
        });
        let ty = self.expr_impl(expr, expected, id);
        if let Some((facts, id)) = self.facts.as_mut().zip(id) {
            facts.expressions.push(ExpressionFact {
                id,
                span: expr.span,
                ty: ir_type(&ty),
                node_addr: expr as *const Expr as usize,
            });
        }
        ty
    }
    /// `assert(condition)`: a `bool` check that traps when it is false.
    fn explicit_assert(&mut self, span: Span, arguments: &[Expr], id: Option<ExprId>) -> Ty {
        let [condition] = arguments else {
            self.error(
                10,
                span,
                format!("assert() expects one argument, found {}", arguments.len()),
            );
            for argument in arguments {
                self.expr(argument, None);
            }
            return Ty::Error;
        };
        let ty = self.expr(condition, Some(&BOOL));
        if ty == Ty::Error {
            return Ty::Error;
        }
        let before = self.diagnostics.len();
        self.ensure(&ty, &BOOL, condition.span);
        if self.diagnostics.len() != before {
            return Ty::Error;
        }
        if let Some((facts, id)) = self.facts.as_mut().zip(id) {
            facts.explicit_asserts.push(id);
        }
        UNIT
    }
    /// Type of one `replace`/`swap` place argument: a writable local, field or
    /// element at any projection depth. Reports why a place is rejected.
    fn replacement_place(&mut self, place: &Expr, builtin: &str) -> Ty {
        match &place.kind {
            ExprKind::Path(path) if path.len() == 1 => {
                let Some(binding) = self.lookup(&path[0]).cloned() else {
                    self.expr(place, None);
                    self.error(
                        5,
                        place.span,
                        format!("unknown local binding '{}'", path[0]),
                    );
                    return Ty::Error;
                };
                self.allow_array_value(place);
                self.expr(place, None);
                match &binding.ty {
                    Ty::Reference {
                        access: IrAccess::Share,
                        inner,
                        ..
                    } if binding.mutable || binding.access == IrAccess::Share => {
                        inner.as_ref().clone()
                    }
                    Ty::Reference { inner, .. } => {
                        self.error(
                            4,
                            place.span,
                            format!(
                                "{builtin}() cannot write through the immutable or borrowed binding '{}'; its owner must be a `var` or a `share` parameter",
                                path[0]
                            ),
                        );
                        inner.as_ref().clone()
                    }
                    ty if binding.access == IrAccess::Share || binding.mutable => ty.clone(),
                    ty => {
                        self.error(
                            4,
                            place.span,
                            format!(
                                "{builtin}() requires a mutable place; '{}' is immutable (declare it with var)",
                                path[0]
                            ),
                        );
                        ty.clone()
                    }
                }
            }
            ExprKind::Index { .. } | ExprKind::Field { .. } => {
                let ty = self.expr(place, None);
                match place_root(place) {
                    Some(path) if path.len() == 1 => {
                        if let Some(binding) = self.lookup(&path[0]).cloned() {
                            let before = self.diagnostics.len();
                            self.check_place_writable(place, &path[0], &binding);
                            if self.diagnostics.len() != before {
                                if let Some(last) = self.diagnostics.last_mut() {
                                    last.help = Some(format!(
                                        "{builtin}() writes the place, so its owner must be a `var` or a `share` parameter"
                                    ));
                                }
                            }
                        }
                    }
                    _ => self.error(
                        6,
                        place.span,
                        format!("{builtin}() requires a place rooted at a named local"),
                    ),
                }
                ty
            }
            _ => {
                self.expr(place, None);
                self.error(
                    6,
                    place.span,
                    format!(
                        "{builtin}() requires a place (a local, field or element) as its first argument, not a computed value"
                    ),
                );
                Ty::Error
            }
        }
    }
    fn place_type_supported(&mut self, ty: &Ty, span: Span, builtin: &str) -> bool {
        match ty {
            Ty::Error | Ty::Never => false,
            Ty::Reference { .. } => {
                self.error(
                    17,
                    span,
                    format!(
                        "{builtin}() cannot move a reference; references are not stored in places"
                    ),
                );
                false
            }
            Ty::Primitive(kind) if *kind == "Unit" => {
                self.error(
                    17,
                    span,
                    format!("{builtin}() requires a place with a value type"),
                );
                false
            }
            _ => true,
        }
    }
    /// `replace(place, value) -> T`.
    fn explicit_replace(&mut self, span: Span, arguments: &[Expr], id: Option<ExprId>) -> Ty {
        let [place, value] = arguments else {
            self.error(
                10,
                span,
                format!(
                    "replace() expects two arguments (place, value), found {}",
                    arguments.len()
                ),
            );
            for argument in arguments {
                self.expr(argument, None);
            }
            return Ty::Error;
        };
        let place_ty = self.replacement_place(place, "replace");
        self.allow_array_value(value);
        let previous_concat = self.concat_destination;
        if place_ty == Ty::String {
            self.concat_destination = Some(value as *const Expr as usize);
        }
        let value_ty = self.expr(value, Some(&place_ty));
        self.concat_destination = previous_concat;
        self.reject_extraction(value, &value_ty);
        if matches!(value_ty, Ty::Reference { .. }) {
            self.error(
                17,
                value.span,
                "reference handle rebinding is not supported",
            );
            return Ty::Error;
        }
        if place_ty == Ty::Error || value_ty == Ty::Error {
            return Ty::Error;
        }
        if !self.place_type_supported(&place_ty, place.span, "replace") {
            return Ty::Error;
        }
        let before = self.diagnostics.len();
        self.ensure(&value_ty, &place_ty, value.span);
        if self.diagnostics.len() != before {
            return Ty::Error;
        }
        if let Some((facts, id)) = self.facts.as_mut().zip(id) {
            facts.explicit_replaces.push(id);
        }
        place_ty
    }
    /// `swap(a, b)`: two places of the same type.
    fn explicit_swap(&mut self, span: Span, arguments: &[Expr], id: Option<ExprId>) -> Ty {
        let [left, right] = arguments else {
            self.error(
                10,
                span,
                format!(
                    "swap() expects two places, found {} arguments",
                    arguments.len()
                ),
            );
            for argument in arguments {
                self.expr(argument, None);
            }
            return Ty::Error;
        };
        let left_ty = self.replacement_place(left, "swap");
        let right_ty = self.replacement_place(right, "swap");
        if left_ty == Ty::Error || right_ty == Ty::Error {
            return Ty::Error;
        }
        if !self.place_type_supported(&left_ty, left.span, "swap") {
            return Ty::Error;
        }
        if left_ty != right_ty {
            self.error(
                7,
                right.span,
                format!(
                    "swap() requires two places of the same type, found {} and {}",
                    name(&left_ty),
                    name(&right_ty)
                ),
            );
            return Ty::Error;
        }
        if let Some((facts, id)) = self.facts.as_mut().zip(id) {
            facts.explicit_swaps.push(id);
        }
        UNIT
    }

    fn explicit_drop(&mut self, span: Span, arguments: &[Expr], id: Option<ExprId>) -> Ty {
        let [value] = arguments else {
            self.error(
                10,
                span,
                format!("drop() expects one argument, found {}", arguments.len()),
            );
            for argument in arguments {
                self.expr(argument, None);
            }
            return Ty::Error;
        };
        self.allow_array_value(value);
        let ty = self.expr(value, None);
        if ty == Ty::Error {
            return Ty::Error;
        }
        if !matches!(ty, Ty::String | Ty::List(_))
            || !matches!(&value.kind, ExprKind::Path(path) if path.len() == 1
                && self.lookup(&path[0]).is_some_and(|binding| binding.access == IrAccess::Owned))
        {
            self.error(
                17,
                value.span,
                "drop() requires a whole named owned String, List<u8>, or List<u32> local",
            );
            return Ty::Error;
        }
        if let Some((facts, id)) = self.facts.as_mut().zip(id) {
            facts.explicit_drops.push(id);
        }
        UNIT
    }

    /// `expr.copy()`: a fresh owned value of a primitive type. The receiver is
    /// only read; a primitive behind a reference is copied out of it.
    fn copy_conversion(&mut self, expression: &Expr, base: &Expr, arguments: &[Expr]) -> Ty {
        if !arguments.is_empty() {
            self.error(
                10,
                expression.span,
                format!("copy() takes no arguments, found {}", arguments.len()),
            );
            for argument in arguments {
                self.expr(argument, None);
            }
            self.expr(base, None);
            return Ty::Error;
        }
        let receiver = self.expr(base, None);
        match read_type(receiver) {
            ty @ Ty::Primitive(kind) if kind != "Unit" => ty,
            ty @ (Ty::Never | Ty::Error) => ty,
            _ => {
                self.error(
                    17,
                    expression.span,
                    "copy is currently available only for primitive values (integers, floats and Bool); copying arrays, rows and structs is not supported yet",
                );
                Ty::Error
            }
        }
    }
    fn direct_callee(&self, callee: &Expr) -> bool {
        matches!(&callee.kind, ExprKind::Path(path)
            if path.len() != 1 || self.lookup(&path[0]).is_none())
    }

    /// TE033: a heap-producing operation needs the alloc layer.
    fn require_alloc(&mut self, span: Span, operation: &str) {
        if !self.alloc {
            self.error(
                33,
                span,
                format!(
                    "{operation} allocates on the heap and is unavailable: the project sets `[build] alloc = false`"
                ),
            );
        }
    }

    fn string_read(
        &mut self,
        expression: &Expr,
        base: &Expr,
        method: &str,
        arguments: &[Expr],
    ) -> Ty {
        if method == "concat" {
            self.require_alloc(expression.span, "String concat()");
        }
        self.allow_array_value(base);
        let previous = self.concat_destination;
        if method != "concat" {
            self.concat_destination = Some(base as *const Expr as usize);
        }
        let receiver = read_type(self.expr(base, None));
        self.concat_destination = previous;
        if matches!(receiver, Ty::List(_)) && method == "len" {
            if !self.list_read_receiver(base) {
                self.error(
                    17,
                    base.span,
                    "List len() requires a local binding or a direct internal List call",
                );
            }
            if !arguments.is_empty() {
                self.error(10, expression.span, "len() expects 0 arguments");
                return Ty::Error;
            }
            return Ty::Primitive("u32");
        }
        let offset_type = Ty::Primitive("u32");
        if method == "concat"
            && self.concat_destination != Some(expression as *const Expr as usize)
            && !self.share_field_assignment
        {
            self.error(
                17,
                expression.span,
                "concat requires a whole String local, a direct String field initializer or assignment on a local struct, a standalone statement, an immediate read-only method, or an owned or explicit borrow String argument to a direct internal call",
            );
        }
        let expected = usize::from(method != "len");
        let mut diverges = receiver == Ty::Never;
        for (index, argument) in arguments.iter().enumerate() {
            let argument_type = if method == "concat" {
                self.allow_array_value(argument);
                &Ty::String
            } else {
                &offset_type
            };
            let want = (expected == 1 && index == 0).then_some(argument_type);
            let actual = read_type(self.expr(argument, want));
            diverges |= actual == Ty::Never;
            if let Some(want) = want {
                self.ensure(&actual, want, argument.span);
            }
        }
        if arguments.len() != expected {
            self.error(
                10,
                expression.span,
                format!("{method}() expects {expected} arguments"),
            );
            return Ty::Error;
        }
        match receiver {
            Ty::String if diverges => Ty::Never,
            Ty::String if method == "is_char_boundary" => BOOL,
            Ty::String if method == "concat" => Ty::String,
            Ty::String if matches!(method, "byte_at" | "scalar_at") => self.table.instantiate_enum(
                registry::by_id(registry::TemplateId::Option),
                vec![ResolvedArgument::Type(Ty::Primitive(
                    if method == "byte_at" { "u8" } else { "u32" },
                ))],
                expression.span,
            ),
            Ty::String => offset_type,
            ty @ (Ty::Error | Ty::Never) => ty,
            _ => {
                self.error(
                    17,
                    base.span,
                    format!("{method}() requires a String receiver"),
                );
                Ty::Error
            }
        }
    }

    fn byte_utf8(&mut self, expr: &Expr, base: &Expr, method: &str, arguments: &[Expr]) -> Ty {
        if method == "to_utf8_string" {
            self.require_alloc(expr.span, "to_utf8_string()");
        }
        self.allow_array_value(base);
        let input = read_type(self.expr(base, None));
        let mut diverges = input == Ty::Never;
        if !matches!(input, Ty::Array(element, _) if *element == Ty::Primitive("u8")) && !diverges {
            self.error(
                17,
                base.span,
                format!("{method}() requires a fixed byte array"),
            );
        }
        for argument in arguments {
            let length = read_type(self.expr(argument, Some(&I32)));
            self.ensure(&length, &I32, argument.span);
            diverges |= length == Ty::Never;
        }
        if arguments.len() != 1 {
            self.error(
                10,
                expr.span,
                format!("{method}() expects one logical length"),
            );
            return Ty::Error;
        }
        if diverges {
            return Ty::Never;
        }
        let error = self.table.utf8_error_type(expr.span);
        let success = if method == "to_utf8_string" {
            Ty::String
        } else {
            I32
        };
        self.table.instantiate_enum(
            registry::by_id(registry::TemplateId::Result),
            vec![
                ResolvedArgument::Type(success),
                ResolvedArgument::Type(error),
            ],
            expr.span,
        )
    }

    fn collection_search(
        &mut self,
        expr: &Expr,
        base: &Expr,
        method: &str,
        arguments: &[Expr],
    ) -> Ty {
        self.allow_array_value(base);
        let receiver = read_type(self.expr(base, None));
        let mut diverges = receiver == Ty::Never;
        let element = match receiver {
            Ty::Array(element, _) if numeric(&element) || *element == BOOL => Some(*element),
            Ty::List(element)
                if matches!(*element, Ty::Primitive(kind) if kind != "Unit")
                    && self.list_read_receiver(base) =>
            {
                Some(*element)
            }
            Ty::List(_) => {
                self.error(
                    17,
                    base.span,
                    format!("{method}() on a List needs primitive elements and a local binding or direct internal call result; compare other element types in a `loop`"),
                );
                None
            }
            Ty::Error | Ty::Never => None,
            _ => {
                self.error(
                    17,
                    base.span,
                    format!("{method}() requires an array with numeric or Bool elements, or a List of primitives (local, reference binding, or direct internal call result)"),
                );
                None
            }
        };
        for argument in arguments {
            let actual = read_type(self.expr(argument, element.as_ref()));
            if let Some(element) = &element {
                self.ensure(&actual, element, argument.span);
            }
            diverges |= actual == Ty::Never;
        }
        if arguments.len() != 1 {
            self.error(10, expr.span, format!("{method}() expects one value"));
            return Ty::Error;
        }
        if diverges {
            Ty::Never
        } else if element.is_none() {
            Ty::Error
        } else if method == "index_of" {
            self.table.instantiate_enum(
                registry::by_id(registry::TemplateId::Option),
                vec![ResolvedArgument::Type(Ty::Primitive("u32"))],
                expr.span,
            )
        } else {
            BOOL
        }
    }

    fn string_push_str(&mut self, expression: &Expr, base: &Expr, arguments: &[Expr]) -> Ty {
        self.require_alloc(expression.span, "String push_str()");
        let writable = matches!(&base.kind, ExprKind::Path(path) if path.len() == 1
        && self.lookup(&path[0]).is_some_and(|binding| {
            (binding.mutable && binding.ty == Ty::String)
                || (binding.access == IrAccess::Share
                    && matches!(&binding.ty, Ty::Reference { inner, .. } if **inner == Ty::String))
        }));
        self.allow_array_value(base);
        self.expr(base, None);
        if !writable {
            self.error(
                17,
                base.span,
                "push_str() requires a mutable whole String local or a direct share String parameter",
            );
        }
        if arguments.len() != 1 {
            self.error(10, expression.span, "push_str() expects 1 argument");
            for argument in arguments {
                self.expr(argument, None);
            }
            return Ty::Error;
        }
        self.allow_array_value(&arguments[0]);
        let suffix = read_type(self.expr(&arguments[0], Some(&Ty::String)));
        self.ensure(&suffix, &Ty::String, arguments[0].span);
        match suffix {
            Ty::Error | Ty::Never => suffix,
            _ => UNIT,
        }
    }

    fn reference_conversion(
        &mut self,
        expression: &Expr,
        base: &Expr,
        arguments: &[Expr],
        access: IrAccess,
        expected: Option<&Ty>,
    ) -> Ty {
        if !arguments.is_empty() {
            self.error(
                10,
                expression.span,
                format!(
                    "{}() conversion takes no arguments, found {}",
                    access_name(access),
                    arguments.len()
                ),
            );
            for argument in arguments {
                self.expr(argument, None);
            }
            return Ty::Error;
        }

        let temporary_inner = match (expected, &base.kind) {
            (Some(inner @ Ty::String), ExprKind::Call { .. }) => Some(inner),
            (Some(inner @ Ty::List(_)), ExprKind::Call { callee, .. })
                if self.direct_callee(callee) =>
            {
                Some(inner)
            }
            _ => None,
        };
        if let Some(inner) = temporary_inner.filter(|_| {
            access == IrAccess::Borrow
                && self.temporary_borrow_argument == Some(expression as *const Expr as usize)
        }) {
            let previous = self.concat_destination;
            if *inner == Ty::String {
                self.concat_destination = Some(base as *const Expr as usize);
            }
            let receiver = self.expr(base, Some(inner));
            self.concat_destination = previous;
            return match (receiver, inner) {
                (ty @ Ty::String, Ty::String) | (ty @ Ty::List(_), Ty::List(_)) => Ty::Reference {
                    access,
                    inner: Box::new(ty),
                    origin: ReferenceOrigin::Temporary,
                },
                (ty @ (Ty::Never | Ty::Error), _) => ty,
                _ => {
                    self.error(
                        17,
                        base.span,
                        format!(
                            "a temporary borrow argument requires an owned {} call result",
                            name(inner)
                        ),
                    );
                    Ty::Error
                }
            };
        }

        // `m[i].borrow()`, `l.a.share()`: a projection of a named local.
        let is_row = matches!(base.kind, ExprKind::Index { .. } | ExprKind::Field { .. });
        let owner_binding = match place_root(base) {
            Some(path) if path.len() == 1 => self.lookup(&path[0]).cloned(),
            _ => None,
        };
        if owner_binding.is_none() {
            self.error(
                17,
                base.span,
                "borrow/share conversion requires a named local owner or reference",
            );
            self.expr(base, None);
            return Ty::Error;
        }
        let expected_inner = match expected {
            Some(Ty::Reference { inner, .. }) => Some(inner.as_ref()),
            other => other,
        };
        // An array owner may be borrowed or shared as a whole.
        self.index_base = base as *const Expr as usize;
        let base_ty = self.expr(base, expected_inner);
        if self.table.is_borrow_option(&base_ty) {
            self.error(
                17,
                base.span,
                "cannot borrow or share the storage of (borrow T)?",
            );
            return Ty::Error;
        }
        if is_row
            && !matches!(
                base_ty,
                Ty::String
                    | Ty::Array(..)
                    | Ty::List(..)
                    | Ty::Struct(..)
                    | Ty::Tuple(..)
                    | Ty::Enum(..)
                    | Ty::Error
                    | Ty::Never
            )
        {
            self.error(
                17,
                base.span,
                "borrow/share conversion of an element or field supports sub-aggregates (arrays and structs) only; references to primitive elements and struct fields are not supported",
            );
            return Ty::Error;
        }
        let (inner, origin, current_access) = match base_ty {
            Ty::String | Ty::Array(..) | Ty::Struct(..) | Ty::Tuple(..) | Ty::Enum(..)
                if is_row =>
            {
                let binding = owner_binding.as_ref().expect("row root checked above");
                let access = match &binding.ty {
                    Ty::Reference { access, .. } => *access,
                    _ => binding.access,
                };
                (
                    Box::new(base_ty),
                    ReferenceOrigin::Binding(binding.origin),
                    Some(access),
                )
            }
            Ty::Reference {
                access,
                inner,
                origin,
            } => (inner, origin, Some(access)),
            owner @ (Ty::Primitive(_)
            | Ty::String
            | Ty::List(_)
            | Ty::Array(..)
            | Ty::Struct(..)
            | Ty::Tuple(..)
            | Ty::Enum(..)) => {
                let origin = owner_binding
                    .as_ref()
                    .map_or(ReferenceOrigin::Temporary, |binding| {
                        ReferenceOrigin::Binding(binding.origin)
                    });
                let current_access = owner_binding.as_ref().map(|binding| binding.access);
                (Box::new(owner), origin, current_access)
            }
            ty @ (Ty::Never | Ty::Error) => return ty,
            _ => {
                self.error(
                    17,
                    base.span,
                    "borrow/share conversion requires a primitive, array or struct owner or reference",
                );
                return Ty::Error;
            }
        };

        if !matches!(
            inner.as_ref(),
            Ty::Primitive(_)
                | Ty::String
                | Ty::List(_)
                | Ty::Array(..)
                | Ty::Struct(..)
                | Ty::Tuple(..)
                | Ty::Enum(..)
        ) {
            self.error(
                17,
                base.span,
                "borrow/share conversion currently supports primitive values, arrays and structs only",
            );
            return Ty::Error;
        }

        if access == IrAccess::Share {
            let already_shared = current_access == Some(IrAccess::Share);
            let incoming_share = owner_binding
                .as_ref()
                .is_some_and(|binding| binding.access == IrAccess::Share);
            let mutable_owner = owner_binding
                .as_ref()
                .is_some_and(|binding| binding.mutable);
            if current_access == Some(IrAccess::Borrow) {
                self.error(
                    17,
                    expression.span,
                    "cannot create a share conversion from a borrow reference",
                );
                return Ty::Error;
            }
            if !already_shared && !incoming_share && !mutable_owner {
                self.error(
                    17,
                    expression.span,
                    "share conversion requires a mutable local owner",
                );
                return Ty::Error;
            }
            if owner_binding.is_none() || matches!(&origin, ReferenceOrigin::Temporary) {
                self.error(
                    17,
                    expression.span,
                    "share conversion requires a named mutable owner",
                );
                return Ty::Error;
            }
        } else if owner_binding.is_none() && matches!(&origin, ReferenceOrigin::Temporary) {
            self.error(
                17,
                expression.span,
                "borrow conversion currently requires a named owner",
            );
            return Ty::Error;
        }

        Ty::Reference {
            access,
            inner,
            origin,
        }
    }
    fn check_field_visibility(&mut self, info: &StructInfo, operation: &str, span: Span) {
        let mut private: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for field in &info.fields {
            if !field.visible_in(&self.module) {
                private.entry(&field.module).or_default().push(&field.name);
            }
        }
        for (module, fields) in private {
            self.error(
                25,
                span,
                format!(
                    "cannot {operation} struct '{}' outside module '{module}': field(s) {} are private",
                    info.name,
                    fields.join(", ")
                ),
            );
        }
    }

    fn anonymous_record(&mut self, expr: &Expr, fields: &[FieldInit], expected: Option<&Ty>) -> Ty {
        if self.lowering && !self.array_allowed(expr) {
            self.error(
                17,
                expr.span,
                "anonymous record literals must be used as an owned value (binding initializer, assignment, argument, result or branch value); bind the record before projecting it",
            );
        }
        let table = Rc::clone(&self.table);
        let expected_record = match expected {
            Some(ty @ Ty::Struct(id, _)) if table.info(*id).module == "\0record" => {
                Some((ty.clone(), table.info(*id)))
            }
            Some(Ty::Error | Ty::Never) | None => None,
            Some(other) => {
                self.error(
                    2,
                    expr.span,
                    format!(
                        "anonymous record literal has no structural type matching expected {}",
                        name(other)
                    ),
                );
                return Ty::Error;
            }
        };

        let mut inferred = Vec::new();
        let mut seen = HashSet::new();
        for init in fields {
            if !seen.insert(init.name.as_str()) {
                self.error(
                    23,
                    init.span,
                    format!("field '{}' is initialised more than once", init.name),
                );
                self.expr(&init.value, None);
                continue;
            }
            let declared = expected_record
                .as_ref()
                .and_then(|(_, info)| info.fields.iter().find(|field| field.name == init.name));
            if expected_record.is_some() && declared.is_none() {
                self.error(
                    23,
                    init.span,
                    format!("anonymous record shape has no field '{}'", init.name),
                );
            }
            let expected_field = declared.map(|field| field.ty.clone());
            self.allow_array_value(&init.value);
            let previous_concat = self.concat_destination;
            if expected_field == Some(Ty::String) {
                self.concat_destination = Some(&init.value as *const Expr as usize);
            }
            let actual = self.expr(&init.value, expected_field.as_ref());
            self.concat_destination = previous_concat;
            self.reject_extraction(&init.value, &actual);
            if let Some(want) = &expected_field {
                self.ensure(&actual, want, init.value.span);
            } else if expected_record.is_none() && actual != Ty::Error && actual != Ty::Never {
                inferred.push((init.name.clone(), actual));
            }
        }
        if let Some((ty, info)) = expected_record {
            let missing: Vec<&str> = info
                .fields
                .iter()
                .filter(|field| !seen.contains(field.name.as_str()))
                .map(|field| field.name.as_str())
                .collect();
            if !missing.is_empty() {
                self.error(
                    23,
                    expr.span,
                    format!(
                        "missing field(s) in anonymous record: {}",
                        missing.join(", ")
                    ),
                );
            }
            ty
        } else if inferred.len() == seen.len() {
            table.instantiate_record(inferred, expr.span)
        } else {
            Ty::Error
        }
    }

    /// `base.field`: a read of one field of a named local struct.
    fn field_read(&mut self, base: &Expr, field_name: &str, expr: &Expr) -> Ty {
        if self.lowering {
            match &base.kind {
                        ExprKind::Path(path) if path.len() == 1 => {
                            self.index_base = base as *const Expr as usize;
                        }
                        // A sub-aggregate of a projection chain; its own arm
                        // marks the root.
                        ExprKind::Index { .. } | ExprKind::Field { .. } => {}
                        _ => self.error(
                            17,
                            base.span,
                            "field access is supported on named local structs and projections of them only; bind the struct to a local first",
                        ),
                    }
        }
        let base_ty = self.expr(base, None);
        // A struct reference (`borrow`/`share` parameter or binding) reads
        // its fields like its owner.
        let base_ty = match base_ty {
            Ty::Reference { inner, .. }
                if matches!(inner.as_ref(), Ty::Struct(..) | Ty::Tuple(..)) =>
            {
                *inner
            }
            other => other,
        };
        match base_ty {
            Ty::Tuple(id, tuple_name, aliases) => {
                let info = self.table.info(id);
                let index = field_name
                    .parse::<usize>()
                    .ok()
                    .filter(|i| *i < info.fields.len())
                    .or_else(|| {
                        aliases
                            .labels
                            .iter()
                            .position(|label| label.as_deref() == Some(field_name))
                    });
                let Some(index) = index else {
                    self.error(
                        24,
                        expr.span,
                        format!("tuple '{tuple_name}' has no field '{field_name}'"),
                    );
                    return Ty::Error;
                };
                if let Some(facts) = &mut self.facts {
                    facts.tuple_projections.push(TupleProjectionFact {
                        node_addr: expr as *const Expr as usize,
                        slot: index as u32,
                    });
                }
                with_tuple_aliases(
                    info.fields[index].ty.clone(),
                    aliases.nested[index].as_deref(),
                )
            }
            Ty::Struct(id, struct_name) => {
                let table = Rc::clone(&self.table);
                let info = &table.info(id);
                match info
                    .fields
                    .iter()
                    .enumerate()
                    .find(|(index, field)| {
                        field.name == field_name
                            || (info.module == "\0tuple" && index.to_string() == field_name)
                    })
                    .map(|(_, field)| field)
                {
                    None => {
                        self.error(
                            24,
                            expr.span,
                            format!("struct '{struct_name}' has no field '{field_name}'"),
                        );
                        Ty::Error
                    }
                    Some(field) => {
                        if !field.visible_in(&self.module) {
                            self.error(
                                25,
                                expr.span,
                                format!(
                                    "field '{field_name}' of struct '{struct_name}' is private to module '{}'",
                                    field.module
                                ),
                            );
                        }
                        field.ty.clone()
                    }
                }
            }
            Ty::Never | Ty::Error => Ty::Error,
            Ty::Reference { .. } => {
                self.error(
                    24,
                    expr.span,
                    "field access requires a struct value or a reference to one",
                );
                Ty::Error
            }
            other => {
                self.error(
                    24,
                    expr.span,
                    format!(
                        "field access requires a struct value, found {}",
                        name(&other)
                    ),
                );
                Ty::Error
            }
        }
    }
    /// A path `Enum::Variant` (the enum possibly qualified or imported): the
    /// enum's type and the variant's index, `None` inside when the enum has no
    /// such variant. `None` overall when the path does not name an enum.
    fn variant_path(&self, path: &[String], span: Span) -> Option<(Ty, Option<u32>)> {
        let (variant, type_path) = path.split_last()?;
        if type_path.is_empty() {
            return None;
        }
        let written = Type {
            span,
            path: type_path.to_vec(),
            arguments: Vec::new(),
        };
        let resolved = self.table.resolve(&self.module, &written).ok()?;
        let Ty::Enum(id, _) = &resolved else {
            return None;
        };
        let index = self
            .table
            .info(*id)
            .variants
            .iter()
            .position(|candidate| &candidate.name == variant)
            .map(|index| index as u32);
        Some((resolved, index))
    }
    fn contextual_variant(
        &self,
        path: &[String],
        span: Span,
        expected: Option<&Ty>,
    ) -> Option<(Ty, Option<u32>)> {
        if let Some((template, index)) = self.prelude_variant(path) {
            if let Some(as_ty @ Ty::Enum(id, _)) = expected {
                if self
                    .table
                    .enum_template(*id)
                    .is_some_and(|expected| expected.id == template.id)
                {
                    return Some((as_ty.clone(), Some(index as u32)));
                }
            }
        }
        if let (Some(as_ty @ Ty::Enum(id, _)), Some((variant, type_path))) =
            (expected, path.split_last())
        {
            if !type_path.is_empty() {
                let written = Type {
                    span,
                    path: type_path.to_vec(),
                    arguments: Vec::new(),
                };
                if self
                    .table
                    .generic_origin(*id)
                    .zip(self.table.generic_definition_key(&self.module, &written))
                    .is_some_and(|(expected, written)| expected == written)
                {
                    let info = self.table.info(*id);
                    let index = info
                        .variants
                        .iter()
                        .position(|candidate| &candidate.name == variant)
                        .map(|index| index as u32);
                    return Some((as_ty.clone(), index));
                }
            }
        }
        if let ([variant], Some(as_ty @ Ty::Enum(id, _))) = (path, expected) {
            // A bare variant is contextual only when an expected enum selects
            // it. Payload constructors are validated by their caller, and
            // ordinary names keep their lexical precedence.
            if self.lookup(variant).is_none()
                && !self.functions.contains_key(variant)
                && !self.imports.contains_key(variant)
            {
                let info = self.table.info(*id);
                if let Some(index) = info
                    .variants
                    .iter()
                    .position(|candidate| candidate.name == *variant)
                {
                    return Some((as_ty.clone(), Some(index as u32)));
                }
            }
        }
        self.variant_path(path, span)
    }

    fn prelude_variant(&self, path: &[String]) -> Option<(&'static Template, usize)> {
        let [name] = path else { return None };
        if self.lookup(name).is_some()
            || self.functions.contains_key(name)
            || self.imports.contains_key(name)
        {
            return None;
        }
        registry::variant(name)
    }

    /// An unqualified prelude constructor without a concrete instance in context.
    fn infer_variant(
        &mut self,
        expr: &Expr,
        id: Option<ExprId>,
        template: &Template,
        variant: usize,
        arguments: Option<&[Expr]>,
        expected: Option<&Ty>,
    ) -> Ty {
        let declared = &template.variants[variant];
        let payload = arguments.unwrap_or_default();
        if declared.payload.is_empty() && arguments.is_some() {
            self.error(
                28,
                expr.span,
                format!(
                    "variant '{}::{}' has no payload; write it without parentheses",
                    template.name, declared.name
                ),
            );
        } else if payload.len() != declared.payload.len() {
            self.error(
                if arguments.is_none() { 28 } else { 10 },
                expr.span,
                format!(
                    "variant '{}::{}' expects {} payload argument(s), found {}",
                    template.name,
                    declared.name,
                    declared.payload.len(),
                    payload.len()
                ),
            );
        } else if let Some(want) = expected.filter(|ty| !matches!(ty, Ty::Error | Ty::Never)) {
            self.error(
                2,
                expr.span,
                format!(
                    "variant '{}' belongs to {}, but expected {}",
                    declared.name,
                    template.name,
                    name(want)
                ),
            );
        } else {
            let mut inferred = vec![None; template.parameters.len()];
            for (argument, &index) in payload.iter().zip(declared.payload) {
                self.allow_array_value(argument);
                let actual = self.expr(argument, None);
                self.reject_extraction(argument, &actual);
                if actual == Ty::Never {
                    self.record_variant(id, None, variant as u32);
                    return Ty::Never;
                }
                if actual == Ty::Error {
                    return Ty::Error;
                }
                if matches!(actual, Ty::Reference { .. }) {
                    let failure =
                        templates::unsupported_reference_argument(template, argument.span);
                    self.error(failure.code, failure.span, failure.message);
                    return Ty::Error;
                }
                if matches!(actual, Ty::Function(..)) || actual == UNIT {
                    self.error(
                        17,
                        argument.span,
                        format!("this {} payload type is not supported yet", template.name),
                    );
                    return Ty::Error;
                }
                if let Err(failure) = self.table.check_template_argument(
                    template,
                    template.parameters[index],
                    &actual,
                    argument.span,
                ) {
                    self.error(failure.code, failure.span, failure.message);
                    return Ty::Error;
                }
                inferred[index] = Some(ResolvedArgument::Type(actual));
            }
            if let Some(resolved) = inferred.into_iter().collect() {
                let ty = self.table.instantiate_enum(template, resolved, expr.span);
                let Ty::Enum(enum_id, _) = ty else {
                    unreachable!("enum template instantiation")
                };
                self.record_variant(id, Some(TypeId(enum_id)), variant as u32);
                return ty;
            }
            self.error(
                2,
                expr.span,
                format!(
                    "cannot determine {}'s outcome type; provide a '{}' annotation",
                    declared.name,
                    template.annotation()
                ),
            );
            return Ty::Error;
        }
        for argument in payload {
            self.allow_array_value(argument);
            self.expr(argument, None);
        }
        Ty::Error
    }

    fn record_variant(&mut self, id: Option<ExprId>, enum_id: Option<TypeId>, variant: u32) {
        if let Some((facts, expression)) = self.facts.as_mut().zip(id) {
            facts.variant_uses.push(VariantUse {
                expression,
                enum_id,
                variant,
            });
        }
    }
    /// A variant written without arguments. Variants with a payload need the
    /// call form (TE028).
    fn unit_variant(
        &mut self,
        expr: &Expr,
        id: Option<ExprId>,
        path: &[String],
        enum_ty: Ty,
        variant: Option<u32>,
    ) -> Ty {
        let Ty::Enum(enum_id, _) = &enum_ty else {
            unreachable!("variant paths name enums")
        };
        let table = Rc::clone(&self.table);
        let info = &table.info(*enum_id);
        let Some(variant) = variant else {
            self.error(
                28,
                expr.span,
                format!(
                    "enum '{}' has no variant '{}'",
                    info.name,
                    path[path.len() - 1]
                ),
            );
            return Ty::Error;
        };
        let declared = &info.variants[variant as usize];
        if !declared.payload.is_empty() {
            self.error(
                28,
                expr.span,
                format!(
                    "variant '{}::{}' carries {} payload value(s); construct it as {}::{}(...)",
                    info.name,
                    declared.name,
                    declared.payload.len(),
                    info.name,
                    declared.name
                ),
            );
            return Ty::Error;
        }
        if self.lowering && !self.array_allowed(expr) {
            self.error(
                17,
                expr.span,
                "enum values must be used as an owned value (binding initializer, assignment, argument, result, field, element or branch value); they cannot be a temporary",
            );
        }
        self.record_variant(id, Some(TypeId(*enum_id)), variant);
        enum_ty
    }
    /// `Enum::Variant(payload...)`: arity and payload types are checked like a
    /// call; arguments are owned-value positions evaluated left to right.
    fn variant_call(
        &mut self,
        expr: &Expr,
        id: Option<ExprId>,
        arguments: &[Expr],
        enum_ty: Ty,
        variant: Option<u32>,
    ) -> Ty {
        let Ty::Enum(enum_id, _) = &enum_ty else {
            unreachable!("variant paths name enums")
        };
        let table = Rc::clone(&self.table);
        let info = &table.info(*enum_id);
        let ExprKind::Call { callee, .. } = &expr.kind else {
            unreachable!("variant calls are calls")
        };
        let ExprKind::Path(path) = &callee.kind else {
            unreachable!("variant calls have path callees")
        };
        let Some(variant) = variant else {
            for argument in arguments {
                self.expr(argument, None);
            }
            self.error(
                28,
                callee.span,
                format!(
                    "enum '{}' has no variant '{}'",
                    info.name,
                    path[path.len() - 1]
                ),
            );
            return Ty::Error;
        };
        let declared = &info.variants[variant as usize];
        if declared.payload.is_empty() {
            for argument in arguments {
                self.expr(argument, None);
            }
            self.error(
                28,
                expr.span,
                format!(
                    "variant '{}::{}' has no payload; write it without parentheses",
                    info.name, declared.name
                ),
            );
            return enum_ty;
        }
        if declared.payload.len() != arguments.len() {
            self.error(
                10,
                expr.span,
                format!(
                    "variant '{}::{}' expects {} argument(s), found {}",
                    info.name,
                    declared.name,
                    declared.payload.len(),
                    arguments.len()
                ),
            );
        }
        let mut diverges = false;
        for (index, argument) in arguments.iter().enumerate() {
            let want = declared.payload.get(index);
            if want.is_some_and(|ty| {
                matches!(
                    ty,
                    Ty::String | Ty::Array(..) | Ty::Struct(..) | Ty::Tuple(..) | Ty::Enum(..)
                )
            }) {
                self.allow_array_value(argument);
            }
            let actual = self.expr(argument, want);
            self.reject_extraction(argument, &actual);
            if let Some(want) = want {
                if matches!(want, Ty::Reference { .. })
                    && !matches!(
                        actual,
                        Ty::Reference {
                            access: IrAccess::Borrow,
                            ..
                        } | Ty::Never
                            | Ty::Error
                    )
                {
                    self.error(
                        17,
                        argument.span,
                        "Some requires a borrow reference for (borrow T)?",
                    );
                } else {
                    self.ensure(&actual, want, argument.span);
                }
            }
            diverges |= actual == Ty::Never;
        }
        self.record_variant(id, Some(TypeId(*enum_id)), variant);
        if diverges {
            Ty::Never
        } else {
            enum_ty
        }
    }
    /// `match scrutinee { pattern => body, ... }`. Patterns nest to any depth
    /// over enum variants and tuples, with `_` and bindings in any position.
    /// An owned scrutinee is consumed and each arm binds owned payload locals;
    /// a scrutinee that cannot be moved (a reference, an element or field
    /// place) is matched in place and binds copies of primitives and
    /// read-only references to aggregates. Arms are checked with a pattern
    /// matrix: an arm no value reaches is unreachable (TE032) and the match
    /// must cover every value (TE031, naming uncovered example patterns).
    fn match_expr(
        &mut self,
        expr: &Expr,
        id: Option<ExprId>,
        scrutinee: &Expr,
        arms: &[MatchArm],
        expected: Option<&Ty>,
    ) -> Ty {
        self.allow_array_value(scrutinee);
        let scrutinee_ty = self.expr(scrutinee, None);
        let table = Rc::clone(&self.table);
        // The matched type: an enum or a tuple (behind the reference, if any).
        let mut column: Option<Ty> = None;
        // A scrutinee that cannot be moved (a reference, or an element or field
        // place) is matched in place: payload bindings borrow the payload.
        let mut borrowed = false;
        match &scrutinee_ty {
            Ty::Enum(..) | Ty::Tuple(..) => {
                borrowed = matches!(
                    scrutinee.kind,
                    ExprKind::Index { .. } | ExprKind::Field { .. }
                );
                column = Some(scrutinee_ty.clone());
            }
            Ty::Reference { inner, .. }
                if matches!(inner.as_ref(), Ty::Enum(..) | Ty::Tuple(..)) =>
            {
                borrowed = true;
                column = Some((**inner).clone());
            }
            Ty::Never | Ty::Error => {}
            other => self.error(
                29,
                scrutinee.span,
                format!("`match` requires an enum value, found {}", name(other)),
            ),
        }
        let signature = {
            let table = Rc::clone(&table);
            move |ty: &Ty| -> Option<Vec<Vec<Ty>>> {
                match ty {
                    Ty::Enum(id, _) => Some(
                        table
                            .info(*id)
                            .variants
                            .iter()
                            .map(|variant| variant.payload.clone())
                            .collect(),
                    ),
                    Ty::Tuple(id, ..) => Some(vec![table
                        .info(*id)
                        .fields
                        .iter()
                        .map(|field| field.ty.clone())
                        .collect()]),
                    _ => None,
                }
            }
        };
        let mut matrix: Vec<Vec<patterns::Pat>> = Vec::new();
        let mut irrefutable_seen = false;
        let mut tainted = false;
        let mut result: Option<Ty> = None;
        let mut facts = Vec::new();
        for arm in arms {
            self.scopes.push(HashMap::new());
            let mut arm_tainted = false;
            let pattern = self.check_pattern(
                &arm.pattern,
                column.as_ref().unwrap_or(&Ty::Error),
                borrowed,
                true,
                &mut Vec::new(),
                &mut arm_tainted,
            );
            tainted |= arm_tainted;
            if let (Some(column), false) = (&column, arm_tainted) {
                let row = vec![patterns::Pat::from_fact(&pattern)];
                let top_level_wildcard = matches!(row[0], patterns::Pat::Wild);
                if !patterns::is_useful(&signature, &matrix, &row, std::slice::from_ref(column)) {
                    let message = if irrefutable_seen {
                        "unreachable match arm: an earlier `_` arm already matches every variant"
                            .to_string()
                    } else if top_level_wildcard {
                        "unreachable `_` arm: every variant is already matched by an earlier arm"
                            .to_string()
                    } else if let (MatchPattern::Variant { variant, args }, Ty::Enum(..)) =
                        (&pattern, column)
                    {
                        if args.iter().all(|arg| {
                            matches!(arg, MatchPattern::Wildcard | MatchPattern::Bind(_))
                        }) {
                            format!(
                                "unreachable match arm: variant '{}' is already matched by an earlier arm",
                                patterns::TableNames(&table).variant_name(column, *variant)
                            )
                        } else {
                            format!(
                                "unreachable match arm: pattern `{}` is already matched by earlier arms",
                                render_pattern(&arm.pattern)
                            )
                        }
                    } else {
                        format!(
                            "unreachable match arm: pattern `{}` is already matched by earlier arms",
                            render_pattern(&arm.pattern)
                        )
                    };
                    self.error(32, arm.pattern.span, message);
                }
                irrefutable_seen |= top_level_wildcard;
                matrix.push(row);
            }
            facts.push(MatchArmFact { pattern });
            let arm_expected = expected.or(result.as_ref().filter(|ty| **ty != Ty::Never));
            let ty = self.expr(&arm.body, arm_expected);
            self.reject_extraction(&arm.body, &ty);
            self.scopes.pop();
            if matches!(ty, Ty::Reference { .. }) || self.table.is_borrow_option(&ty) {
                self.error(
                    17,
                    arm.body.span,
                    "reference-valued match arm results are not supported",
                );
            }
            result = Some(match result.take() {
                None => ty,
                Some(previous) => {
                    if !compatible(&ty, &previous) && !compatible(&previous, &ty) {
                        self.error(
                            13,
                            arm.body.span,
                            format!(
                                "match arms have incompatible types: {} and {}",
                                name(&previous),
                                name(&ty)
                            ),
                        );
                        Ty::Error
                    } else if previous == Ty::Never {
                        ty
                    } else {
                        previous
                    }
                }
            });
        }
        if let (Some(column), false) = (&column, tainted) {
            let uncovered = patterns::missing(
                &signature,
                &matrix,
                std::slice::from_ref(column),
                MAX_MISSING_PATTERNS,
            );
            if !uncovered.is_empty() {
                let names = patterns::TableNames(&table);
                let examples: Vec<String> = uncovered
                    .iter()
                    .map(|witness| format!("`{}`", patterns::render(&witness[0], &names)))
                    .collect();
                self.error(
                    31,
                    expr.span,
                    format!(
                        "non-exhaustive match: missing {}; add arms for them or a `_` arm",
                        examples.join(", ")
                    ),
                );
            }
        }
        if let Some((facts_out, expression)) = self.facts.as_mut().zip(id) {
            facts_out.matches.push(MatchFact {
                expression,
                borrowed,
                arms: facts,
            });
        }
        if scrutinee_ty == Ty::Never {
            return Ty::Never;
        }
        result.unwrap_or(Ty::Error)
    }
    /// Check one pattern against the type it matches and register its
    /// bindings in the current arm scope. Errors set `tainted` and yield `_`.
    fn check_pattern(
        &mut self,
        pattern: &Pattern,
        expected: &Ty,
        borrowed: bool,
        top_level: bool,
        names: &mut Vec<String>,
        tainted: &mut bool,
    ) -> MatchPattern {
        match &pattern.kind {
            PatternKind::Wildcard => MatchPattern::Wildcard,
            PatternKind::Binding(binding) => {
                let path = std::slice::from_ref(binding);
                let enum_context = matches!(expected, Ty::Enum(..)).then_some(expected);
                if self
                    .contextual_variant(path, pattern.span, enum_context)
                    .is_some()
                    || self.prelude_variant(path).is_some()
                {
                    return self.check_variant_pattern(
                        pattern,
                        path,
                        &[],
                        expected,
                        borrowed,
                        names,
                        tainted,
                    );
                }
                if top_level {
                    self.error(
                        30,
                        pattern.span,
                        format!(
                            "'{binding}' is not an enum variant pattern; binding patterns are not supported, write `_` to match anything"
                        ),
                    );
                    *tainted = true;
                    return MatchPattern::Wildcard;
                }
                if names.contains(binding) {
                    self.error(
                        30,
                        pattern.span,
                        format!("binding '{binding}' is introduced more than once in the pattern"),
                    );
                    *tainted = true;
                }
                names.push(binding.clone());
                let addr = pattern as *const Pattern as usize;
                // A borrowing match binds primitives by copy and every
                // aggregate payload as a read-only reference to it.
                let bound_ty = if borrowed
                    && matches!(
                        expected,
                        Ty::String | Ty::Array(..) | Ty::Struct(..) | Ty::Tuple(..) | Ty::Enum(..)
                    ) {
                    Ty::Reference {
                        access: IrAccess::Borrow,
                        inner: Box::new(expected.clone()),
                        origin: ReferenceOrigin::Binding(addr),
                    }
                } else {
                    expected.clone()
                };
                let local = self.register_local(
                    binding,
                    &bound_ty,
                    false,
                    IrAccess::Owned,
                    pattern.span,
                    addr,
                );
                self.scopes.last_mut().unwrap().insert(
                    binding.clone(),
                    Binding {
                        ty: bound_ty,
                        mutable: false,
                        access: IrAccess::Owned,
                        id: local,
                        origin: addr,
                    },
                );
                MatchPattern::Bind(local)
            }
            PatternKind::Variant { path, slots } => {
                self.check_variant_pattern(pattern, path, slots, expected, borrowed, names, tainted)
            }
            PatternKind::Tuple(elements) => {
                let mut field_types: Option<Vec<Ty>> = None;
                match expected {
                    Ty::Tuple(id, ..) => {
                        let fields = self.table.info(*id).fields;
                        if fields.len() == elements.len() {
                            field_types =
                                Some(fields.iter().map(|field| field.ty.clone()).collect());
                        } else {
                            self.error(
                                30,
                                pattern.span,
                                format!(
                                    "tuple pattern has {} element(s) but the matched tuple has {}",
                                    elements.len(),
                                    fields.len()
                                ),
                            );
                            *tainted = true;
                        }
                    }
                    Ty::Error | Ty::Never => *tainted = true,
                    other => {
                        self.error(
                            30,
                            pattern.span,
                            format!(
                                "a tuple pattern cannot match a value of type '{}'",
                                name(other)
                            ),
                        );
                        *tainted = true;
                    }
                }
                let args = elements
                    .iter()
                    .enumerate()
                    .map(|(index, element)| {
                        let element_ty = field_types
                            .as_ref()
                            .map_or(Ty::Error, |types| types[index].clone());
                        self.check_pattern(element, &element_ty, borrowed, false, names, tainted)
                    })
                    .collect();
                if field_types.is_some() {
                    MatchPattern::Tuple(args)
                } else {
                    MatchPattern::Wildcard
                }
            }
        }
    }
    #[allow(clippy::too_many_arguments)]
    fn check_variant_pattern(
        &mut self,
        pattern: &Pattern,
        path: &[String],
        slots: &[Pattern],
        expected: &Ty,
        borrowed: bool,
        names: &mut Vec<String>,
        tainted: &mut bool,
    ) -> MatchPattern {
        let table = Rc::clone(&self.table);
        let span = pattern.span;
        let expected_enum = matches!(expected, Ty::Enum(..)).then_some(expected);
        let contextual = self.contextual_variant(path, span, expected_enum);
        let resolved = if contextual.is_some() {
            contextual
        } else if let Some((template, _)) = self.prelude_variant(path) {
            self.error(
                30,
                span,
                format!(
                    "pattern '{}' belongs to {}, but the value being matched has type '{}'",
                    path[0],
                    template.name,
                    name(expected)
                ),
            );
            None
        } else {
            self.error(
                30,
                span,
                format!("'{}' does not name an enum variant", path.join("::")),
            );
            None
        };
        let mut declared_payload: Option<Vec<Ty>> = None;
        let mut selected: Option<u32> = None;
        match &resolved {
            Some((Ty::Enum(pattern_enum, pattern_name), variant)) => {
                let pattern_info = table.info(*pattern_enum);
                match expected {
                    Ty::Enum(expected_enum, _) if expected_enum != pattern_enum => {
                        self.error(
                            30,
                            span,
                            format!(
                                "pattern '{}' belongs to enum '{}', but the value being matched has type '{}'",
                                path.join("::"),
                                pattern_name,
                                name(expected)
                            ),
                        );
                    }
                    Ty::Enum(..) => match variant {
                        None => self.error(
                            30,
                            span,
                            format!(
                                "enum '{}' has no variant '{}'",
                                pattern_info.name,
                                path[path.len() - 1]
                            ),
                        ),
                        Some(variant) => {
                            let declared = &pattern_info.variants[*variant as usize];
                            selected = Some(*variant);
                            declared_payload = Some(declared.payload.clone());
                            if slots.len() != declared.payload.len() {
                                self.error(
                                    30,
                                    span,
                                    format!(
                                        "variant '{}::{}' has {} payload value(s) but the pattern binds {}; bind each one by name or `_`",
                                        pattern_info.name,
                                        declared.name,
                                        declared.payload.len(),
                                        slots.len()
                                    ),
                                );
                            }
                        }
                    },
                    Ty::Error | Ty::Never => {}
                    other => self.error(
                        30,
                        span,
                        format!(
                            "pattern '{}' belongs to enum '{}', but the value being matched has type '{}'",
                            path.join("::"),
                            pattern_name,
                            name(other)
                        ),
                    ),
                }
            }
            _ => {}
        }
        if selected.is_none() || declared_payload.as_ref().map(Vec::len) != Some(slots.len()) {
            *tainted = true;
        }
        let args = slots
            .iter()
            .enumerate()
            .map(|(index, slot)| {
                let slot_ty = declared_payload
                    .as_ref()
                    .and_then(|payload| payload.get(index))
                    .cloned()
                    .unwrap_or(Ty::Error);
                self.check_pattern(slot, &slot_ty, borrowed, false, names, tainted)
            })
            .collect();
        match selected {
            Some(variant) => MatchPattern::Variant { variant, args },
            None => MatchPattern::Wildcard,
        }
    }
    fn expr_impl(&mut self, expr: &Expr, expected: Option<&Ty>, id: Option<ExprId>) -> Ty {
        match &expr.kind {
            ExprKind::Call {
                callee,
                arguments,
                interface: None,
            } if matches!(&callee.kind, ExprKind::Path(path)
            if (path.len() == 1 && self.generic_functions.contains_key(&path[0]))
                || (path.len() > 1 && {
                    let expanded = self.imports.get(&path[0]).map_or_else(
                        || path.join("::"),
                        |target| format!("{}::{}", target, path[1..].join("::")),
                    );
                    self.generic_functions
                        .contains_key(expanded.strip_prefix("self::").unwrap_or(&expanded))
                })) =>
            {
                self.generic_identity_call(expr, callee, arguments, expected)
            }
            ExprKind::Path(path)
                if self.contextual_variant(path, expr.span, expected).is_some() =>
            {
                let (enum_ty, variant) = self
                    .contextual_variant(path, expr.span, expected)
                    .expect("checked variant path");
                self.unit_variant(expr, id, path, enum_ty, variant)
            }
            ExprKind::Call {
                callee, arguments, ..
            } if matches!(&callee.kind, ExprKind::Path(path)
                    if self.contextual_variant(path, callee.span, expected).is_some()) =>
            {
                let ExprKind::Path(path) = &callee.kind else {
                    unreachable!("checked variant callee")
                };
                let (enum_ty, variant) = self
                    .contextual_variant(path, callee.span, expected)
                    .expect("checked variant path");
                self.variant_call(expr, id, arguments, enum_ty, variant)
            }
            ExprKind::Array(elements) => {
                if self.lowering && !self.array_allowed(expr) {
                    self.error(
                        17,
                        expr.span,
                        "array literals must be used as an owned value (binding initializer, assignment, argument, element, result or branch value)",
                    );
                }
                if let Some(list @ Ty::List(element)) = expected {
                    // Elements evaluate once, in written order, and move in.
                    for item in elements {
                        self.allow_array_value(item);
                        let actual = self.expr(item, Some(element));
                        self.reject_extraction(item, &actual);
                        if matches!(actual, Ty::Reference { .. }) {
                            self.error(17, item.span, "List elements cannot be references");
                        }
                        self.ensure(&actual, element, item.span);
                    }
                    self.check_list_element_support(element, expr.span);
                    return list.clone();
                }
                let mut element_ty = match expected {
                    Some(Ty::Array(element, _)) => Some(element.as_ref().clone()),
                    _ => None,
                };
                for element in elements {
                    self.allow_array_value(element);
                    let actual = self.expr(element, element_ty.as_ref());
                    self.reject_extraction(element, &actual);
                    if matches!(actual, Ty::Reference { .. }) {
                        self.error(17, element.span, "array elements cannot be references yet");
                    }
                    if let Some(want) = &element_ty {
                        self.ensure(&actual, want, element.span);
                    } else if !matches!(actual, Ty::Error | Ty::Never) {
                        element_ty = Some(actual);
                    }
                }
                let Some(element) = element_ty else {
                    self.error(
                        2,
                        expr.span,
                        "cannot infer empty array element type; add an Array annotation",
                    );
                    return Ty::Error;
                };
                self.check_element_support(&element, expr.span);
                match u32::try_from(elements.len()) {
                    Ok(count) => Ty::Array(Box::new(element), count),
                    Err(_) => {
                        self.error(
                            8,
                            expr.span,
                            "array length exceeds implementation limit u32::MAX",
                        );
                        Ty::Error
                    }
                }
            }
            ExprKind::Tuple(elements) => {
                let labeled = elements
                    .iter()
                    .filter(|element| element.label.is_some())
                    .count();
                let mut seen = HashSet::new();
                let expected_fields = match expected {
                    Some(Ty::Tuple(id, _, aliases)) => {
                        let info = self.table.info(*id);
                        (info.module == "\0tuple").then_some((info.fields, aliases.clone()))
                    }
                    _ => None,
                };
                if let Some((fields, aliases)) = expected_fields {
                    if fields.len() != elements.len() {
                        self.error(2, expr.span, "tuple arity does not match its expected type");
                        return Ty::Error;
                    }
                    for (position, element) in elements.iter().enumerate() {
                        let index = if let Some(label) = &element.label {
                            aliases
                                .labels
                                .iter()
                                .position(|alias| alias.as_deref() == Some(label))
                        } else {
                            (labeled == 0).then_some(position)
                        };
                        let Some(index) = index else {
                            self.error(
                                2,
                                element.span,
                                format!(
                                    "unknown tuple label '{}'",
                                    element.label.as_deref().unwrap_or("")
                                ),
                            );
                            continue;
                        };
                        if !seen.insert(index) {
                            self.error(2, element.span, "duplicate tuple initializer label");
                            continue;
                        }
                        let field = &fields[index];
                        let field_ty =
                            with_tuple_aliases(field.ty.clone(), aliases.nested[index].as_deref());
                        self.allow_array_value(&element.value);
                        let actual = self.expr(&element.value, Some(&field_ty));
                        self.ensure(&actual, &field_ty, element.value.span);
                    }
                    if seen.len() != fields.len() {
                        self.error(2, expr.span, "tuple initializer must provide every element");
                    }
                    if let Some(facts) = &mut self.facts {
                        facts.tuple_initializers.push(TupleInitializerFact {
                            node_addr: expr as *const Expr as usize,
                            slots: elements
                                .iter()
                                .map(|element| {
                                    if let Some(label) = &element.label {
                                        aliases
                                            .labels
                                            .iter()
                                            .position(|alias| alias.as_deref() == Some(label))
                                            .unwrap_or(0)
                                            as u32
                                    } else {
                                        elements
                                            .iter()
                                            .position(|candidate| std::ptr::eq(candidate, element))
                                            .unwrap_or(0)
                                            as u32
                                    }
                                })
                                .collect(),
                        });
                    }
                    expected.cloned().unwrap_or(Ty::Error)
                } else {
                    if labeled != 0 && labeled != elements.len() {
                        self.error(
                            2,
                            expr.span,
                            "tuple elements must be either all labeled or all positional",
                        );
                        return Ty::Error;
                    }
                    if labeled != 0 {
                        let mut seen_labels = HashSet::new();
                        for element in elements {
                            let label = element.label.as_deref().expect("all elements are labeled");
                            if !seen_labels.insert(label) {
                                self.error(
                                    2,
                                    element.span,
                                    format!("duplicate tuple initializer label '{label}'"),
                                );
                                return Ty::Error;
                            }
                        }
                    }
                    let element_types = elements
                        .iter()
                        .map(|element| {
                            self.allow_array_value(&element.value);
                            (element.label.clone(), self.expr(&element.value, None))
                        })
                        .collect::<Vec<_>>();
                    if element_types
                        .iter()
                        .any(|(_, ty)| matches!(ty, Ty::Error | Ty::Never))
                    {
                        return Ty::Error;
                    }
                    let has_embedded_reference = element_types
                        .iter()
                        .any(|(_, ty)| self.contains_reference(ty, &mut HashSet::new()));
                    if has_embedded_reference {
                        self.error(17, expr.span, "tuple elements cannot contain direct or nested references until embedded tuple loans are supported");
                        return Ty::Error;
                    }
                    match self.table.instantiate_tuple(element_types, expr.span) {
                        Ok(ty) => ty,
                        Err(failure) => {
                            self.error(failure.code, failure.span, failure.message);
                            Ty::Error
                        }
                    }
                }
            }
            ExprKind::RepeatArray { value, count } => {
                if self.lowering && !self.array_allowed(expr) {
                    self.error(
                        17,
                        expr.span,
                        "array repetition must be used as an owned value (binding initializer, assignment, argument, element, result or branch value)",
                    );
                }
                let context = match expected {
                    Some(Ty::Array(element, _)) => Some(element.as_ref()),
                    _ => None,
                };
                // Check the expression exactly once, even for a zero count. Runtime
                // repetition and ownership are deliberately gated from typed IR.
                self.allow_array_value(value);
                let element = self.expr(value, context);
                self.reject_extraction(value, &element);
                if matches!(element, Ty::Reference { .. }) {
                    self.error(17, value.span, "array elements cannot be references yet");
                }
                if self.lowering && matches!(element, Ty::Never) && context.is_none() {
                    self.error(
                        2,
                        expr.span,
                        "cannot infer repeated element type; add an Array annotation",
                    );
                }
                self.check_element_support(&element, expr.span);
                if self.lowering
                    && self.contains_string_owner(&element, &mut HashSet::new())
                    && !matches!(value.kind, ExprKind::StringLiteral(_))
                {
                    self.error(
                        17,
                        value.span,
                        "`[value; N]` would copy a String-owning element; owners are moved, never copied, so list each element in an array literal or build the array from separate named owners",
                    );
                }
                let count = self.array_count(count);
                if let Some(context) = context {
                    if !matches!(element, Ty::Never | Ty::Error) {
                        self.ensure(&element, context, value.span);
                    }
                }
                match count {
                    Some(count) => {
                        let element = if matches!(element, Ty::Never) {
                            context.cloned().unwrap_or(Ty::Never)
                        } else {
                            element
                        };
                        Ty::Array(Box::new(element), count)
                    }
                    None => Ty::Error,
                }
            }
            ExprKind::Index { base, index } => {
                if self.lowering {
                    match &base.kind {
                        ExprKind::Path(path) if path.len() == 1 => {
                            self.index_base = base.as_ref() as *const Expr as usize;
                        }
                        // A row, field or element of a projection chain; its own
                        // arm marks the root.
                        ExprKind::Index { .. } | ExprKind::Field { .. } => {}
                        _ => self.error(
                            17,
                            base.span,
                            "indexing is supported on named local arrays and projections of them only; bind the array to a local first",
                        ),
                    }
                }
                let base_ty = self.expr(base, None);
                let index_ty = self.expr(index, None);
                if !integer(&index_ty) && !matches!(index_ty, Ty::Never | Ty::Error) {
                    self.error(7, index.span, "array index must be an integer");
                }
                // An array reference (`borrow`/`share` parameter or binding)
                // indexes like its owner.
                let base_ty = match base_ty {
                    Ty::Reference { inner, .. }
                        if matches!(inner.as_ref(), Ty::Array(..) | Ty::List(_)) =>
                    {
                        *inner
                    }
                    other => other,
                };
                let result = match base_ty {
                    Ty::List(element) => *element,
                    Ty::Array(element, count) => {
                        if let Some(value) = constant_index(index) {
                            if value < 0 || value >= i128::from(count) {
                                self.error(8, index.span, format!("constant array index {value} is out of bounds for length {count}"));
                            }
                        }
                        *element
                    }
                    Ty::Never | Ty::Error => Ty::Error,
                    other => {
                        self.error(
                            7,
                            base.span,
                            format!(
                                "indexing requires an Array or List value, found {}",
                                name(&other)
                            ),
                        );
                        Ty::Error
                    }
                };
                result
            }
            ExprKind::Number(raw) => {
                let float_literal = raw.contains(['.', 'e', 'E']);
                let chosen = if let Some(want) = expected {
                    if (float_literal && floating(want)) || (!float_literal && integer(want)) {
                        want.clone()
                    } else {
                        if float_literal {
                            F64
                        } else {
                            I32
                        }
                    }
                } else if float_literal {
                    F64
                } else {
                    I32
                };
                if let Ty::Primitive(kind) = chosen {
                    let cleaned = raw.replace('_', "");
                    if integer(&chosen) {
                        let limit = int_limit(kind);
                        if cleaned
                            .parse::<u128>()
                            .ok()
                            .zip(limit)
                            .is_none_or(|(n, max)| n > max)
                        {
                            self.error(
                                8,
                                expr.span,
                                format!("integer literal does not fit {kind}"),
                            );
                        }
                    } else if cleaned.parse::<f64>().is_err() {
                        self.error(8, expr.span, "invalid floating-point literal");
                    }
                }
                chosen
            }
            ExprKind::StringLiteral(_) => Ty::String,
            ExprKind::CharLiteral(_) => Ty::Primitive("char"),
            ExprKind::Bool(_) => BOOL,
            ExprKind::Path(path) => {
                if let Some((function, signature)) = self
                    .generic_path_targets
                    .get(&(expr as *const Expr as usize))
                    .cloned()
                {
                    if let Some((facts, expression)) = self.facts.as_mut().zip(id) {
                        facts.path_uses.push(PathUse {
                            expression,
                            target: PathTarget::Function(function),
                            access: None,
                        });
                    }
                    return signature;
                }
                if let Some((template, variant)) = self.prelude_variant(path) {
                    return self.infer_variant(expr, id, template, variant, None, expected);
                }
                if path.len() != 1 {
                    let expanded = self.imports.get(&path[0]).map_or_else(
                        || path.join("::"),
                        |target| format!("{}::{}", target, path[1..].join("::")),
                    );
                    let key = expanded.strip_prefix("self::").unwrap_or(&expanded);
                    if let (Some(facts), Some(expression), Some(function)) = (
                        self.facts.as_mut(),
                        id,
                        self.qualified_function_ids.get(key).copied(),
                    ) {
                        facts.path_uses.push(PathUse {
                            expression,
                            target: PathTarget::Function(function),
                            access: None,
                        });
                    }
                    return self
                        .qualified_functions
                        .get(key)
                        .cloned()
                        .unwrap_or_else(|| {
                            self.error(
                                9,
                                expr.span,
                                format!(
                                    "unresolved or unsupported qualified function '{expanded}'"
                                ),
                            );
                            Ty::Error
                        });
                }
                if let Some(binding) = self.lookup(&path[0]).cloned() {
                    if let Some((facts, expression, local)) =
                        self.facts.as_mut().zip(id).and_then(|(facts, expression)| {
                            binding.id.map(|local| (facts, expression, local))
                        })
                    {
                        facts.path_uses.push(PathUse {
                            expression,
                            target: PathTarget::Local(local),
                            access: Some(binding.access),
                        });
                    }
                    if self.lowering
                        && matches!(
                            binding.ty,
                            Ty::String
                                | Ty::Array(..)
                                | Ty::Struct(..)
                                | Ty::Tuple(..)
                                | Ty::Enum(..)
                        )
                        && self.index_base != expr as *const Expr as usize
                        && !self.array_allowed(expr)
                    {
                        self.error(
                            17,
                            expr.span,
                            "whole arrays and structs can only be moved into a binding, assignment, argument, element, result or branch value, or indexed or read by field",
                        );
                    }
                    return binding.ty;
                }
                if let Some(ty) = self.functions.get(&path[0]).cloned() {
                    if let Some((facts, expression, function)) =
                        self.facts.as_mut().zip(id).and_then(|(facts, expression)| {
                            self.function_ids
                                .get(&path[0])
                                .copied()
                                .map(|function| (facts, expression, function))
                        })
                    {
                        facts.path_uses.push(PathUse {
                            expression,
                            target: PathTarget::Function(function),
                            access: None,
                        });
                    }
                    return ty;
                }
                self.error(5, expr.span, format!("unresolved name '{}'", path[0]));
                Ty::Error
            }
            ExprKind::Unary { operator, operand } => {
                // A leading minus is part of a floating literal's contextual
                // type. Checking the unsigned magnitude without context would
                // default it to f64 before the surrounding f32 can apply.
                if operator == "-" {
                    if let ExprKind::Number(raw) = &operand.kind {
                        if raw.contains(['.', 'e', 'E']) {
                            let chosen = expected.filter(|ty| floating(ty)).cloned().unwrap_or(F64);
                            // Check the magnitude under the same context so it
                            // gets a type fact for lowering as well as the
                            // unary expression receiving that type.
                            self.expr(operand, Some(&chosen));
                            return chosen;
                        }
                    }
                }
                if operator == "-" {
                    if let ExprKind::Number(raw) = &operand.kind {
                        if !raw.contains(['.', 'e', 'E']) {
                            let chosen = expected.filter(|t| integer(t)).cloned().unwrap_or(I32);
                            if let Ty::Primitive(kind) = chosen {
                                if !kind.starts_with('u') {
                                    let value = raw.replace('_', "").parse::<u128>();
                                    if value
                                        .ok()
                                        .zip(int_limit(kind))
                                        .is_none_or(|(n, max)| n > max + 1)
                                    {
                                        self.error(
                                            8,
                                            expr.span,
                                            format!("integer literal does not fit {kind}"),
                                        );
                                    }
                                    return Ty::Primitive(kind);
                                }
                            }
                        }
                    }
                }
                if operator == "-" {
                    self.allow_array_value(operand);
                    let operand_ty = read_type(self.expr(operand, None));
                    if matches!(operand_ty, Ty::Struct(..) | Ty::Enum(..)) {
                        let interface = qualified_interface(
                            &self.module,
                            &self.imports,
                            &Type {
                                span: expr.span,
                                path: vec!["core".into(), "ops".into(), "Neg".into()],
                                arguments: Vec::new(),
                            },
                        );
                        let forwarded = self.generic_evidence.iter().find(|evidence| {
                            evidence.interface == interface
                                && evidence.candidate.target == operand_ty
                        });
                        let matching = if let Some(evidence) = forwarded {
                            vec![evidence.candidate.clone()]
                        } else {
                            self.extension_candidates
                                .iter()
                                .filter(|candidate| {
                                    candidate.interface.as_deref() == Some(interface.as_str())
                                        && candidate.target == operand_ty
                                        && candidate.methods.contains_key("neg")
                                })
                                .cloned()
                                .collect::<Vec<_>>()
                        };
                        let applicable = matching
                            .iter()
                            .filter(|candidate| {
                                candidate.visible
                                    && (candidate.local || candidate.public_methods.contains("neg"))
                            })
                            .cloned()
                            .collect::<Vec<_>>();
                        if applicable.len() > 1 {
                            self.error(7, expr.span, "ambiguous Neg implementation for `-`");
                            return Ty::Error;
                        }
                        if let Some(candidate) = applicable.first() {
                            let (receiver_access, parameters, result, _, function) =
                                candidate.methods.get("neg").cloned().unwrap();
                            if receiver_access != Access::Owned || !parameters.is_empty() {
                                self.error(
                                    7,
                                    expr.span,
                                    "Neg requires an owned receiver and no operands",
                                );
                                return Ty::Error;
                            }
                            if let Some((facts, expression)) = self.facts.as_mut().zip(id) {
                                let signature = match ir_type(&Ty::Function(
                                    vec![FunctionParameter {
                                        access: IrAccess::Owned,
                                        ty: operand_ty.clone(),
                                    }],
                                    Box::new(result.clone()),
                                )) {
                                    Some(IrType::Function(signature)) => signature,
                                    _ => return Ty::Error,
                                };
                                facts.selected_operators.push(SelectedCall {
                                    expression,
                                    function,
                                    receiver_access,
                                    signature,
                                });
                            }
                            return result;
                        }
                        self.error(
                            7,
                            expr.span,
                            if matching.is_empty() {
                                "no visible Neg implementation for this operand type"
                            } else {
                                "matching Neg implementation is private or inactive"
                            },
                        );
                        return Ty::Error;
                    }
                    if operand_ty == Ty::Never {
                        return Ty::Never;
                    }
                    if numeric(&operand_ty) {
                        if matches!(operand_ty, Ty::Primitive("u8" | "u16" | "u32" | "u64")) {
                            self.error(7, expr.span, "negation requires a signed numeric type");
                            return Ty::Error;
                        }
                        return operand_ty;
                    }
                    if operand_ty != Ty::Error {
                        self.error(
                            7,
                            expr.span,
                            "negation requires a signed numeric type or Neg implementation",
                        );
                    }
                    return Ty::Error;
                }
                let wanted = if operator == "!" {
                    Some(&BOOL)
                } else {
                    expected.filter(|t| numeric(t))
                };
                let ty = read_type(self.expr(operand, wanted));
                if ty == Ty::Never {
                    return Ty::Never;
                }
                match operator.as_str() {
                    "!" => {
                        self.ensure(&ty, &BOOL, operand.span);
                        BOOL
                    }
                    "+" | "-" if numeric(&ty) => ty,
                    "+" | "-" => {
                        if ty != Ty::Error {
                            self.error(7, expr.span, "unary arithmetic requires a number");
                        }
                        Ty::Error
                    }
                    _ => {
                        self.error(
                            7,
                            expr.span,
                            format!("unsupported unary operator '{operator}'"),
                        );
                        Ty::Error
                    }
                }
            }
            ExprKind::Cast { value, target } => {
                let source = self.expr(value, None);
                let target = self.type_path(target);
                if numeric(&source) && numeric(&target) {
                    target
                } else {
                    self.error(
                        7,
                        expr.span,
                        "numeric casts require an integer or floating-point source and target",
                    );
                    Ty::Error
                }
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                if matches!(
                    operator.as_str(),
                    "+" | "-"
                        | "*"
                        | "/"
                        | "%"
                        | "&"
                        | "^"
                        | "|"
                        | "<<"
                        | ">>"
                        | "=="
                        | "!="
                        | "<"
                        | "<="
                        | ">"
                        | ">="
                ) {
                    if !matches!(&left.kind, ExprKind::Path(path) if path.len() > 1) {
                        self.allow_array_value(left);
                    }
                    if !matches!(&right.kind, ExprKind::Path(path) if path.len() > 1) {
                        self.allow_array_value(right);
                    }
                }
                let bool_op = matches!(operator.as_str(), "&&" | "||");
                let expected_num = if matches!(operator.as_str(), "&" | "^" | "|" | "<<" | ">>") {
                    Some(&U32)
                } else {
                    expected.filter(|t| numeric(t))
                };
                let left_is_literal = matches!(left.kind, ExprKind::Number(_))
                    || matches!(&left.kind, ExprKind::Unary { operator, operand }
                        if (operator == "+" || operator == "-")
                            && matches!(operand.kind, ExprKind::Number(_)));
                let (left_ty, right_ty) = if !bool_op && expected_num.is_none() && left_is_literal {
                    // Resolve the right operand once, then use its numeric type
                    // to constrain a literal on the left.
                    let right_ty = read_type(self.expr(right, None));
                    let left_ty = read_type(self.expr(left, Some(&right_ty)));
                    (left_ty, right_ty)
                } else {
                    let left_ty = read_type(
                        self.expr(left, if bool_op { Some(&BOOL) } else { expected_num }),
                    );
                    let overloaded_arithmetic =
                        matches!(
                            operator.as_str(),
                            "+" | "-" | "*" | "/" | "%" | "&" | "^" | "|" | "<<" | ">>"
                        ) && matches!(left_ty, Ty::Struct(..) | Ty::Enum(..));
                    let overloaded_equality = matches!(operator.as_str(), "==" | "!=")
                        && matches!(left_ty, Ty::Struct(..) | Ty::Enum(..));
                    let right_ty = read_type(self.expr(
                        right,
                        if bool_op {
                            Some(&BOOL)
                        } else if overloaded_arithmetic || overloaded_equality {
                            None
                        } else {
                            Some(&left_ty)
                        },
                    ));
                    (left_ty, right_ty)
                };
                if left_ty == Ty::Never || (right_ty == Ty::Never && !bool_op) {
                    return Ty::Never;
                }
                if matches!(operator.as_str(), "+" | "-" | "*" | "/" | "%")
                    && (matches!(left_ty, Ty::Array(..)) || matches!(right_ty, Ty::Array(..)))
                {
                    self.error(
                        17,
                        expr.span,
                        "arrays do not support user-defined arithmetic",
                    );
                    return Ty::Error;
                }
                if matches!(
                    operator.as_str(),
                    "+" | "-" | "*" | "/" | "%" | "&" | "^" | "|" | "<<" | ">>"
                ) && matches!(left_ty, Ty::Struct(..) | Ty::Enum(..))
                    && left_ty != Ty::Error
                {
                    let (interface_name, method_name, operator_name) = if operator == "<<" {
                        ("Shl", "shl", "Shl")
                    } else if operator == ">>" {
                        ("Shr", "shr", "Shr")
                    } else if operator == "&" {
                        ("BitAnd", "bitand", "BitAnd")
                    } else if operator == "^" {
                        ("BitXor", "bitxor", "BitXor")
                    } else if operator == "|" {
                        ("BitOr", "bitor", "BitOr")
                    } else if operator == "+" {
                        ("Add", "add", "Add")
                    } else if operator == "-" {
                        ("Sub", "sub", "Sub")
                    } else if operator == "*" {
                        ("Mul", "mul", "Mul")
                    } else if operator == "/" {
                        ("Div", "div", "Div")
                    } else {
                        ("Rem", "rem", "Rem")
                    };
                    let add_interface = qualified_interface(
                        &self.module,
                        &self.imports,
                        &Type {
                            span: expr.span,
                            path: vec![
                                "core".to_owned(),
                                "ops".to_owned(),
                                interface_name.to_owned(),
                            ],
                            arguments: Vec::new(),
                        },
                    );
                    let forwarded = self.generic_evidence.iter().find(|evidence| {
                        evidence.interface == add_interface && evidence.candidate.target == left_ty
                    });
                    let matching = if let Some(evidence) = forwarded {
                        vec![evidence.candidate.clone()]
                    } else {
                        self.extension_candidates
                            .iter()
                            .filter(|candidate| {
                                candidate.interface.as_deref() == Some(add_interface.as_str())
                                    && candidate.target == left_ty
                                    && candidate.methods.contains_key(method_name)
                            })
                            .cloned()
                            .collect::<Vec<_>>()
                    };
                    let applicable = matching
                        .iter()
                        .filter(|candidate| {
                            candidate.visible
                                && (candidate.local
                                    || candidate.public_methods.contains(method_name))
                        })
                        .cloned()
                        .collect::<Vec<_>>();
                    if applicable.len() > 1 {
                        self.error(
                            7,
                            expr.span,
                            format!("ambiguous {operator_name} implementation for `{operator}`"),
                        );
                        return Ty::Error;
                    }
                    if let Some(candidate) = applicable.first() {
                        let (receiver_access, parameters, result, _, function) =
                            candidate.methods.get(method_name).cloned().unwrap();
                        if receiver_access != Access::Owned
                            || parameters.len() != 1
                            || parameters[0].access != IrAccess::Owned
                            || parameters[0].ty != right_ty
                        {
                            self.error(7, expr.span, format!("{operator_name} requires an owned receiver and an owned operand matching its associated Rhs"));
                            return Ty::Error;
                        }
                        if let Some((facts, expression)) = self.facts.as_mut().zip(id) {
                            let signature = match ir_type(&Ty::Function(
                                vec![
                                    FunctionParameter {
                                        access: IrAccess::Owned,
                                        ty: left_ty.clone(),
                                    },
                                    parameters[0].clone(),
                                ],
                                Box::new(result.clone()),
                            )) {
                                Some(IrType::Function(signature)) => signature,
                                _ => return Ty::Error,
                            };
                            facts.selected_operators.push(SelectedCall {
                                expression,
                                function,
                                receiver_access,
                                signature,
                            });
                        }
                        return result;
                    }
                    self.error(
                        7,
                        expr.span,
                        if matching.is_empty() {
                            format!(
                                "no visible {operator_name} implementation for this operand type"
                            )
                        } else {
                            format!(
                                "matching {operator_name} implementation is private or inactive"
                            )
                        },
                    );
                    return Ty::Error;
                }
                if matches!(operator.as_str(), "==" | "!=")
                    && matches!(left_ty, Ty::Struct(..) | Ty::Enum(..))
                    && left_ty != Ty::Error
                {
                    let interface_key = qualified_interface(
                        &self.module,
                        &self.imports,
                        &Type {
                            span: expr.span,
                            path: vec!["core".into(), "ops".into(), "PartialEq".into()],
                            arguments: Vec::new(),
                        },
                    );
                    let matching = self
                        .generic_evidence
                        .iter()
                        .find(|evidence| {
                            evidence.interface == interface_key
                                && evidence.candidate.target == left_ty
                        })
                        .map(|evidence| vec![evidence.candidate.clone()])
                        .unwrap_or_else(|| {
                            self.extension_candidates
                                .iter()
                                .filter(|candidate| {
                                    candidate.interface.as_deref() == Some(interface_key.as_str())
                                        && candidate.target == left_ty
                                        && candidate.methods.contains_key("eq")
                                })
                                .cloned()
                                .collect()
                        });
                    let applicable = matching
                        .iter()
                        .filter(|candidate| {
                            candidate.visible
                                && (candidate.local || candidate.public_methods.contains("eq"))
                        })
                        .cloned()
                        .collect::<Vec<_>>();
                    if applicable.len() > 1 {
                        self.error(
                            7,
                            expr.span,
                            format!("ambiguous PartialEq implementation for `{operator}`"),
                        );
                        return Ty::Error;
                    }
                    if let Some(candidate) = applicable.first() {
                        let (receiver_access, parameters, result, _, function) =
                            candidate.methods.get("eq").cloned().unwrap();
                        if receiver_access != Access::Borrow
                            || parameters.len() != 1
                            || parameters[0].access != IrAccess::Owned
                            || parameters[0].ty != right_ty
                            || result != BOOL
                        {
                            self.error(7, expr.span, "PartialEq requires a borrowed receiver, an owned matching operand, and Bool result");
                            return Ty::Error;
                        }
                        if let Some((facts, expression)) = self.facts.as_mut().zip(id) {
                            let signature = match ir_type(&Ty::Function(
                                vec![
                                    FunctionParameter {
                                        access: IrAccess::Borrow,
                                        ty: left_ty.clone(),
                                    },
                                    parameters[0].clone(),
                                ],
                                Box::new(BOOL),
                            )) {
                                Some(IrType::Function(signature)) => signature,
                                _ => return Ty::Error,
                            };
                            facts.selected_operators.push(SelectedCall {
                                expression,
                                function,
                                receiver_access,
                                signature,
                            });
                        }
                        return BOOL;
                    }
                    self.error(
                        7,
                        expr.span,
                        if matching.is_empty() {
                            if matches!(left_ty, Ty::Enum(..)) {
                                "enums without a visible PartialEq implementation cannot be compared with `==` or `!=`; use `match` to inspect the variant"
                            } else {
                                "no visible PartialEq implementation for this operand type"
                            }
                        } else {
                            "matching PartialEq implementation is private or inactive"
                        },
                    );
                    return Ty::Error;
                }
                if matches!(operator.as_str(), "==" | "!=")
                    && matches!(right_ty, Ty::Enum(..))
                    && !matches!(left_ty, Ty::Enum(..))
                {
                    self.error(
                        7,
                        expr.span,
                        "enum equality requires a visible `PartialEq` implementation on the left operand; use `match` to inspect the variant",
                    );
                    return BOOL;
                }
                if matches!(operator.as_str(), "<" | "<=" | ">" | ">=")
                    && matches!(left_ty, Ty::Struct(..) | Ty::Enum(..))
                    && left_ty != Ty::Error
                {
                    let method_name = match operator.as_str() {
                        "<" => "lt",
                        "<=" => "le",
                        ">" => "gt",
                        ">=" => "ge",
                        _ => unreachable!(),
                    };
                    let interface_key = qualified_interface(
                        &self.module,
                        &self.imports,
                        &Type {
                            span: expr.span,
                            path: vec!["core".into(), "ops".into(), "PartialOrd".into()],
                            arguments: Vec::new(),
                        },
                    );
                    let matching = self
                        .generic_evidence
                        .iter()
                        .find(|evidence| {
                            evidence.interface == interface_key
                                && evidence.candidate.target == left_ty
                        })
                        .map(|evidence| vec![evidence.candidate.clone()])
                        .unwrap_or_else(|| {
                            self.extension_candidates
                                .iter()
                                .filter(|candidate| {
                                    candidate.interface.as_deref() == Some(interface_key.as_str())
                                        && candidate.target == left_ty
                                        && candidate.methods.contains_key(method_name)
                                })
                                .cloned()
                                .collect()
                        });
                    let applicable = matching
                        .iter()
                        .filter(|candidate| {
                            candidate.visible
                                && (candidate.local
                                    || candidate.public_methods.contains(method_name))
                        })
                        .cloned()
                        .collect::<Vec<_>>();
                    if applicable.len() > 1 {
                        self.error(
                            7,
                            expr.span,
                            format!("ambiguous PartialOrd implementation for `{operator}`"),
                        );
                        return Ty::Error;
                    }
                    if let Some(candidate) = applicable.first() {
                        let (receiver_access, parameters, result, _, function) =
                            candidate.methods.get(method_name).cloned().unwrap();
                        if receiver_access != Access::Borrow
                            || parameters.len() != 1
                            || parameters[0].access != IrAccess::Owned
                            || parameters[0].ty != right_ty
                            || result != BOOL
                        {
                            self.error(7, expr.span, "PartialOrd requires a borrowed receiver, an owned matching operand, and Bool result");
                            return Ty::Error;
                        }
                        if let Some((facts, expression)) = self.facts.as_mut().zip(id) {
                            let signature = match ir_type(&Ty::Function(
                                vec![
                                    FunctionParameter {
                                        access: IrAccess::Borrow,
                                        ty: left_ty.clone(),
                                    },
                                    parameters[0].clone(),
                                ],
                                Box::new(BOOL),
                            )) {
                                Some(IrType::Function(signature)) => signature,
                                _ => return Ty::Error,
                            };
                            facts.selected_operators.push(SelectedCall {
                                expression,
                                function,
                                receiver_access,
                                signature,
                            });
                        }
                        return BOOL;
                    }
                    self.error(
                        7,
                        expr.span,
                        if matching.is_empty() {
                            "no visible PartialOrd implementation for this operand type"
                        } else {
                            "matching PartialOrd implementation is private or inactive"
                        },
                    );
                    return Ty::Error;
                }
                match operator.as_str() {
                    "&&" | "||" => {
                        self.ensure(&left_ty, &BOOL, left.span);
                        self.ensure(&right_ty, &BOOL, right.span);
                        BOOL
                    }
                    "&" | "^" | "|" | "<<" | ">>" => {
                        self.ensure(&left_ty, &U32, left.span);
                        self.ensure(&right_ty, &U32, right.span);
                        U32
                    }
                    "+" | "-" | "*" | "/" | "%" => {
                        if !numeric(&left_ty) && left_ty != Ty::Error {
                            self.error(7, left.span, "arithmetic requires numbers");
                        }
                        if operator == "%" && !integer(&left_ty) && left_ty != Ty::Error {
                            self.error(7, expr.span, "remainder requires integers");
                        }
                        self.ensure(&right_ty, &left_ty, right.span);
                        if numeric(&left_ty) {
                            left_ty
                        } else {
                            Ty::Error
                        }
                    }
                    "<" | "<=" | ">" | ">=" => {
                        if !numeric(&left_ty) && left_ty != Ty::Error {
                            self.error(7, left.span, "ordering requires numbers");
                        }
                        self.ensure(&right_ty, &left_ty, right.span);
                        BOOL
                    }
                    "==" | "!=" => {
                        if matches!(left_ty, Ty::Enum(..)) {
                            self.error(
                                7,
                                left.span,
                                "enums cannot be compared with `==` or `!=` yet; use `match` to inspect the variant",
                            );
                        } else if !numeric(&left_ty)
                            && left_ty != BOOL
                            && left_ty != Ty::Primitive("char")
                            && left_ty != Ty::Error
                        {
                            self.error(7, left.span, "equality requires numeric or Bool operands");
                        }
                        self.ensure(&right_ty, &left_ty, right.span);
                        BOOL
                    }
                    _ => {
                        self.error(
                            7,
                            expr.span,
                            format!("unsupported binary operator '{operator}'"),
                        );
                        Ty::Error
                    }
                }
            }
            ExprKind::Call {
                callee,
                arguments,
                interface,
            } => {
                if let Some(interface) = interface {
                    return self.interface_selected_call(expr, id, callee, arguments, interface);
                }
                if let ExprKind::Path(path) = &callee.kind {
                    if path.as_slice() == ["drop"]
                        && self.lookup("drop").is_none()
                        && !self.functions.contains_key("drop")
                        && !self.imports.contains_key("drop")
                    {
                        return self.explicit_drop(expr.span, arguments, id);
                    }
                    if path.as_slice() == ["replace"]
                        && self.lookup("replace").is_none()
                        && !self.functions.contains_key("replace")
                        && !self.imports.contains_key("replace")
                    {
                        return self.explicit_replace(expr.span, arguments, id);
                    }
                    if path.as_slice() == ["swap"]
                        && self.lookup("swap").is_none()
                        && !self.functions.contains_key("swap")
                        && !self.imports.contains_key("swap")
                    {
                        return self.explicit_swap(expr.span, arguments, id);
                    }
                    if path.as_slice() == ["assert"]
                        && self.lookup("assert").is_none()
                        && !self.functions.contains_key("assert")
                        && !self.imports.contains_key("assert")
                    {
                        return self.explicit_assert(expr.span, arguments, id);
                    }
                    if let Some((template, variant)) = self.prelude_variant(path) {
                        return self.infer_variant(
                            expr,
                            id,
                            template,
                            variant,
                            Some(arguments),
                            expected,
                        );
                    }
                }
                if let ExprKind::Field { base, name } = &callee.kind {
                    if name == "to_u32" {
                        if !arguments.is_empty() {
                            self.error(7, expr.span, "to_u32() takes no arguments");
                            return Ty::Error;
                        }
                        let source = self.expr(base, None);
                        return self.cast_u8_to_u32(source, expr.span);
                    }
                    if matches!(name.as_str(), "wrapping_add" | "wrapping_mul") {
                        if arguments.len() != 1 {
                            self.error(7, expr.span, "wrapping arithmetic takes one u32 argument");
                            return Ty::Error;
                        }
                        let receiver = self.expr(base, Some(&U32));
                        let argument = self.expr(&arguments[0], Some(&U32));
                        if read_type(receiver) == U32 && read_type(argument) == U32 {
                            return U32;
                        }
                        self.error(7, expr.span, "wrapping arithmetic requires u32 operands");
                        return Ty::Error;
                    }
                    if matches!(name.as_str(), "bit_and" | "bit_xor" | "bit_or") {
                        if arguments.len() != 1 {
                            self.error(7, expr.span, "bitwise methods take one u32 argument");
                            return Ty::Error;
                        }
                        let receiver = self.expr(base, Some(&U32));
                        let argument = self.expr(&arguments[0], Some(&U32));
                        if read_type(receiver) == U32 && read_type(argument) == U32 {
                            return U32;
                        }
                        self.error(7, expr.span, "bitwise methods require u32 operands");
                        return Ty::Error;
                    }
                    let access = match name.as_str() {
                        "borrow" => Some(IrAccess::Borrow),
                        "share" => Some(IrAccess::Share),
                        _ => None,
                    };
                    if let Some(access) = access {
                        return self.reference_conversion(expr, base, arguments, access, expected);
                    }
                    if name == "copy" {
                        return self.copy_conversion(expr, base, arguments);
                    }
                    if matches!(name.as_str(), "validate_utf8" | "to_utf8_string") {
                        return self.byte_utf8(expr, base, name, arguments);
                    }
                    if matches!(name.as_str(), "contains" | "index_of") {
                        return self.collection_search(expr, base, name, arguments);
                    }
                    if name == "get" {
                        return self.list_get(expr, base, arguments);
                    }
                    if matches!(name.as_str(), "push" | "pop" | "clear") {
                        return self.list_mutation(expr, base, name, arguments);
                    }
                    if name == "push_str" {
                        return self.string_push_str(expr, base, arguments);
                    }
                    if matches!(
                        name.as_str(),
                        "len" | "is_char_boundary" | "byte_at" | "scalar_at" | "concat"
                    ) {
                        return self.string_read(expr, base, name, arguments);
                    }
                    if self.extension_candidates.iter().any(|candidate| {
                        candidate.interface.is_none() && candidate.methods.contains_key(name)
                    }) {
                        self.allow_array_value(base);
                        let receiver = read_type(self.expr(base, None));
                        let available = self.extension_candidates.clone();
                        let mut matching = Vec::new();
                        for candidate in available.into_iter().filter(|candidate| {
                            candidate.interface.is_none() && candidate.methods.contains_key(name)
                        }) {
                            if candidate.target == receiver {
                                matching.push(candidate);
                            } else if let Some(candidate) =
                                self.specialize_inherent_candidate(&candidate, &receiver)
                            {
                                matching.push(candidate);
                            }
                        }
                        let applicable = matching
                            .iter()
                            .filter(|candidate| {
                                candidate.visible
                                    && (candidate.local
                                        || candidate.interface.is_some()
                                        || candidate.public_methods.contains(name))
                            })
                            .cloned()
                            .collect::<Vec<_>>();
                        if applicable.is_empty() && !matching.is_empty() {
                            self.error(
                                7,
                                expr.span,
                                "matching inherent extension is private or inactive",
                            );
                            return Ty::Error;
                        }
                        if applicable.is_empty() {
                            self.error(
                                7,
                                expr.span,
                                format!(
                                    "no visible inherent method '{}' for {}",
                                    name,
                                    self::name(&receiver)
                                ),
                            );
                            return Ty::Error;
                        }
                        if applicable.len() > 1 {
                            self.error(
                                7,
                                expr.span,
                                format!("ambiguous inherent method '{}'", name),
                            );
                            return Ty::Error;
                        }
                        let candidate = &applicable[0];
                        let (receiver_access, parameters, result, _, function) =
                            candidate.methods.get(name).cloned().unwrap();
                        if receiver_access == Access::Owned {
                            self.reject_extraction(base, &receiver);
                        }
                        if parameters.len() != arguments.len() {
                            self.error(
                                10,
                                expr.span,
                                format!(
                                    "expected {} method arguments, found {}",
                                    parameters.len(),
                                    arguments.len()
                                ),
                            );
                        }
                        for (argument, parameter) in arguments.iter().zip(&parameters) {
                            let actual = self.expr(argument, Some(&parameter.ty));
                            self.ensure(&actual, &parameter.ty, argument.span);
                        }
                        if let (Some(facts), Some(expression)) = (self.facts.as_mut(), id) {
                            let mut function_parameters = vec![FunctionParameter {
                                access: ir_access(receiver_access),
                                ty: candidate.target.clone(),
                            }];
                            function_parameters.extend(parameters.clone());
                            let signature = match ir_type(&Ty::Function(
                                function_parameters,
                                Box::new(result.clone()),
                            )) {
                                Some(IrType::Function(signature)) => signature,
                                _ => {
                                    self.error(
                                        7,
                                        expr.span,
                                        "inherent method signature is outside the executable type subset",
                                    );
                                    return Ty::Error;
                                }
                            };
                            facts.selected_calls.push(SelectedCall {
                                expression,
                                function,
                                receiver_access,
                                signature,
                            });
                        }
                        return result;
                    }
                }
                let ty = self.expr(callee, None);
                if let Ty::Function(params, result) = ty {
                    let direct = self.direct_callee(callee);
                    if params.len() != arguments.len() {
                        self.error(
                            10,
                            expr.span,
                            format!(
                                "expected {} arguments, found {}",
                                params.len(),
                                arguments.len()
                            ),
                        );
                    }
                    let mut diverges = false;
                    for (i, arg) in arguments.iter().enumerate() {
                        if params.get(i).is_some_and(|parameter| {
                            parameter.access == IrAccess::Owned
                                && matches!(
                                    parameter.ty,
                                    Ty::String
                                        | Ty::List(_)
                                        | Ty::Array(..)
                                        | Ty::Struct(..)
                                        | Ty::Tuple(..)
                                        | Ty::Enum(..)
                                )
                        }) {
                            // An owned aggregate parameter takes a literal, repetition,
                            // call result, `if` or named value moved into the call.
                            self.allow_array_value(arg);
                        }
                        let previous_concat = self.concat_destination;
                        let previous_borrow = self.temporary_borrow_argument;
                        if let Some(parameter) = params.get(i).filter(|_| direct) {
                            let argument = arg as *const Expr as usize;
                            match (&parameter.ty, parameter.access) {
                                (Ty::String, IrAccess::Owned) => {
                                    self.concat_destination = Some(argument)
                                }
                                (Ty::String | Ty::List(_), IrAccess::Borrow) => {
                                    self.temporary_borrow_argument = Some(argument)
                                }
                                _ => {}
                            }
                        }
                        let actual = self.expr(arg, params.get(i).map(|parameter| &parameter.ty));
                        self.concat_destination = previous_concat;
                        self.temporary_borrow_argument = previous_borrow;
                        if params.get(i).is_some_and(|parameter| {
                            parameter.access == IrAccess::Owned
                                && self.struct_has_unsupported_nested_string_owner(&parameter.ty)
                        }) {
                            self.error(
                                17,
                                arg.span,
                                "owned struct calls can transport only String-owning structs admitted by the transport rule (String, primitive and nested owner fields)",
                            );
                        }
                        if params.get(i).is_some_and(|parameter| {
                            parameter.access == IrAccess::Owned
                                && self.tuple_has_unsupported_nested_string_owner(&parameter.ty)
                        }) {
                            self.error(
                                17,
                                arg.span,
                                "owned tuple calls cannot transport nested String-owning aggregates other than tuples in this slice",
                            );
                        }
                        if let Some(parameter) = params
                            .get(i)
                            .filter(|parameter| matches!(parameter.ty, Ty::List(_)))
                        {
                            if !direct {
                                self.error(
                                    17,
                                    arg.span,
                                    "List arguments require a direct internal call",
                                );
                            } else if parameter.access == IrAccess::Owned
                                && !(matches!(&arg.kind, ExprKind::Path(path) if path.len() == 1 && self.lookup(&path[0]).is_some())
                                    || matches!(&arg.kind, ExprKind::Call { callee, .. } if self.direct_callee(callee)))
                            {
                                self.error(
                                    17,
                                    arg.span,
                                    "owned List arguments require a named whole local or a direct internal List call result",
                                );
                            }
                        }
                        if params
                            .get(i)
                            .is_none_or(|parameter| parameter.access == IrAccess::Owned)
                        {
                            self.reject_extraction(arg, &actual);
                        }
                        if let Some(param) = params.get(i) {
                            if param.access == IrAccess::Owned {
                                self.ensure(&actual, &param.ty, arg.span);
                            } else if matches!(&actual, Ty::Reference { inner, .. }
                                if !(compatible(inner, &param.ty)
                                    || direct && self.table.has_error_ancestor(inner, &param.ty)))
                            {
                                self.error(
                                    2,
                                    arg.span,
                                    format!(
                                        "expected {} {}, found {}",
                                        access_name(param.access),
                                        name(&param.ty),
                                        name(&actual)
                                    ),
                                );
                            } else if !reference_access_matches(&actual, param.access) {
                                self.error(
                                    17,
                                    arg.span,
                                    format!(
                                        "argument does not match the {} parameter access; use an explicit .borrow() or .share() conversion",
                                        access_name(param.access)
                                    ),
                                );
                            }
                        }
                        diverges |= actual == Ty::Never;
                    }
                    if diverges {
                        Ty::Never
                    } else {
                        *result
                    }
                } else {
                    for arg in arguments {
                        self.expr(arg, None);
                    }
                    if ty != Ty::Error {
                        self.error(11, callee.span, "expression is not callable");
                    }
                    Ty::Error
                }
            }
            ExprKind::Field {
                base,
                name: field_name,
            } => {
                let ty = self.field_read(base, field_name, expr);
                if matches!(ty, Ty::Error) {
                    self.failed_fields.insert(expr as *const Expr as usize);
                }
                ty
            }
            ExprKind::Struct {
                path,
                type_arguments,
                fields,
            } => {
                if path.is_empty() && type_arguments.is_empty() {
                    return self.anonymous_record(expr, fields, expected);
                }
                if self.lowering && !self.array_allowed(expr) {
                    self.error(
                        17,
                        expr.span,
                        "struct literals must be used as an owned value (binding initializer, assignment, argument, result or branch value); they cannot be a temporary or field base",
                    );
                }
                let literal_type = Type {
                    span: expr.span,
                    path: path.clone(),
                    arguments: type_arguments.clone(),
                };
                let target = self.type_path(&literal_type);
                let table = Rc::clone(&self.table);
                let info_storage = match &target {
                    Ty::Struct(id, _) | Ty::Tuple(id, _, _) => Some(table.info(*id)),
                    Ty::Error => None,
                    other => {
                        self.error(
                            23,
                            expr.span,
                            format!("'{}' is not a struct type", name(other)),
                        );
                        None
                    }
                };
                let info = info_storage.as_ref();
                if info.is_some_and(|info| info.bodyless) {
                    self.error(
                        23,
                        expr.span,
                        format!(
                            "bodyless nominal type '{}' cannot be constructed",
                            name(&target)
                        ),
                    );
                }
                let mut seen: Vec<&str> = Vec::new();
                // Field initialisers are checked (and later evaluated) in source order.
                for init in fields {
                    let declared = info
                        .and_then(|info| info.fields.iter().find(|field| field.name == init.name));
                    if let Some(info) = info {
                        if declared.is_none() {
                            self.error(
                                23,
                                init.span,
                                format!("struct '{}' has no field '{}'", info.name, init.name),
                            );
                        }
                    }
                    if seen.contains(&init.name.as_str()) {
                        self.error(
                            23,
                            init.span,
                            format!("field '{}' is initialised more than once", init.name),
                        );
                    }
                    seen.push(&init.name);
                    let expected_field = declared.map(|field| field.ty.clone());
                    // A field initialiser is an owned-value position, so a nested
                    // struct or array literal, a call or a named aggregate is moved in.
                    self.allow_array_value(&init.value);
                    let previous_concat = self.concat_destination;
                    if expected_field == Some(Ty::String) {
                        self.concat_destination = Some(&init.value as *const Expr as usize);
                    }
                    let actual = self.expr(&init.value, expected_field.as_ref());
                    self.concat_destination = previous_concat;
                    self.reject_extraction(&init.value, &actual);
                    if let Some(want) = &expected_field {
                        self.ensure(&actual, want, init.value.span);
                    }
                }
                if let Some(info) = info {
                    let missing: Vec<&str> = info
                        .fields
                        .iter()
                        .filter(|field| !seen.contains(&field.name.as_str()))
                        .map(|field| field.name.as_str())
                        .collect();
                    if !missing.is_empty() {
                        self.error(
                            23,
                            expr.span,
                            format!(
                                "missing field(s) in '{}' literal: {}",
                                info.name,
                                missing.join(", ")
                            ),
                        );
                    }
                    self.check_field_visibility(info, "construct", expr.span);
                }
                target
            }
            ExprKind::Block(block) => {
                let ty = self.block(block, expected).0;
                if matches!(ty, Ty::Reference { .. }) || self.table.is_borrow_option(&ty) {
                    self.error(
                        17,
                        expr.span,
                        "reference-valued block results are not supported",
                    );
                }
                ty
            }
            ExprKind::Match { scrutinee, arms } => {
                self.match_expr(expr, id, scrutinee, arms, expected)
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let cond = read_type(self.expr(condition, Some(&BOOL)));
                self.ensure(&cond, &BOOL, condition.span);
                let (then_ty, _) = self.block(then_branch, expected);
                if matches!(then_ty, Ty::Reference { .. }) || self.table.is_borrow_option(&then_ty)
                {
                    self.error(
                        17,
                        then_branch.span,
                        "reference-valued branch results are not supported",
                    );
                }
                if let Some(other) = else_branch {
                    let else_ty = self.expr(other, expected.or(Some(&then_ty)));
                    if matches!(else_ty, Ty::Reference { .. })
                        || self.table.is_borrow_option(&else_ty)
                    {
                        self.error(
                            17,
                            other.span,
                            "reference-valued branch results are not supported",
                        );
                    }
                    if cond == Ty::Never {
                        return Ty::Never;
                    }
                    if !compatible(&then_ty, &else_ty) {
                        self.error(
                            13,
                            other.span,
                            format!(
                                "if branches have incompatible types: {} and {}",
                                name(&then_ty),
                                name(&else_ty)
                            ),
                        );
                        Ty::Error
                    } else if then_ty == Ty::Never {
                        else_ty
                    } else {
                        then_ty
                    }
                } else {
                    self.ensure(&then_ty, &UNIT, then_branch.span);
                    if cond == Ty::Never {
                        Ty::Never
                    } else {
                        UNIT
                    }
                }
            }
        }
    }
}

/// Check primitive and fixed-array types in a standalone parsed module.
/// TE020 and TE021 belong to `check_control_flow`; ownership is not checked here.
/// A function with a non-Unit result must have a tail value or provable returns.
pub fn check_types(module: &Module) -> Vec<Diagnostic> {
    check_standalone(module, CheckMode::Types).0
}

/// Check a standalone module and retain canonical local and expression facts.
/// This returns no facts if type or control-flow diagnostics exist.
/// Unsupported array element storage, including references, reports TE017.
pub fn check_typed_module(module: &Module) -> Result<TypedModule, Vec<Diagnostic>> {
    let (mut diagnostics, functions, types) = check_standalone(module, CheckMode::Execution);
    diagnostics.extend(crate::check_control_flow(module));
    if diagnostics.is_empty() {
        Ok(TypedModule { functions, types })
    } else {
        Err(diagnostics)
    }
}

fn extension_candidates_for(
    caller: &str,
    project: &Project,
    resolution: &Resolution,
    table: &Rc<TypeTable>,
    extension_ids: &HashMap<(String, usize, String), FunctionId>,
) -> Vec<ExtensionCandidate> {
    let mut candidates = Vec::new();
    let direct_imports = resolution.module_imports.get(caller);
    let interface_declarations =
        resolution
            .all_extension_candidates()
            .into_iter()
            .map(|candidate| {
                (
                    candidate.module,
                    candidate.public,
                    candidate.span,
                    candidate.target,
                    Some(candidate.interface),
                    candidate.associated_types,
                    candidate.methods,
                    Vec::new(),
                    None,
                )
            });
    let inherent_declarations = resolution
        .all_inherent_extension_candidates()
        .into_iter()
        .map(|candidate| {
            let generic_target =
                (!candidate.generic_parameters.is_empty()).then(|| candidate.target.clone());
            (
                candidate.module,
                candidate.public,
                candidate.span,
                candidate.target,
                None,
                Vec::new(),
                candidate.methods,
                candidate.generic_parameters,
                generic_target,
            )
        });
    for (
        declaration_module,
        public,
        declaration_span,
        declaration_target,
        declaration_interface,
        declaration_associated_types,
        declaration_methods,
        generic_parameters,
        generic_target,
    ) in interface_declarations.chain(inherent_declarations)
    {
        let local = declaration_module == caller;
        let direct = direct_imports.is_some_and(|imports| imports.contains(&declaration_module));
        if !local && !direct {
            continue;
        }
        let Some(source) = resolution.modules.get(&declaration_module) else {
            continue;
        };
        let mut imports = HashMap::new();
        for item in &source.syntax.items {
            if let ItemKind::Use { path, alias, .. } = &item.kind {
                if path.len() == 1 && project.modules.iter().any(|module| module.name == path[0]) {
                    continue;
                }
                if let Some(local) = alias.as_ref().or(path.last()) {
                    imports.insert(local.clone(), path.join("::"));
                }
            }
        }
        for (alias, path) in &project.manifest.prelude {
            imports.entry(alias.clone()).or_insert_with(|| path.clone());
        }
        let mut checker = Checker {
            alloc: project.manifest.alloc(),
            module: declaration_module.clone(),
            table: Rc::clone(table),
            imports: imports.clone(),
            ..checker()
        };
        let target = if generic_target.is_some() {
            Ty::Error
        } else {
            checker.type_path(&declaration_target)
        };
        let interface = declaration_interface
            .as_ref()
            .map(|ty| qualified_interface(&declaration_module, &imports, ty));
        let public_methods = if interface.is_some() {
            declaration_methods
                .iter()
                .map(|method| method.name.clone())
                .collect()
        } else {
            declaration_methods
                .iter()
                .filter(|method| method.public)
                .map(|method| method.name.clone())
                .collect()
        };
        let methods = declaration_methods
            .iter()
            .map(|method| {
                if generic_target.is_some() {
                    return (
                        method.name.clone(),
                        (
                            method.receiver,
                            Vec::new(),
                            Ty::Error,
                            method.span,
                            extension_ids
                                .get(&(
                                    declaration_module.clone(),
                                    declaration_span.start,
                                    method.name.clone(),
                                ))
                                .copied()
                                .unwrap_or(FunctionId(0)),
                        ),
                    );
                }
                let parameters = method
                    .parameters
                    .iter()
                    .map(|parameter| FunctionParameter {
                        access: ir_access(parameter.access),
                        ty: checker.type_path(&parameter.ty),
                    })
                    .collect();
                let result = method
                    .result
                    .as_ref()
                    .map(|ty| checker.type_path(ty))
                    .unwrap_or(UNIT);
                (
                    method.name.clone(),
                    (
                        method.receiver,
                        parameters,
                        result,
                        method.span,
                        extension_ids
                            .get(&(
                                declaration_module.clone(),
                                declaration_span.start,
                                method.name.clone(),
                            ))
                            .copied()
                            .unwrap_or(FunctionId(0)),
                    ),
                )
            })
            .collect();
        let associated_types = declaration_associated_types
            .iter()
            .filter_map(|binding| {
                binding
                    .ty
                    .as_ref()
                    .map(|ty| (binding.name.clone(), checker.type_path(ty)))
            })
            .collect();
        candidates.push(ExtensionCandidate {
            module: declaration_module,
            span: declaration_span,
            visible: local || public,
            local,
            target,
            interface,
            associated_types,
            methods,
            public_methods,
            generic_target,
            generic_parameters,
            generic_methods: declaration_methods,
            declaration_imports: imports,
        });
    }
    candidates
}

fn imports_for_module(module: &Module, project: &Project) -> HashMap<String, String> {
    let mut imports = HashMap::new();
    for item in &module.items {
        if let ItemKind::Use { path, alias, .. } = &item.kind {
            if path.len() == 1
                && project
                    .modules
                    .iter()
                    .any(|candidate| candidate.name == path[0])
            {
                continue;
            }
            if let Some(local) = alias.as_ref().or(path.last()) {
                imports.insert(local.clone(), path.join("::"));
            }
        }
    }
    for (alias, path) in &project.manifest.prelude {
        imports.entry(alias.clone()).or_insert_with(|| path.clone());
    }
    imports
}

fn check_standalone(
    module: &Module,
    mode: CheckMode,
) -> (Vec<Diagnostic>, Vec<FunctionFacts>, Vec<TypeFact>) {
    let capture = mode != CheckMode::Types;
    let (table, table_diagnostics) = TypeTable::build(&[("", module)], HashMap::new());
    let mut c = Checker {
        alloc: true,
        diagnostics: table_diagnostics,
        lowering: capture,
        allowed_arrays: HashSet::new(),
        concat_destination: None,
        share_field_assignment: false,
        parameter_origins: HashSet::new(),
        temporary_borrow_argument: None,
        failed_fields: HashSet::new(),
        index_base: 0,
        module: String::new(),
        table: Rc::new(table),
        generic_types: HashMap::new(),
        generic_consts: HashMap::new(),
        generic_evidence: Vec::new(),
        generic_functions: HashMap::new(),
        specialization_registry: None,
        generic_path_targets: HashMap::new(),
        functions: HashMap::new(),
        function_ids: HashMap::new(),
        facts: None,
        qualified_functions: HashMap::new(),
        qualified_function_ids: HashMap::new(),
        imports: HashMap::new(),
        extension_candidates: Vec::new(),
        scopes: Vec::new(),
        result: UNIT,
    };
    let mut next_function = 0u32;
    for item in &module.items {
        match &item.kind {
            ItemKind::Function {
                external,
                name,
                parameters,
                result,
                ..
            } => {
                if *external {
                    c.error(
                        15,
                        item.span,
                        "external functions require project host-profile validation",
                    );
                }
                c.function_ids
                    .insert(name.clone(), FunctionId(next_function));
                next_function += 1;
                let params = parameters
                    .iter()
                    .map(|p| FunctionParameter {
                        access: ir_access(p.access),
                        ty: c.type_path(&p.ty),
                    })
                    .collect();
                let result = result.as_ref().map(|t| c.type_path(t)).unwrap_or(UNIT);
                if c.functions
                    .insert(name.clone(), Ty::Function(params, Box::new(result)))
                    .is_some()
                {
                    c.error(14, item.span, format!("duplicate function '{name}'"));
                }
            }
            // Standalone mode has no module loader; the virtual `alloc` module
            // is the only import it can satisfy.
            ItemKind::Use { path, .. }
                if path.first().is_some_and(|head| head == "alloc")
                    && c.alloc
                    && matches!(path.as_slice(), [_] | [_, _]) => {}
            ItemKind::Use { .. } => c.error(15, item.span, "imports require module resolution"),
            ItemKind::Type { .. }
            | ItemKind::Interface { .. }
            | ItemKind::Extension { .. }
            | ItemKind::InherentExtension { .. } => {}
        }
    }
    let mut functions = Vec::new();
    for item in &module.items {
        if let ItemKind::Function {
            name,
            parameters,
            body,
            ..
        } = &item.kind
        {
            let Ty::Function(params, result) = c.functions.get(name).cloned().unwrap() else {
                unreachable!()
            };
            if capture {
                c.facts = Some(FunctionFacts {
                    id: c.function_ids[name],
                    span: item.span,
                    source_module: String::new(),
                    source_name: name.clone(),
                    specialization_key: None,
                    signature: match ir_type(&Ty::Function(params.clone(), result.clone())) {
                        Some(IrType::Function(signature)) => signature,
                        _ => Signature {
                            parameters: Vec::new(),
                            result: Box::new(IrType::Primitive(Primitive::Unit)),
                        },
                    },
                    locals: Vec::new(),
                    expressions: Vec::new(),
                    path_uses: Vec::new(),
                    variant_uses: Vec::new(),
                    explicit_drops: Vec::new(),
                    explicit_asserts: Vec::new(),
                    explicit_replaces: Vec::new(),
                    explicit_swaps: Vec::new(),
                    selected_calls: Vec::new(),
                    selected_operators: Vec::new(),
                    selected_assignments: Vec::new(),
                    matches: Vec::new(),
                    tuple_projections: Vec::new(),
                    tuple_initializers: Vec::new(),
                    next_expr: 0,
                });
            }
            check_function_body(&mut c, parameters, body, params, *result);
            if let Some(facts) = c.facts.take() {
                functions.push(facts);
            }
        }
    }
    let types = if capture {
        type_facts(&c.table)
    } else {
        Vec::new()
    };
    (c.diagnostics, functions, types)
}
fn check_function_body(
    c: &mut Checker,
    parameters: &[Parameter],
    body: &Block,
    params: Vec<FunctionParameter>,
    result: Ty,
) {
    let previous_parameter_origins = std::mem::take(&mut c.parameter_origins);
    c.result = result;
    c.scopes.push(HashMap::new());
    for (p, parameter) in parameters.iter().zip(params) {
        bind_parameter(c, p, parameter.ty);
    }
    if let Some(tail) = &body.tail {
        c.allow_array_value(tail);
    }
    let (tail, returns) = c.block(body, Some(&c.result.clone()));
    if !returns {
        c.ensure(
            &tail,
            &c.result.clone(),
            body.tail.as_deref().map_or(body.span, |e| e.span),
        );
    }
    c.scopes.pop();
    c.parameter_origins = previous_parameter_origins;
}

/// Check primitive and fixed-array types in the modules loaded by `resolve`.
///
/// Call this only after resolution succeeds. An invalid resolution returns no
/// type diagnostics, leaving its parse/name/module diagnostics to the caller.
/// The pass checks functions and their calls, including imports and prelude
/// aliases; user-defined types, ownership, and other semantics remain outside
/// this primitive pass. Every diagnostic keeps a span from the original AST.
pub fn check_resolved_types(project: &Project, resolution: &Resolution) -> Vec<Diagnostic> {
    if !resolution.diagnostics.is_empty() {
        return Vec::new();
    }
    check_resolved_mode(project, resolution, CheckMode::Types)
        .err()
        .unwrap_or_default()
        .into_iter()
        .filter(|diagnostic| !matches!(diagnostic.code.to_string().as_str(), "TE020" | "TE021"))
        .collect()
}

fn install_function_environment(
    checker: &mut Checker,
    module_name: &str,
    syntax: &Module,
    project: &Project,
    generic_templates: &HashMap<String, GenericFunctionTemplate>,
    signatures: &HashMap<String, Ty>,
    ids: &HashMap<String, FunctionId>,
) {
    for item in &syntax.items {
        match &item.kind {
            ItemKind::Function {
                name,
                generic_parameters,
                ..
            } => {
                let key = format!("{module_name}::{name}");
                if !generic_parameters.is_empty() {
                    if let Some(template) = generic_templates.get(&key) {
                        checker
                            .generic_functions
                            .insert(name.clone(), template.clone());
                    }
                }
                if let Some(signature) = signatures.get(&key) {
                    checker.functions.insert(name.clone(), signature.clone());
                    checker.function_ids.insert(name.clone(), ids[&key]);
                }
            }
            ItemKind::Use { path, alias, .. } => {
                let module_only = path.len() == 1
                    && project
                        .modules
                        .iter()
                        .any(|candidate| candidate.name == path[0]);
                if !module_only {
                    if let Some(local) = alias.as_ref().or(path.last()) {
                        checker.imports.insert(local.clone(), path.join("::"));
                    }
                }
            }
            ItemKind::Type { .. }
            | ItemKind::Interface { .. }
            | ItemKind::Extension { .. }
            | ItemKind::InherentExtension { .. } => {}
        }
    }
    for (alias, path) in &project.manifest.prelude {
        checker
            .imports
            .entry(alias.clone())
            .or_insert_with(|| path.clone());
    }
    for (alias, path) in &checker.imports {
        let key = path.strip_prefix("self::").unwrap_or(path);
        if let Some(template) = generic_templates.get(key) {
            checker
                .generic_functions
                .insert(alias.clone(), template.clone());
        }
        if let Some(signature) = signatures.get(key) {
            checker.functions.insert(alias.clone(), signature.clone());
            if let Some(id) = ids.get(key) {
                checker.function_ids.insert(alias.clone(), *id);
            }
        }
    }
}

pub(crate) fn check_resolved_mode(
    project: &Project,
    resolution: &Resolution,
    mode: CheckMode,
) -> Result<TypedModule, Vec<Diagnostic>> {
    let lowering = mode != CheckMode::Types;
    if !resolution.diagnostics.is_empty() {
        return Err(resolution.diagnostics.clone());
    }
    let mut diagnostics = Vec::new();
    let mut module_imports: HashMap<String, HashMap<String, String>> = HashMap::new();
    for (module_name, source) in &resolution.modules {
        let imports = module_imports.entry(module_name.clone()).or_default();
        for item in &source.syntax.items {
            if let ItemKind::Use { path, alias, .. } = &item.kind {
                if path.len() == 1
                    && project
                        .modules
                        .iter()
                        .any(|candidate| candidate.name == path[0])
                {
                    continue;
                }
                if let Some(local) = alias.as_ref().or(path.last()) {
                    imports.insert(local.clone(), path.join("::"));
                }
            }
        }
        for (alias, path) in &project.manifest.prelude {
            imports.entry(alias.clone()).or_insert_with(|| path.clone());
        }
    }
    let modules: Vec<(&str, &Module)> = resolution
        .modules
        .iter()
        .map(|(name, source)| (name.as_str(), &source.syntax))
        .collect();
    let (table, table_diagnostics) = TypeTable::build(&modules, module_imports);
    let table = Rc::new(table);
    diagnostics.extend(table_diagnostics);
    let mut generic_templates = HashMap::new();
    for (module_name, source) in &resolution.modules {
        for item in &source.syntax.items {
            if let ItemKind::Function {
                name,
                generic_parameters,
                bounds,
                parameters,
                result,
                ..
            } = &item.kind
            {
                if !generic_parameters.is_empty() {
                    let imports = imports_for_module(&source.syntax, project);
                    let bound_interfaces = bounds
                        .iter()
                        .map(|bound| qualified_interface(module_name, &imports, &bound.interface))
                        .collect();
                    generic_templates.insert(
                        format!("{module_name}::{name}"),
                        GenericFunctionTemplate {
                            module: module_name.clone(),
                            name: name.clone(),
                            span: item.span,
                            generic_parameters: generic_parameters.clone(),
                            bounds: bounds.clone(),
                            bound_interfaces,
                            parameters: parameters.clone(),
                            result: result.clone(),
                        },
                    );
                }
            }
        }
    }
    for template in generic_templates.values() {
        if !supported_generic_function(template) {
            diagnostics.push(diagnostic(
                7,
                template.span,
                format!(
                    "generic function '{}::{}' is outside the supported unconstrained direct-type-parameter specialization subset",
                    template.module, template.name
                ),
            ));
        }
    }
    let mut ids = HashMap::new();
    let mut next_id = 0;
    for (module_name, source) in &resolution.modules {
        for item in &source.syntax.items {
            if let ItemKind::Function {
                name,
                generic_parameters,
                ..
            } = &item.kind
            {
                if generic_parameters.is_empty() {
                    ids.insert(format!("{module_name}::{name}"), FunctionId(next_id));
                    next_id += 1;
                }
            }
        }
    }
    let mut extension_ids = HashMap::new();
    for (module_name, source) in &resolution.modules {
        for item in &source.syntax.items {
            let methods = match &item.kind {
                ItemKind::Extension { methods, .. } => Some(methods),
                ItemKind::InherentExtension {
                    methods,
                    generic_parameters,
                    ..
                } if generic_parameters.is_empty() => Some(methods),
                _ => None,
            };
            if let Some(methods) = methods {
                for method in methods {
                    extension_ids.insert(
                        (module_name.clone(), item.span.start, method.name.clone()),
                        FunctionId(next_id),
                    );
                    next_id += 1;
                }
            }
        }
    }
    let specialization_registry = Rc::new(RefCell::new(SpecializationRegistry {
        next_id,
        ..SpecializationRegistry::default()
    }));
    let mut signatures = HashMap::new();
    for (module_name, source) in &resolution.modules {
        let mut c = Checker {
            alloc: project.manifest.alloc(),
            lowering,
            module: module_name.clone(),
            table: Rc::clone(&table),
            ..checker()
        };
        for item in &source.syntax.items {
            match &item.kind {
                ItemKind::Function {
                    name,
                    generic_parameters,
                    parameters,
                    result,
                    ..
                } => {
                    if !generic_parameters.is_empty() {
                        continue;
                    }
                    let params = parameters
                        .iter()
                        .map(|p| FunctionParameter {
                            access: ir_access(p.access),
                            ty: c.type_path(&p.ty),
                        })
                        .collect();
                    let result = result.as_ref().map(|t| c.type_path(t)).unwrap_or(UNIT);
                    signatures.insert(
                        format!("{module_name}::{name}"),
                        Ty::Function(params, Box::new(result)),
                    );
                }
                ItemKind::Type { .. }
                | ItemKind::Use { .. }
                | ItemKind::Interface { .. }
                | ItemKind::Extension { .. }
                | ItemKind::InherentExtension { .. } => {}
            }
        }
        diagnostics.extend(c.diagnostics);
        diagnostics.extend(crate::check_control_flow(&source.syntax));
    }
    let mut all_facts = Vec::with_capacity(next_id as usize);
    for (module_name, source) in &resolution.modules {
        let mut c = Checker {
            alloc: project.manifest.alloc(),
            lowering,
            module: module_name.clone(),
            table: Rc::clone(&table),
            generic_functions: generic_templates.clone(),
            specialization_registry: Some(Rc::clone(&specialization_registry)),
            extension_candidates: extension_candidates_for(
                module_name,
                project,
                resolution,
                &table,
                &extension_ids,
            ),
            qualified_functions: signatures.clone(),
            qualified_function_ids: ids.clone(),
            ..checker()
        };
        install_function_environment(
            &mut c,
            module_name,
            &source.syntax,
            project,
            &generic_templates,
            &signatures,
            &ids,
        );
        for item in &source.syntax.items {
            if let ItemKind::Function {
                name,
                parameters,
                body,
                ..
            } = &item.kind
            {
                let key = format!("{module_name}::{name}");
                if let (Some(Ty::Function(params, result)), Some(id)) =
                    (signatures.get(&key), ids.get(&key))
                {
                    let ir_signature = if lowering {
                        ir_type(&Ty::Function(params.clone(), result.clone()))
                    } else {
                        None
                    };
                    if let Some(IrType::Function(signature)) = ir_signature {
                        c.facts = Some(FunctionFacts {
                            id: *id,
                            span: item.span,
                            source_module: module_name.clone(),
                            source_name: name.clone(),
                            specialization_key: None,
                            signature,
                            locals: Vec::new(),
                            expressions: Vec::new(),
                            path_uses: Vec::new(),
                            variant_uses: Vec::new(),
                            explicit_drops: Vec::new(),
                            explicit_asserts: Vec::new(),
                            explicit_replaces: Vec::new(),
                            explicit_swaps: Vec::new(),
                            selected_calls: Vec::new(),
                            selected_operators: Vec::new(),
                            selected_assignments: Vec::new(),
                            matches: Vec::new(),
                            tuple_projections: Vec::new(),
                            tuple_initializers: Vec::new(),
                            next_expr: 0,
                        });
                    }
                    check_function_body(&mut c, parameters, body, params.clone(), *result.clone());
                    if let Some(facts) = c.facts.take() {
                        all_facts.push(facts);
                    }
                }
            }
        }
        for item in &source.syntax.items {
            if matches!(&item.kind, ItemKind::InherentExtension { generic_parameters, .. } if !generic_parameters.is_empty())
            {
                continue;
            }
            let (target, methods) = match &item.kind {
                ItemKind::Extension {
                    target, methods, ..
                }
                | ItemKind::InherentExtension {
                    target, methods, ..
                } => (target, methods),
                _ => continue,
            };
            let target_ty = c.type_path(target);
            for method in methods {
                let Some(body) = &method.body else {
                    continue;
                };
                let function =
                    extension_ids[&(module_name.clone(), item.span.start, method.name.clone())];
                let mut parameters = vec![Parameter {
                    span: method.span,
                    mutable: false,
                    name: "self".to_owned(),
                    access: method.receiver,
                    ty: target.clone(),
                }];
                parameters.extend(method.parameters.iter().cloned());
                let params = parameters
                    .iter()
                    .map(|parameter| FunctionParameter {
                        access: ir_access(parameter.access),
                        ty: if parameter.name == "self" {
                            target_ty.clone()
                        } else {
                            c.type_path(&parameter.ty)
                        },
                    })
                    .collect::<Vec<_>>();
                let result = method
                    .result
                    .as_ref()
                    .map(|ty| c.type_path(ty))
                    .unwrap_or(UNIT);
                if lowering {
                    if let Some(IrType::Function(signature)) =
                        ir_type(&Ty::Function(params.clone(), Box::new(result.clone())))
                    {
                        c.facts = Some(FunctionFacts {
                            id: function,
                            span: method.span,
                            source_module: module_name.clone(),
                            source_name: method.name.clone(),
                            specialization_key: None,
                            signature,
                            locals: Vec::new(),
                            expressions: Vec::new(),
                            path_uses: Vec::new(),
                            variant_uses: Vec::new(),
                            explicit_drops: Vec::new(),
                            explicit_asserts: Vec::new(),
                            explicit_replaces: Vec::new(),
                            explicit_swaps: Vec::new(),
                            selected_calls: Vec::new(),
                            selected_operators: Vec::new(),
                            selected_assignments: Vec::new(),
                            matches: Vec::new(),
                            tuple_projections: Vec::new(),
                            tuple_initializers: Vec::new(),
                            next_expr: 0,
                        });
                    }
                }
                check_function_body(&mut c, &parameters, body, params, result);
                if let Some(facts) = c.facts.take() {
                    all_facts.push(facts);
                }
            }
        }
        diagnostics.extend(c.diagnostics);
    }
    let mut specialization_index = 0usize;
    let mut method_index = 0usize;
    let mut generic_limit_reported = false;
    let mut method_limit_reported = false;
    loop {
        let mut made_progress = false;
        loop {
            let request = specialization_registry
                .borrow()
                .requests
                .get(specialization_index)
                .cloned();
            let Some(request) = request else {
                break;
            };
            if specialization_index >= 256 {
                if !generic_limit_reported {
                    diagnostics.push(diagnostic(
                        7,
                        request.template.span,
                        "generic specialization limit exceeded (maximum 256 distinct functions)",
                    ));
                    generic_limit_reported = true;
                }
                specialization_index += 1;
                continue;
            }
            specialization_index += 1;
            made_progress = true;
            let Some(source) = resolution.modules.get(&request.template.module) else {
                diagnostics.push(diagnostic(
                    7,
                    request.template.span,
                    "generic specialization source module is unavailable",
                ));
                continue;
            };
            let Some(item) = source
                .syntax
                .items
                .iter()
                .find(|item| item.span == request.template.span)
            else {
                diagnostics.push(diagnostic(
                    7,
                    request.template.span,
                    "generic specialization source declaration is unavailable",
                ));
                continue;
            };
            let ItemKind::Function {
                parameters, body, ..
            } = &item.kind
            else {
                unreachable!("generic template points to a function item")
            };
            let mut c = Checker {
                alloc: project.manifest.alloc(),
                lowering,
                module: request.template.module.clone(),
                table: Rc::clone(&table),
                generic_types: request.substitution.clone(),
                generic_consts: request.const_substitution.clone(),
                generic_evidence: request.evidence.clone(),
                generic_functions: generic_templates.clone(),
                specialization_registry: Some(Rc::clone(&specialization_registry)),
                extension_candidates: extension_candidates_for(
                    &request.template.module,
                    project,
                    resolution,
                    &table,
                    &extension_ids,
                ),
                qualified_functions: signatures.clone(),
                qualified_function_ids: ids.clone(),
                ..checker()
            };
            install_function_environment(
                &mut c,
                &request.template.module,
                &source.syntax,
                project,
                &generic_templates,
                &signatures,
                &ids,
            );
            let params = parameters
                .iter()
                .map(|parameter| FunctionParameter {
                    access: ir_access(parameter.access),
                    ty: c.type_path(&parameter.ty),
                })
                .collect::<Vec<_>>();
            let result = request
                .template
                .result
                .as_ref()
                .map(|ty| c.type_path(ty))
                .unwrap_or(UNIT);
            if lowering {
                c.facts = Some(FunctionFacts {
                    id: request.id,
                    span: request.template.span,
                    source_module: request.template.module.clone(),
                    source_name: request.template.name.clone(),
                    specialization_key: Some(request.key.clone()),
                    signature: request.signature,
                    locals: Vec::new(),
                    expressions: Vec::new(),
                    path_uses: Vec::new(),
                    variant_uses: Vec::new(),
                    explicit_drops: Vec::new(),
                    explicit_asserts: Vec::new(),
                    explicit_replaces: Vec::new(),
                    explicit_swaps: Vec::new(),
                    selected_calls: Vec::new(),
                    selected_operators: Vec::new(),
                    selected_assignments: Vec::new(),
                    matches: Vec::new(),
                    tuple_projections: Vec::new(),
                    tuple_initializers: Vec::new(),
                    next_expr: 0,
                });
            }
            check_function_body(&mut c, parameters, body, params, result);
            if let Some(facts) = c.facts.take() {
                all_facts.push(facts);
            }
            diagnostics.extend(c.diagnostics);
        }
        loop {
            let request = specialization_registry
                .borrow()
                .method_requests
                .get(method_index)
                .cloned();
            let Some(request) = request else {
                break;
            };
            if method_index >= 256 {
                if !method_limit_reported {
                    diagnostics.push(diagnostic(
                        7,
                        request.method.span,
                        "generic inherent method specialization limit exceeded (maximum 256 distinct methods)",
                    ));
                    method_limit_reported = true;
                }
                method_index += 1;
                continue;
            }
            method_index += 1;
            made_progress = true;
            let Some(source) = resolution.modules.get(&request.module) else {
                diagnostics.push(diagnostic(
                    7,
                    request.method.span,
                    "generic inherent method module is unavailable",
                ));
                continue;
            };
            let Some(extension) = source
                .syntax
                .items
                .iter()
                .find(|item| item.span == request.extension_span)
            else {
                diagnostics.push(diagnostic(
                    7,
                    request.method.span,
                    "generic inherent extension source is unavailable",
                ));
                continue;
            };
            let method = match &extension.kind {
                ItemKind::InherentExtension { methods, .. } => methods.iter().find(|method| {
                    method.span == request.method.span && method.name == request.method.name
                }),
                _ => None,
            };
            let Some(method) = method else {
                diagnostics.push(diagnostic(
                    7,
                    request.method.span,
                    "generic inherent method source is unavailable",
                ));
                continue;
            };
            let mut parameters = vec![Parameter {
                span: method.span,
                mutable: false,
                name: "self".to_owned(),
                access: method.receiver,
                ty: Type {
                    span: method.span,
                    path: vec!["Self".into()],
                    arguments: Vec::new(),
                },
            }];
            parameters.extend(method.parameters.iter().cloned());
            let mut c = Checker {
                alloc: project.manifest.alloc(),
                lowering,
                module: request.module.clone(),
                table: Rc::clone(&table),
                generic_types: request.substitution.clone(),
                generic_consts: request.const_substitution.clone(),
                generic_functions: generic_templates.clone(),
                specialization_registry: Some(Rc::clone(&specialization_registry)),
                extension_candidates: extension_candidates_for(
                    &request.module,
                    project,
                    resolution,
                    &table,
                    &extension_ids,
                ),
                qualified_functions: signatures.clone(),
                qualified_function_ids: ids.clone(),
                ..checker()
            };
            install_function_environment(
                &mut c,
                &request.module,
                &source.syntax,
                project,
                &generic_templates,
                &signatures,
                &ids,
            );
            let mut parameter_types = vec![FunctionParameter {
                access: ir_access(method.receiver),
                ty: request.target.clone(),
            }];
            parameter_types.extend(method.parameters.iter().map(|parameter| FunctionParameter {
                access: ir_access(parameter.access),
                ty: c.type_path(&parameter.ty),
            }));
            let result = method
                .result
                .as_ref()
                .map(|ty| c.type_path(ty))
                .unwrap_or(UNIT);
            if lowering {
                if let Some(IrType::Function(signature)) = ir_type(&Ty::Function(
                    parameter_types.clone(),
                    Box::new(result.clone()),
                )) {
                    c.facts = Some(FunctionFacts {
                        id: request.id,
                        span: method.span,
                        source_module: request.module.clone(),
                        source_name: method.name.clone(),
                        specialization_key: Some(request.key.clone()),
                        signature,
                        locals: Vec::new(),
                        expressions: Vec::new(),
                        path_uses: Vec::new(),
                        variant_uses: Vec::new(),
                        explicit_drops: Vec::new(),
                        explicit_asserts: Vec::new(),
                        explicit_replaces: Vec::new(),
                        explicit_swaps: Vec::new(),
                        selected_calls: Vec::new(),
                        selected_operators: Vec::new(),
                        selected_assignments: Vec::new(),
                        matches: Vec::new(),
                        tuple_projections: Vec::new(),
                        tuple_initializers: Vec::new(),
                        next_expr: 0,
                    });
                }
            }
            if let Some(body) = &method.body {
                check_function_body(&mut c, &parameters, body, parameter_types, result);
            }
            if let Some(facts) = c.facts.take() {
                all_facts.push(facts);
            }
            diagnostics.extend(c.diagnostics);
        }
        if !made_progress {
            break;
        }
    }
    if diagnostics.is_empty() {
        all_facts.sort_by_key(|facts| facts.id.0);
        Ok(TypedModule {
            functions: all_facts,
            types: if lowering {
                type_facts(&table)
            } else {
                Vec::new()
            },
        })
    } else {
        Err(diagnostics)
    }
}

fn checker() -> Checker {
    Checker {
        alloc: true,
        diagnostics: Vec::new(),
        lowering: true,
        allowed_arrays: HashSet::new(),
        concat_destination: None,
        share_field_assignment: false,
        parameter_origins: HashSet::new(),
        temporary_borrow_argument: None,
        failed_fields: HashSet::new(),
        index_base: 0,
        module: String::new(),
        table: Rc::new(TypeTable::empty()),
        generic_types: HashMap::new(),
        generic_consts: HashMap::new(),
        generic_evidence: Vec::new(),
        generic_functions: HashMap::new(),
        specialization_registry: None,
        generic_path_targets: HashMap::new(),
        functions: HashMap::new(),
        function_ids: HashMap::new(),
        facts: None,
        qualified_functions: HashMap::new(),
        qualified_function_ids: HashMap::new(),
        imports: HashMap::new(),
        extension_candidates: Vec::new(),
        scopes: Vec::new(),
        result: UNIT,
    }
}

/// Bind a direct, unconstrained type parameter from an already checked
/// argument. The argument's `Ty` is the source of truth (so aliases and
/// literal defaulting have already been resolved by expression checking).
/// This first inference primitive intentionally rejects compound parameter
/// patterns; those require recursive semantic substitution and remain gated.
fn infer_direct_type_parameter(
    generic_parameters: &HashSet<String>,
    written: &Type,
    actual: &Ty,
    substitutions: &mut HashMap<String, Ty>,
) -> Result<(), ()> {
    if written.path.len() != 1
        || !written.arguments.is_empty()
        || !generic_parameters.contains(&written.path[0])
        || matches!(actual, Ty::Error | Ty::Never)
    {
        return Err(());
    }
    match substitutions.get(&written.path[0]) {
        Some(previous) if previous != actual => Err(()),
        Some(_) => Ok(()),
        None => {
            substitutions.insert(written.path[0].clone(), actual.clone());
            Ok(())
        }
    }
}
fn bind_parameter(c: &mut Checker, p: &Parameter, ty: Ty) {
    if p.mutable && p.access != Access::Owned {
        c.error(
            17,
            p.span,
            "borrow/share parameters cannot be rebound; remove the var modifier",
        );
    }
    let access = ir_access(p.access);
    let origin = p as *const _ as usize;
    c.parameter_origins.insert(origin);
    let local_ty = match access {
        IrAccess::Owned => ty.clone(),
        _ => Ty::Reference {
            access,
            inner: Box::new(ty.clone()),
            origin: ReferenceOrigin::Binding(origin),
        },
    };
    let id = c.register_local(
        &p.name,
        &local_ty,
        p.access == Access::Owned && p.mutable,
        access,
        p.span,
        origin,
    );
    if c.scopes
        .last_mut()
        .unwrap()
        .insert(
            p.name.clone(),
            Binding {
                ty: local_ty,
                mutable: p.access == Access::Owned && p.mutable,
                access,
                id,
                origin: p as *const _ as usize,
            },
        )
        .is_some()
    {
        c.error(3, p.span, format!("duplicate parameter '{}'", p.name));
    }
}

#[cfg(test)]
mod access_tests {
    use super::*;
    use memobits_diagnostics::SourceId;
    use memobits_syntax::{parse, StatementKind};

    #[test]
    fn generic_parameter_inference_uses_semantic_types_and_rejects_conflicts() {
        let parameter = Type {
            span: Span {
                source: SourceId(0),
                start: 0,
                end: 1,
            },
            path: vec!["T".to_owned()],
            arguments: Vec::new(),
        };
        let generics = HashSet::from(["T".to_owned()]);
        let mut substitutions = HashMap::new();
        assert!(infer_direct_type_parameter(
            &generics,
            &parameter,
            &Ty::Primitive("i32"),
            &mut substitutions,
        )
        .is_ok());
        assert_eq!(substitutions.get("T"), Some(&Ty::Primitive("i32")));
        assert!(infer_direct_type_parameter(
            &generics,
            &parameter,
            &Ty::Primitive("u32"),
            &mut substitutions,
        )
        .is_err());
        assert!(infer_direct_type_parameter(
            &generics,
            &parameter,
            &Ty::Error,
            &mut HashMap::new(),
        )
        .is_err());
    }

    #[test]
    fn generic_body_type_resolution_uses_concrete_semantic_substitutions() {
        let parameter = Type {
            span: Span {
                source: SourceId(0),
                start: 0,
                end: 1,
            },
            path: vec!["T".to_owned()],
            arguments: Vec::new(),
        };
        let mut checker = checker();
        checker
            .generic_types
            .insert("T".to_owned(), Ty::Primitive("u32"));
        assert_eq!(checker.type_path(&parameter), Ty::Primitive("u32"));
        assert!(checker.diagnostics.is_empty());
    }

    #[test]
    fn internal_function_types_preserve_non_owned_access_metadata() {
        let ty = Ty::Function(
            vec![FunctionParameter {
                access: IrAccess::Share,
                ty: I32,
            }],
            Box::new(UNIT.clone()),
        );
        let Some(IrType::Function(signature)) = ir_type(&ty) else {
            panic!("function type should lower");
        };
        assert_eq!(signature.parameters[0].access, IrAccess::Share);
    }

    #[test]
    fn reference_conversions_keep_ir_type_and_origin_separate() {
        let parsed = parse(
            SourceId(0),
            "fn f(var owner: i32) { let view := owner.borrow(); }",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
            panic!("expected function")
        };
        let StatementKind::Binding { value, .. } = &body.statements[0].kind else {
            panic!("expected reference binding")
        };

        let mut checker = checker();
        checker.scopes.push(HashMap::from([(
            "owner".to_owned(),
            Binding {
                ty: I32,
                mutable: true,
                access: IrAccess::Owned,
                id: Some(LocalId(0)),
                origin: 42,
            },
        )]));
        let ty = checker.expr(value, None);
        assert!(matches!(
            &ty,
            Ty::Reference {
                access: IrAccess::Borrow,
                inner,
                origin: ReferenceOrigin::Binding(42),
            } if inner.as_ref() == &I32
        ));
        assert!(checker.diagnostics.is_empty(), "{:?}", checker.diagnostics);
        assert!(matches!(
            ir_type(&ty),
            Some(IrType::Reference {
                access: IrAccess::Borrow,
                inner,
            }) if *inner == IrType::Primitive(Primitive::I32)
        ));

        let another_owner = Ty::Reference {
            access: IrAccess::Borrow,
            inner: Box::new(I32),
            origin: ReferenceOrigin::Binding(7),
        };
        assert!(compatible(&ty, &another_owner));
    }

    #[test]
    fn share_conversion_checks_mutability_and_conversion_arity() {
        let immutable = parse(SourceId(1), "fn f(owner: i32) { let r := owner.share(); }");
        let immutable_diagnostics = check_types(&immutable.module);
        assert!(immutable_diagnostics.iter().any(|diagnostic| {
            diagnostic.code.to_string() == "TE017"
                && diagnostic
                    .message
                    .contains("requires a mutable local owner")
        }));

        let wrong_arity = parse(
            SourceId(2),
            "fn f(var owner: i32) { let r := owner.borrow(1); }",
        );
        let arity_diagnostics = check_types(&wrong_arity.module);
        assert!(arity_diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("borrow() conversion takes no arguments")
        }));
    }

    #[test]
    fn call_access_matching_distinguishes_borrow_and_share() {
        let parsed = parse(
            SourceId(3),
            "fn inspect(value: borrow i32) {} fn mutate(value: share i32) {} fn caller(var owner: i32) { inspect(owner.share()); mutate(owner.borrow()); }",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let diagnostics = check_types(&parsed.module);
        assert!(diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("does not match the share parameter access")
        }));
        assert!(!diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("does not match the borrow parameter access")
        }));
    }

    #[test]
    fn share_parameter_mutation_is_not_parameter_rebinding() {
        let parsed = parse(
            SourceId(4),
            "fn increment(value: share i32) { value += 1; }",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let diagnostics = check_types(&parsed.module);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert!(!diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("cannot assign to immutable binding")
        }));
    }

    #[test]
    fn primitive_reference_conversions_produce_typed_facts() {
        let parsed = parse(
            SourceId(5),
            "fn f(var owner: i32) -> i32 { let view := owner.borrow(); view + 1 }",
        );
        assert!(check_typed_module(&parsed.module).is_ok());
    }
}

/// Adapter feeding the analysis type table to the shared `memobits_ir`
/// transport rule.
struct TyOwnerModel<'t>(&'t TypeTable);

impl memobits_ir::OwnerTypeModel for TyOwnerModel<'_> {
    type Ty = Ty;
    fn view<'a>(&self, ty: &'a Ty) -> memobits_ir::OwnerTyView<'a, Ty> {
        use memobits_ir::OwnerTyView as View;
        match ty {
            Ty::String => View::String,
            Ty::Primitive(_) => View::Primitive,
            Ty::Struct(id, _) => View::Struct(*id),
            Ty::Array(element, len) => View::Array {
                element,
                nonempty: *len != 0,
            },
            _ => View::Other,
        }
    }
    fn nominal_struct(&self, id: u32) -> Option<memobits_ir::OwnerStructDef<Ty>> {
        let info = self.0.info(id);
        if info.module == "\0tuple" {
            return None;
        }
        Some(memobits_ir::OwnerStructDef {
            has_error_ancestry: self.0.error_ancestry(id).is_some(),
            fields: info.fields.iter().map(|field| field.ty.clone()).collect(),
        })
    }
}
