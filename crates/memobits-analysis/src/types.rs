//! Type checks for primitives and fixed arrays. Executable IR supports arrays of primitive
//! elements and nested arrays (literal, repetition, indexing, element, row and whole-array
//! assignment, array parameters, results and `if`/block results); every other array form is
//! gated with TE017.
//! Name resolution across modules and ownership checking are separate passes.
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
    Access, Block, Expr, ExprKind, FieldPattern, ItemKind, MatchArm, Module, Parameter,
    PatternKind, Statement, StatementKind, Type,
};

mod templates;
mod typetable;
use memobits_syntax::templates::{self as registry, Template};
use templates::ResolvedArgument;
use typetable::{StructInfo, TypeTable};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum CheckMode {
    Types,
    Execution,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty {
    Primitive(&'static str),
    String,
    List(&'static str),
    Array(Box<Ty>, u32),
    /// A struct, by index in the type table, with its name for messages.
    Struct(u32, Rc<str>),
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
enum ReferenceOrigin {
    Binding(usize),
    Temporary,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct FunctionParameter {
    access: IrAccess,
    ty: Ty,
}
const UNIT: Ty = Ty::Primitive("Unit");
const BOOL: Ty = Ty::Primitive("Bool");
const I32: Ty = Ty::Primitive("i32");
const F64: Ty = Ty::Primitive("f64");
fn ir_access(access: Access) -> IrAccess {
    match access {
        Access::Owned => IrAccess::Owned,
        Access::Borrow => IrAccess::Borrow,
        Access::Share => IrAccess::Share,
    }
}
fn access_name(access: IrAccess) -> &'static str {
    match access {
        IrAccess::Owned => "owned",
        IrAccess::Borrow => "borrow",
        IrAccess::Share => "share",
    }
}
fn numeric(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Primitive("i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "f32" | "f64")
    )
}
fn read_type(ty: Ty) -> Ty {
    match ty {
        Ty::Reference { inner, .. } => *inner,
        other => other,
    }
}
fn integer(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Primitive("i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64")
    )
}
fn int_limit(kind: &str) -> Option<u128> {
    match kind {
        "i8" => Some(127),
        "i16" => Some(32767),
        "i32" => Some(2147483647),
        "i64" => Some(9223372036854775807),
        "u8" => Some(255),
        "u16" => Some(65535),
        "u32" => Some(4294967295),
        "u64" => Some(u64::MAX as u128),
        _ => None,
    }
}
fn floating(ty: &Ty) -> bool {
    matches!(ty, Ty::Primitive("f32" | "f64"))
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
fn name(ty: &Ty) -> String {
    match ty {
        Ty::Primitive(s) => s.to_string(),
        Ty::String => "String".into(),
        Ty::List(element) => format!("List<{element}>"),
        Ty::Array(element, count) => format!("Array<{}, {count}>", name(element)),
        Ty::Struct(_, name) | Ty::Enum(_, name) => name.to_string(),
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
        | ExprKind::Bool(_)
        | ExprKind::Path(_) => Flow::NEXT,
        ExprKind::Array(elements) => elements
            .iter()
            .fold(Flow::NEXT, |flow, element| flow.then(flow_expr(element))),
        ExprKind::RepeatArray { value, count } => {
            if count.raw.bytes().all(|byte| byte == b'0' || byte == b'_') {
                Flow::NEXT
            } else {
                flow_expr(value)
            }
        }
        ExprKind::Index { base, index } => flow_expr(base).then(flow_expr(index)),
        ExprKind::Unary { operand, .. } => flow_expr(operand),
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
        ExprKind::Call { callee, arguments } => arguments
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

/// One arm: the variant it selects (`None` for the `_` arm) and, for each
/// payload slot of that variant, the owned local it binds (`None` for `_`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatchArmFact {
    pub variant: Option<u32>,
    pub bindings: Vec<Option<LocalId>>,
}

/// Facts are indexed by function, then by fresh expression/local identities.
/// The syntax module is deliberately not relabeled as checked syntax.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionFacts {
    pub id: FunctionId,
    pub span: Span,
    pub signature: Signature,
    pub locals: Vec<LocalFact>,
    pub expressions: Vec<ExpressionFact>,
    pub path_uses: Vec<PathUse>,
    /// Enum variant constructions: a unit variant path or a payload call.
    pub variant_uses: Vec<VariantUse>,
    /// `match` expressions over owned enums, with the pattern facts lowering needs.
    pub matches: Vec<MatchFact>,
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
                Some(registry::TemplateId::Attempt) => Some(memobits_ir::EntryOutcome::Attempt),
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
            "Bool" => Primitive::Bool,
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
        Ty::List("u8") => IrType::List(Primitive::U8),
        Ty::List("u32") => IrType::List(Primitive::U32),
        Ty::List(_) => return None,
        Ty::Array(element, len) => IrType::Array {
            element: Box::new(ir_type(element)?),
            len: *len,
        },
        Ty::Struct(id, _) => IrType::Struct(TypeId(*id)),
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
    diagnostics: Vec<Diagnostic>,
    lowering: bool,
    /// Addresses of expressions in an owned-value position (binding initialiser,
    /// `=` right-hand side, return/tail value, owned aggregate argument, array
    /// element) that may be a whole aggregate: array and struct literals,
    /// repetitions, named locals, and the tails of `if`/block expressions in
    /// such a position.
    allowed_arrays: HashSet<usize>,
    concat_destination: Option<usize>,
    temporary_borrow_argument: Option<usize>,
    /// Field reads that already failed; they are not also reported as extractions.
    failed_fields: HashSet<usize>,
    /// Address of the path expression currently checked as an index or field base.
    index_base: usize,
    /// Module whose names and field visibility are being checked.
    module: String,
    table: Rc<TypeTable>,
    functions: HashMap<String, Ty>,
    function_ids: HashMap<String, FunctionId>,
    facts: Option<FunctionFacts>,
    qualified_functions: HashMap<String, Ty>,
    qualified_function_ids: HashMap<String, FunctionId>,
    imports: HashMap<String, String>,
    scopes: Vec<HashMap<String, Binding>>,
    result: Ty,
}
impl Checker {
    fn error(&mut self, n: u16, span: Span, message: impl Into<String>) {
        self.diagnostics.push(diagnostic(n, span, message));
    }
    fn array_count(&mut self, count: &memobits_syntax::IntegerLiteral) -> Option<u32> {
        let value = count.raw.replace('_', "").parse::<u32>().ok();
        if value.is_none() {
            self.error(
                8,
                count.span,
                "array length exceeds implementation limit u32::MAX",
            );
        }
        value
    }
    /// Executable arrays hold non-Unit primitive, struct or nested array elements.
    fn check_element_support(&mut self, element: &Ty, span: Span) {
        if self.table.is_borrow_option(element) {
            self.error(17, span, "Option<borrow T> cannot be stored in an array");
        } else if self.lowering
            && !matches!(
                element,
                Ty::Error | Ty::Never | Ty::String | Ty::Array(..) | Ty::Struct(..) | Ty::Enum(..)
            )
            && !matches!(element, Ty::Primitive(kind) if *kind != "Unit")
        {
            self.error(
                17,
                span,
                "executable arrays support non-Unit primitive, struct and nested array elements only",
            );
        }
    }
    /// Whole aggregate values (arrays and structs) are produced by a literal,
    /// repetition, call or named local in an owned-value position. The position propagates into the tails
    /// of `if` and block expressions, which therefore may produce arrays too.
    fn allow_array_value(&mut self, value: &Expr) {
        match &value.kind {
            ExprKind::Array(_)
            | ExprKind::RepeatArray { .. }
            | ExprKind::Struct { .. }
            | ExprKind::Path(_) => {
                self.allowed_arrays.insert(value as *const Expr as usize);
            }
            ExprKind::Block(block) => {
                if let Some(tail) = &block.tail {
                    self.allow_array_value(tail);
                }
            }
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                if let Some(tail) = &then_branch.tail {
                    self.allow_array_value(tail);
                }
                if let Some(other) = else_branch {
                    self.allow_array_value(other);
                }
            }
            ExprKind::Match { arms, .. } => {
                for arm in arms {
                    self.allow_array_value(&arm.body);
                }
            }
            _ => {}
        }
    }
    fn array_allowed(&self, expr: &Expr) -> bool {
        self.allowed_arrays
            .contains(&(expr as *const Expr as usize))
    }
    /// TE022: an aggregate element or field read is not an owned value; it may
    /// not feed a binding, assignment, return, call argument, array element or
    /// block result. Primitive reads are copied implicitly and are allowed.
    fn reject_extraction(&mut self, expr: &Expr, ty: &Ty) {
        if self.lowering
            && !matches!(ty, Ty::Primitive(_))
            && !self.failed_fields.contains(&(expr as *const Expr as usize))
            && matches!(expr.kind, ExprKind::Index { .. } | ExprKind::Field { .. })
        {
            let what = if matches!(expr.kind, ExprKind::Field { .. }) {
                "a struct or array field cannot be moved out by field access"
            } else {
                "a struct or array element cannot be moved out by indexing"
            };
            self.error(
                22,
                expr.span,
                format!("{what}; only primitive values are copied implicitly and partial moves are deferred, so borrow or share the aggregate, or read a primitive inside it"),
            );
        }
    }
    /// TE004: a write through a projection chain (`a[i].x`, `l.pts[j]`) needs
    /// the root binding to be a `var` owner or a share reference.
    fn check_place_writable(&mut self, target: &Expr, root: &str, binding: &Binding) {
        let writable = binding.mutable || binding.access == IrAccess::Share;
        let aggregate = |ty: &Ty| match ty {
            Ty::Array(..) => Some("an element of immutable array"),
            Ty::Struct(..) => Some("a field of immutable struct"),
            _ => None,
        };
        match &binding.ty {
            ty @ (Ty::Array(..) | Ty::Struct(..) | Ty::Enum(..)) if !writable => {
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
                Ty::Array(..) | Ty::Struct(..) | Ty::Enum(..)
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
                Ty::Array(..) | Ty::Struct(..) | Ty::Enum(..)
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
        self.report_type_resolution(ty, self.table.resolve(&self.module, ty))
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
            Ty::Struct(id, _) => Some(table.info(*id)),
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
                        self.report_type_resolution(ty, self.table.resolve_local(&self.module, ty))
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
                            "Option<borrow T> requires an immutable local binding",
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
                    if operator == "="
                        && matches!(&target.kind, ExprKind::Path(path) if path.len() == 1
                            && self.lookup(&path[0]).is_some_and(|binding|
                                (binding.mutable && binding.ty == Ty::String)
                                || (binding.access == IrAccess::Share && target_ty == Ty::String)))
                    {
                        self.concat_destination = Some(value as *const Expr as usize);
                    }
                    let value_ty = self.expr(value, Some(&target_ty));
                    self.concat_destination = previous;
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
                        if !numeric(&target_ty) {
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
                    }
                }
                StatementKind::Expression(expr) => {
                    let previous = self.concat_destination;
                    self.concat_destination = Some(expr as *const Expr as usize);
                    let ty = self.expr(expr, None);
                    self.concat_destination = previous;
                    if matches!(
                        ty,
                        Ty::String | Ty::Array(..) | Ty::Struct(..) | Ty::Enum(..)
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
                        Ty::Never | Ty::Error => Ty::Error,
                        _ => {
                            self.error(17, items.span, "loop iteration requires a fixed Array or Bytes with numeric or Bool elements");
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

    fn list_read_receiver(&self, base: &Expr) -> bool {
        match &base.kind {
            ExprKind::Path(path) => path.len() == 1,
            ExprKind::Call { callee, .. } => self.direct_callee(callee),
            _ => false,
        }
    }

    fn string_read(
        &mut self,
        expression: &Expr,
        base: &Expr,
        method: &str,
        arguments: &[Expr],
    ) -> Ty {
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
        if method == "concat" && self.concat_destination != Some(expression as *const Expr as usize)
        {
            self.error(
                17,
                expression.span,
                "concat requires a whole String local, a standalone statement, an immediate read-only method, or an owned or explicit borrow String argument to a direct internal call",
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
            Ty::List(element @ ("u8" | "u32")) if self.list_read_receiver(base) => {
                Some(Ty::Primitive(element))
            }
            Ty::Error | Ty::Never => None,
            _ => {
                self.error(
                    17,
                    base.span,
                    format!("{method}() requires an array with numeric or Bool elements, or a List<u8> or List<u32> local, reference binding, or direct internal call result"),
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

    fn list_get(&mut self, expr: &Expr, base: &Expr, arguments: &[Expr]) -> Ty {
        self.allow_array_value(base);
        let receiver = self.expr(base, None);
        let Ty::List(element) = read_type(receiver) else {
            self.error(
                17,
                base.span,
                "get() requires a whole List local or a direct internal List call",
            );
            return Ty::Error;
        };
        if !self.list_read_receiver(base) {
            self.error(
                17,
                base.span,
                "get() requires a whole List local or a direct internal List call",
            );
        }
        if arguments.len() != 1 {
            self.error(10, expr.span, "get() expects one index");
            return Ty::Error;
        }
        let index_type = Ty::Primitive("u32");
        let index = read_type(self.expr(&arguments[0], Some(&index_type)));
        self.ensure(&index, &index_type, arguments[0].span);
        if index == Ty::Never {
            return Ty::Never;
        }
        self.table.instantiate_enum(
            registry::by_id(registry::TemplateId::Option),
            vec![ResolvedArgument::Type(Ty::Primitive(element))],
            expr.span,
        )
    }

    fn list_mutation(&mut self, expr: &Expr, base: &Expr, method: &str, arguments: &[Expr]) -> Ty {
        self.allow_array_value(base);
        let receiver = self.expr(base, None);
        let mutable_receiver = matches!(
            receiver,
            Ty::List(_)
                | Ty::Reference {
                    access: IrAccess::Share,
                    ..
                }
        );
        let writable = matches!(&base.kind, ExprKind::Path(path) if path.len() == 1
            && self.lookup(&path[0]).is_some_and(|binding| mutable_receiver && (binding.mutable || binding.access == IrAccess::Share)));
        let Ty::List(element) = read_type(receiver) else {
            self.error(
                17,
                base.span,
                format!("{method}() requires a mutable List local, mutable share handle, or share parameter"),
            );
            return Ty::Error;
        };
        if !writable {
            self.error(
                17,
                base.span,
                format!("{method}() requires a mutable List local, mutable share handle, or share parameter"),
            );
        }
        let pop = method == "pop";
        if arguments.len() != usize::from(method == "push") {
            let message = match method {
                "pop" => "pop() takes no arguments",
                "clear" => "clear() takes no arguments",
                _ => "push() expects one element",
            };
            self.error(10, expr.span, message);
            return Ty::Error;
        }
        if pop {
            return self.table.instantiate_enum(
                registry::by_id(registry::TemplateId::Option),
                vec![ResolvedArgument::Type(Ty::Primitive(element))],
                expr.span,
            );
        }
        if method == "clear" {
            return UNIT;
        }
        let element = Ty::Primitive(element);
        let value = read_type(self.expr(&arguments[0], Some(&element)));
        self.ensure(&value, &element, arguments[0].span);
        if value == Ty::Never {
            Ty::Never
        } else {
            UNIT
        }
    }

    fn string_push_str(&mut self, expression: &Expr, base: &Expr, arguments: &[Expr]) -> Ty {
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
                "cannot borrow or share the storage of Option<borrow T>",
            );
            return Ty::Error;
        }
        if is_row
            && !matches!(
                base_ty,
                Ty::String | Ty::Array(..) | Ty::Struct(..) | Ty::Enum(..) | Ty::Error | Ty::Never
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
            Ty::String | Ty::Array(..) | Ty::Struct(..) | Ty::Enum(..) if is_row => {
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
            Ty::Reference { inner, .. } if matches!(inner.as_ref(), Ty::Struct(..)) => *inner,
            other => other,
        };
        match base_ty {
            Ty::Struct(id, struct_name) => {
                let table = Rc::clone(&self.table);
                let info = &table.info(id);
                match info.fields.iter().find(|field| field.name == field_name) {
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
                    "cannot determine {}'s outcome type; provide an {} annotation",
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
                    Ty::String | Ty::Array(..) | Ty::Struct(..) | Ty::Enum(..)
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
                        "Some requires a borrow reference for Option<borrow T>",
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
    /// `match scrutinee { pattern => body, ... }`. Patterns are flat
    /// (`Enum::Variant`, `Enum::Variant(a, _)`, `_`). An owned scrutinee is
    /// consumed and each arm binds owned payload locals; a scrutinee that
    /// cannot be moved (a reference, an element or field place) is matched in
    /// place and binds borrows.
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
        let mut enum_id = None;
        // A scrutinee that cannot be moved (a reference, or an element or field
        // place) is matched in place: payload bindings borrow the payload.
        let mut borrowed = false;
        match &scrutinee_ty {
            Ty::Enum(found, _) => {
                borrowed = matches!(
                    scrutinee.kind,
                    ExprKind::Index { .. } | ExprKind::Field { .. }
                );
                enum_id = Some(*found);
            }
            Ty::Reference { inner, .. } if matches!(inner.as_ref(), Ty::Enum(..)) => {
                borrowed = true;
                if let Ty::Enum(found, _) = inner.as_ref() {
                    enum_id = Some(*found);
                }
            }
            Ty::Never | Ty::Error => {}
            other => self.error(
                29,
                scrutinee.span,
                format!("`match` requires an enum value, found {}", name(other)),
            ),
        }
        let info_storage = enum_id.map(|enum_id| table.info(enum_id));
        let info = info_storage.as_ref();
        let mut covered: Vec<bool> =
            info.map_or(Vec::new(), |info| vec![false; info.variants.len()]);
        let mut wildcard_seen = false;
        let mut result: Option<Ty> = None;
        let mut facts = Vec::new();
        for arm in arms {
            self.scopes.push(HashMap::new());
            let mut arm_fact = MatchArmFact {
                variant: None,
                bindings: Vec::new(),
            };
            let mut unreachable = wildcard_seen.then(|| {
                "unreachable match arm: an earlier `_` arm already matches every variant"
                    .to_string()
            });
            match &arm.pattern.kind {
                PatternKind::Wildcard => {
                    if unreachable.is_none() && !covered.is_empty() && covered.iter().all(|c| *c) {
                        unreachable = Some(
                            "unreachable `_` arm: every variant is already matched by an earlier arm"
                                .into(),
                        );
                    }
                    wildcard_seen = true;
                }
                PatternKind::Variant { path, slots } => {
                    let expected_enum = enum_id.map(|id| Ty::Enum(id, table.info(id).name.into()));
                    let contextual =
                        self.contextual_variant(path, arm.pattern.span, expected_enum.as_ref());
                    let resolved = if contextual.is_some() {
                        contextual
                    } else if let Some((template, _)) = self.prelude_variant(path) {
                        self.error(
                            30,
                            arm.pattern.span,
                            format!(
                                "pattern '{}' belongs to {}, but the scrutinee has type '{}'",
                                path[0],
                                template.name,
                                name(&scrutinee_ty)
                            ),
                        );
                        None
                    } else {
                        let message = if path.len() == 1 {
                            format!(
                                "'{}' is not an enum variant pattern; binding patterns are not supported, write `_` to match anything",
                                path[0]
                            )
                        } else {
                            format!("'{}' does not name an enum variant", path.join("::"))
                        };
                        self.error(30, arm.pattern.span, message);
                        None
                    };
                    let mut declared_payload: Option<Vec<Ty>> = None;
                    if let Some((Ty::Enum(pattern_enum, pattern_name), variant)) = &resolved {
                        let pattern_info = &table.info(*pattern_enum);
                        if let Some(expected_enum) = enum_id {
                            if expected_enum != *pattern_enum {
                                self.error(
                                    30,
                                    arm.pattern.span,
                                    format!(
                                        "pattern '{}' belongs to enum '{}', but the scrutinee has type '{}'",
                                        path.join("::"),
                                        pattern_name,
                                        name(&scrutinee_ty)
                                    ),
                                );
                            } else {
                                match variant {
                                    None => self.error(
                                        30,
                                        arm.pattern.span,
                                        format!(
                                            "enum '{}' has no variant '{}'",
                                            pattern_info.name,
                                            path[path.len() - 1]
                                        ),
                                    ),
                                    Some(variant) => {
                                        let declared = &pattern_info.variants[*variant as usize];
                                        arm_fact.variant = Some(*variant);
                                        declared_payload = Some(declared.payload.clone());
                                        if slots.len() != declared.payload.len() {
                                            self.error(
                                                30,
                                                arm.pattern.span,
                                                format!(
                                                    "variant '{}::{}' has {} payload value(s) but the pattern binds {}; bind each one by name or `_`",
                                                    pattern_info.name,
                                                    declared.name,
                                                    declared.payload.len(),
                                                    slots.len()
                                                ),
                                            );
                                        }
                                        if unreachable.is_none() {
                                            if covered[*variant as usize] {
                                                unreachable = Some(format!(
                                                    "unreachable match arm: variant '{}::{}' is already matched by an earlier arm",
                                                    pattern_info.name, declared.name
                                                ));
                                            } else {
                                                covered[*variant as usize] = true;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    let mut bound: Vec<&str> = Vec::new();
                    for (index, slot) in slots.iter().enumerate() {
                        let slot_ty = declared_payload
                            .as_ref()
                            .and_then(|payload| payload.get(index))
                            .cloned()
                            .unwrap_or(Ty::Error);
                        let Some(binding) = &slot.name else {
                            arm_fact.bindings.push(None);
                            continue;
                        };
                        if bound.contains(&binding.as_str()) {
                            self.error(
                                30,
                                slot.span,
                                format!("binding '{binding}' is introduced more than once in the pattern"),
                            );
                        }
                        bound.push(binding);
                        let addr = slot as *const _ as usize;
                        // A borrowing match binds primitives by copy and every
                        // aggregate payload as a read-only reference to it.
                        let slot_ty = if borrowed
                            && matches!(
                                slot_ty,
                                Ty::String | Ty::Array(..) | Ty::Struct(..) | Ty::Enum(..)
                            ) {
                            Ty::Reference {
                                access: IrAccess::Borrow,
                                inner: Box::new(slot_ty),
                                origin: ReferenceOrigin::Binding(addr),
                            }
                        } else {
                            slot_ty
                        };
                        let local = self.register_local(
                            binding,
                            &slot_ty,
                            false,
                            IrAccess::Owned,
                            slot.span,
                            addr,
                        );
                        arm_fact.bindings.push(local);
                        self.scopes.last_mut().unwrap().insert(
                            binding.clone(),
                            Binding {
                                ty: slot_ty,
                                mutable: false,
                                access: IrAccess::Owned,
                                id: local,
                                origin: addr,
                            },
                        );
                    }
                }
            }
            if let Some(message) = unreachable {
                self.error(32, arm.pattern.span, message);
            }
            facts.push(arm_fact);
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
        if let Some(info) = info {
            if !wildcard_seen {
                let missing: Vec<String> = info
                    .variants
                    .iter()
                    .zip(&covered)
                    .filter(|(_, covered)| !**covered)
                    .map(|(variant, _)| format!("{}::{}", info.name, variant.name))
                    .collect();
                if !missing.is_empty() {
                    self.error(
                        31,
                        expr.span,
                        format!(
                            "non-exhaustive match: missing {}; add arms for them or a `_` arm",
                            missing.join(", ")
                        ),
                    );
                }
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
    fn expr_impl(&mut self, expr: &Expr, expected: Option<&Ty>, id: Option<ExprId>) -> Ty {
        match &expr.kind {
            ExprKind::Path(path)
                if self.contextual_variant(path, expr.span, expected).is_some() =>
            {
                let (enum_ty, variant) = self
                    .contextual_variant(path, expr.span, expected)
                    .expect("checked variant path");
                self.unit_variant(expr, id, path, enum_ty, variant)
            }
            ExprKind::Call { callee, arguments }
                if matches!(&callee.kind, ExprKind::Path(path)
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
                if let Some(list @ Ty::List(_)) = expected {
                    if elements.is_empty() {
                        return list.clone();
                    }
                    self.error(17, expr.span, "only empty List literals are supported");
                    return Ty::Error;
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
                    Ty::Reference { inner, .. } if matches!(inner.as_ref(), Ty::Array(..)) => {
                        *inner
                    }
                    other => other,
                };
                let result = match base_ty {
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
                            format!("indexing requires an Array value, found {}", name(&other)),
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
            ExprKind::Bool(_) => BOOL,
            ExprKind::Path(path) => {
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
                            Ty::String | Ty::Array(..) | Ty::Struct(..) | Ty::Enum(..)
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
                    "+" | "-" if numeric(&ty) => {
                        if operator == "-"
                            && matches!(ty, Ty::Primitive("u8" | "u16" | "u32" | "u64"))
                        {
                            self.error(7, expr.span, "negation requires a signed numeric type");
                        }
                        ty
                    }
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
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                let bool_op = matches!(operator.as_str(), "&&" | "||");
                let expected_num = expected.filter(|t| numeric(t));
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
                    let right_ty = read_type(
                        self.expr(right, if bool_op { Some(&BOOL) } else { Some(&left_ty) }),
                    );
                    (left_ty, right_ty)
                };
                if left_ty == Ty::Never || (right_ty == Ty::Never && !bool_op) {
                    return Ty::Never;
                }
                match operator.as_str() {
                    "&&" | "||" => {
                        self.ensure(&left_ty, &BOOL, left.span);
                        self.ensure(&right_ty, &BOOL, right.span);
                        BOOL
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
                        } else if !numeric(&left_ty) && left_ty != BOOL && left_ty != Ty::Error {
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
            ExprKind::Call { callee, arguments } => {
                if let ExprKind::Path(path) = &callee.kind {
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
            ExprKind::Struct { path, fields } => {
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
                    arguments: Vec::new(),
                };
                let target = self.type_path(&literal_type);
                let table = Rc::clone(&self.table);
                let info_storage = match &target {
                    Ty::Struct(id, _) => Some(table.info(*id)),
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
                    let actual = self.expr(&init.value, expected_field.as_ref());
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
/// Array forms outside the executable subset (results, nesting, element references) report TE017.
pub fn check_typed_module(module: &Module) -> Result<TypedModule, Vec<Diagnostic>> {
    let (mut diagnostics, functions, types) = check_standalone(module, CheckMode::Execution);
    diagnostics.extend(crate::check_control_flow(module));
    if diagnostics.is_empty() {
        Ok(TypedModule { functions, types })
    } else {
        Err(diagnostics)
    }
}

fn check_standalone(
    module: &Module,
    mode: CheckMode,
) -> (Vec<Diagnostic>, Vec<FunctionFacts>, Vec<TypeFact>) {
    let capture = mode != CheckMode::Types;
    let (table, table_diagnostics) = TypeTable::build(&[("", module)], HashMap::new());
    let mut c = Checker {
        diagnostics: table_diagnostics,
        lowering: capture,
        allowed_arrays: HashSet::new(),
        concat_destination: None,
        temporary_borrow_argument: None,
        failed_fields: HashSet::new(),
        index_base: 0,
        module: String::new(),
        table: Rc::new(table),
        functions: HashMap::new(),
        function_ids: HashMap::new(),
        facts: None,
        qualified_functions: HashMap::new(),
        qualified_function_ids: HashMap::new(),
        imports: HashMap::new(),
        scopes: Vec::new(),
        result: UNIT,
    };
    let mut next_function = 0u32;
    for item in &module.items {
        match &item.kind {
            ItemKind::Function {
                name,
                parameters,
                result,
                ..
            } => {
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
            ItemKind::Use { .. } => c.error(15, item.span, "imports require module resolution"),
            ItemKind::Type { .. } => {}
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
                    matches: Vec::new(),
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
    let mut ids = HashMap::new();
    let mut next_id = 0;
    for (module_name, source) in &resolution.modules {
        for item in &source.syntax.items {
            if let ItemKind::Function { name, .. } = &item.kind {
                ids.insert(format!("{module_name}::{name}"), FunctionId(next_id));
                next_id += 1;
            }
        }
    }
    let mut signatures = HashMap::new();
    for (module_name, source) in &resolution.modules {
        let mut c = Checker {
            lowering,
            module: module_name.clone(),
            table: Rc::clone(&table),
            ..checker()
        };
        for item in &source.syntax.items {
            match &item.kind {
                ItemKind::Function {
                    name,
                    parameters,
                    result,
                    ..
                } => {
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
                ItemKind::Type { .. } => {}
                ItemKind::Use { .. } => {}
            }
        }
        diagnostics.extend(c.diagnostics);
        diagnostics.extend(crate::check_control_flow(&source.syntax));
    }
    let mut all_facts = Vec::with_capacity(next_id as usize);
    for (module_name, source) in &resolution.modules {
        let mut c = Checker {
            lowering,
            module: module_name.clone(),
            table: Rc::clone(&table),
            qualified_functions: signatures.clone(),
            qualified_function_ids: ids.clone(),
            ..checker()
        };
        for item in &source.syntax.items {
            match &item.kind {
                ItemKind::Function { name, .. } => {
                    let key = format!("{module_name}::{name}");
                    if let Some(signature) = signatures.get(&key) {
                        c.functions.insert(name.clone(), signature.clone());
                        c.function_ids.insert(name.clone(), ids[&key]);
                    }
                }
                ItemKind::Use { path, alias, .. } => {
                    if let Some(local) = alias.as_ref().or(path.last()) {
                        c.imports.insert(local.clone(), path.join("::"));
                    }
                }
                ItemKind::Type { .. } => {}
            }
        }
        for (alias, path) in &project.manifest.prelude {
            c.imports
                .entry(alias.clone())
                .or_insert_with(|| path.clone());
        }
        for (alias, path) in &c.imports {
            let key = path.strip_prefix("self::").unwrap_or(path);
            if let Some(signature) = signatures.get(key) {
                c.functions.insert(alias.clone(), signature.clone());
                if let Some(id) = ids.get(key) {
                    c.function_ids.insert(alias.clone(), *id);
                }
            }
        }
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
                            signature,
                            locals: Vec::new(),
                            expressions: Vec::new(),
                            path_uses: Vec::new(),
                            variant_uses: Vec::new(),
                            matches: Vec::new(),
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
        diagnostics.extend(c.diagnostics);
    }
    if diagnostics.is_empty() {
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
        diagnostics: Vec::new(),
        lowering: true,
        allowed_arrays: HashSet::new(),
        concat_destination: None,
        temporary_borrow_argument: None,
        failed_fields: HashSet::new(),
        index_base: 0,
        module: String::new(),
        table: Rc::new(TypeTable::empty()),
        functions: HashMap::new(),
        function_ids: HashMap::new(),
        facts: None,
        qualified_functions: HashMap::new(),
        qualified_function_ids: HashMap::new(),
        imports: HashMap::new(),
        scopes: Vec::new(),
        result: UNIT,
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
        assert!(diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("does not match the share parameter access")));
        assert!(!diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("does not match the borrow parameter access")));
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
        assert!(!diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("cannot assign to immutable binding")));
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
