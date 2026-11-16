//! Type checks for primitives and fixed arrays. Executable IR supports arrays of primitive
//! elements (literal, repetition, indexing, element and whole-array assignment); every other
//! array form is gated with TE017.
//! Name resolution across modules and ownership checking are separate passes.
use std::collections::HashMap;

use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, Span};
use memobits_ir::{
    Access as IrAccess, FunctionId, LocalId, ParameterType, Primitive, Signature, Type as IrType,
};
use memobits_project::Project;
use memobits_resolve::Resolution;
use memobits_syntax::{
    Access, Block, Expr, ExprKind, ItemKind, Module, Parameter, StatementKind, Type,
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty {
    Primitive(&'static str),
    Array(Box<Ty>, u32),
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
fn parameter_accepts(actual: &Ty, parameter: &FunctionParameter) -> bool {
    match (parameter.access, actual) {
        (IrAccess::Owned, actual) => compatible(actual, &parameter.ty),
        (
            IrAccess::Borrow,
            Ty::Reference {
                access: IrAccess::Borrow | IrAccess::Share,
                inner,
                ..
            },
        ) => compatible(inner, &parameter.ty),
        (
            IrAccess::Share,
            Ty::Reference {
                access: IrAccess::Share,
                inner,
                ..
            },
        ) => compatible(inner, &parameter.ty),
        (_, Ty::Error | Ty::Never) => true,
        _ => false,
    }
}
fn name(ty: &Ty) -> String {
    match ty {
        Ty::Primitive(s) => s.to_string(),
        Ty::Array(element, count) => format!("Array<{}, {count}>", name(element)),
        Ty::Function(..) => "function".into(),
        Ty::Reference { access, inner, .. } => {
            format!("{} {}", access_name(*access), name(inner))
        }
        Ty::Never => "never".into(),
        Ty::Error => "unknown".into(),
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
            StatementKind::Binding { value, .. } | StatementKind::Expression(value) => {
                flow_expr(value)
            }
            StatementKind::Assign { target, value, .. } => flow_expr(target).then(flow_expr(value)),
            StatementKind::Return(value) => value
                .as_ref()
                .map_or(Flow::STOP, flow_expr)
                .then(Flow::STOP),
            StatementKind::Loop(body) => Flow {
                falls: flow_block(body).breaks,
                breaks: false,
            },
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
        ExprKind::Number(_) | ExprKind::Bool(_) | ExprKind::Path(_) => Flow::NEXT,
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
    next_expr: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedModule {
    pub functions: Vec<FunctionFacts>,
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
        Ty::Array(element, len) => IrType::Array {
            element: Box::new(ir_type(element)?),
            len: *len,
        },
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
    executable: bool,
    /// Address of the one array literal expression that may initialize a `let`.
    allowed_array: usize,
    /// Address of the path expression currently checked as an index base.
    index_base: usize,
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
    /// Types in function signatures: arrays cannot cross calls yet.
    fn signature_type(&mut self, ty: &Type) -> Ty {
        let checked = self.type_path(ty);
        if self.executable && matches!(checked, Ty::Array(..)) {
            self.error(
                17,
                ty.span,
                "array parameters and results are not supported yet",
            );
        }
        checked
    }
    /// Executable arrays hold non-Unit primitive elements only.
    fn check_element_support(&mut self, element: &Ty, span: Span) {
        if self.executable
            && !matches!(element, Ty::Error | Ty::Never)
            && !matches!(element, Ty::Primitive(kind) if *kind != "Unit")
        {
            self.error(
                17,
                span,
                "executable arrays support non-Unit primitive elements only",
            );
        }
    }
    /// Whole-array values are produced only by a literal, repetition or named
    /// local that directly initializes a binding or is assigned with `=`.
    fn allow_array_value(&mut self, value: &Expr) {
        if matches!(
            value.kind,
            ExprKind::Array(_) | ExprKind::RepeatArray { .. } | ExprKind::Path(_)
        ) {
            self.allowed_array = value as *const Expr as usize;
        }
    }
    /// D1: an element read is not an owned value. It may feed arithmetic,
    /// comparisons and conditions, but not a binding, assignment, return, call
    /// argument, array element or block result.
    fn reject_extraction(&mut self, expr: &Expr) {
        if self.executable && matches!(expr.kind, ExprKind::Index { .. }) {
            self.error(
                22,
                expr.span,
                "an array element cannot be moved out by indexing; an explicit copy is required and is not available yet. Use the element inside an arithmetic or comparison expression instead",
            );
        }
    }
    fn type_path(&mut self, ty: &Type) -> Ty {
        if ty.path == ["Array"] {
            if let [memobits_syntax::TypeArgument::Type(element), memobits_syntax::TypeArgument::Integer(count)] =
                ty.arguments.as_slice()
            {
                let element = self.type_path(element);
                self.check_element_support(&element, ty.span);
                return match self.array_count(count) {
                    Some(count) => Ty::Array(Box::new(element), count),
                    None => Ty::Error,
                };
            }
            self.error(
                2,
                ty.span,
                "Array requires an element type and integer literal length",
            );
            return Ty::Error;
        }
        if !ty.arguments.is_empty() {
            self.error(1, ty.span, "unsupported type arguments");
            return Ty::Error;
        }
        if ty.path.len() != 1 {
            self.error(
                1,
                ty.span,
                "qualified types are not supported by this primitive type pass",
            );
            return Ty::Error;
        }
        match ty.path[0].as_str() {
            "i8" => Ty::Primitive("i8"),
            "i16" => Ty::Primitive("i16"),
            "i32" => I32,
            "i64" => Ty::Primitive("i64"),
            "u8" => Ty::Primitive("u8"),
            "u16" => Ty::Primitive("u16"),
            "u32" => Ty::Primitive("u32"),
            "u64" => Ty::Primitive("u64"),
            "f32" => Ty::Primitive("f32"),
            "f64" => F64,
            "Bool" => BOOL,
            _ => {
                self.error(
                    1,
                    ty.span,
                    format!("unsupported or unresolved type '{}'", ty.path[0]),
                );
                Ty::Error
            }
        }
    }
    fn ensure(&mut self, actual: &Ty, expected: &Ty, span: Span) {
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
                    let annotation = annotation.as_ref().map(|ty| self.type_path(ty));
                    self.allow_array_value(value);
                    let inferred = self.expr(value, annotation.as_ref());
                    self.reject_extraction(value);
                    if let Some(ann) = &annotation {
                        self.ensure(&inferred, ann, value.span);
                    }
                    let ty = annotation.unwrap_or(inferred);
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
                StatementKind::Assign {
                    target,
                    operator,
                    value,
                } => {
                    let target_ty = match &target.kind {
                        ExprKind::Path(path) if path.len() == 1 => {
                            match self.lookup(&path[0]).cloned() {
                                Some(binding) => {
                                    self.allowed_array = target as *const Expr as usize;
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
                        ExprKind::Index { base, .. } => {
                            let element = self.expr(target, None);
                            match &base.kind {
                                ExprKind::Path(path) if path.len() == 1 => {
                                    if let Some(binding) = self.lookup(&path[0]).cloned() {
                                        if matches!(binding.ty, Ty::Array(..))
                                            && !binding.mutable
                                            && binding.access != IrAccess::Share
                                        {
                                            self.error(
                                                4,
                                                target.span,
                                                format!(
                                                    "cannot assign to an element of immutable array binding '{}'; declare it with var",
                                                    path[0]
                                                ),
                                            );
                                        }
                                    }
                                }
                                _ => self.error(
                                    6,
                                    target.span,
                                    "element assignment requires a named local array",
                                ),
                            }
                            element
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
                    let value_ty = self.expr(value, Some(&target_ty));
                    if operator == "=" {
                        self.reject_extraction(value);
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
                    self.expr(expr, None);
                }
                StatementKind::Return(value) => {
                    let actual = value
                        .as_ref()
                        .map(|e| self.expr(e, Some(&self.result.clone())))
                        .unwrap_or(UNIT.clone());
                    if let Some(value) = value {
                        self.reject_extraction(value);
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
                StatementKind::Break | StatementKind::Continue => {}
            }
        }
        let tail_ty = if let Some(tail) = &block.tail {
            let ty = self.expr(tail, expected);
            self.reject_extraction(tail);
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

        let owner_binding = match &base.kind {
            ExprKind::Path(path) if path.len() == 1 => self.lookup(&path[0]).cloned(),
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
        let base_ty = self.expr(base, expected_inner);
        let (inner, origin, current_access) = match base_ty {
            Ty::Reference {
                access,
                inner,
                origin,
            } => (inner, origin, Some(access)),
            primitive @ Ty::Primitive(_) => {
                let origin = owner_binding
                    .as_ref()
                    .map_or(ReferenceOrigin::Temporary, |binding| {
                        ReferenceOrigin::Binding(binding.origin)
                    });
                let current_access = owner_binding.as_ref().map(|binding| binding.access);
                (Box::new(primitive), origin, current_access)
            }
            ty @ (Ty::Never | Ty::Error) => return ty,
            _ => {
                self.error(
                    17,
                    base.span,
                    "borrow/share conversion requires a primitive owner or reference",
                );
                return Ty::Error;
            }
        };

        if !matches!(inner.as_ref(), Ty::Primitive(_)) {
            self.error(
                17,
                base.span,
                "borrow/share conversion currently supports primitive values only",
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
    fn expr_impl(&mut self, expr: &Expr, expected: Option<&Ty>, id: Option<ExprId>) -> Ty {
        match &expr.kind {
            ExprKind::Array(elements) => {
                if self.executable && self.allowed_array != expr as *const Expr as usize {
                    self.error(
                        17,
                        expr.span,
                        "array literals must initialize a binding or be assigned with = in executable code",
                    );
                }
                let mut element_ty = match expected {
                    Some(Ty::Array(element, _)) => Some(element.as_ref().clone()),
                    _ => None,
                };
                for element in elements {
                    let actual = self.expr(element, element_ty.as_ref());
                    self.reject_extraction(element);
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
                if self.executable && self.allowed_array != expr as *const Expr as usize {
                    self.error(
                        17,
                        expr.span,
                        "array repetition must initialize a binding or be assigned with = in executable code",
                    );
                }
                let context = match expected {
                    Some(Ty::Array(element, _)) => Some(element.as_ref()),
                    _ => None,
                };
                // Check the expression exactly once, even for a zero count. Runtime
                // repetition and ownership are deliberately gated from typed IR.
                let element = self.expr(value, context);
                self.reject_extraction(value);
                if matches!(element, Ty::Reference { .. }) {
                    self.error(17, value.span, "array elements cannot be references yet");
                }
                if self.executable && matches!(element, Ty::Never) && context.is_none() {
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
                if self.executable {
                    if matches!(&base.kind, ExprKind::Path(path) if path.len() == 1) {
                        self.index_base = base.as_ref() as *const Expr as usize;
                    } else {
                        self.error(
                            17,
                            base.span,
                            "indexing is supported on named local arrays only",
                        );
                    }
                }
                let base_ty = self.expr(base, None);
                let index_ty = self.expr(index, None);
                if !integer(&index_ty) && !matches!(index_ty, Ty::Never | Ty::Error) {
                    self.error(7, index.span, "array index must be an integer");
                }
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
            ExprKind::Bool(_) => BOOL,
            ExprKind::Path(path) => {
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
                    if self.executable
                        && matches!(binding.ty, Ty::Array(..))
                        && self.index_base != expr as *const Expr as usize
                        && self.allowed_array != expr as *const Expr as usize
                    {
                        self.error(
                            17,
                            expr.span,
                            "whole arrays can only be moved by a direct binding initializer or = assignment, or indexed",
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
                        if !numeric(&left_ty) && left_ty != BOOL && left_ty != Ty::Error {
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
                if let ExprKind::Field { base, name } = &callee.kind {
                    let access = match name.as_str() {
                        "borrow" => Some(IrAccess::Borrow),
                        "share" => Some(IrAccess::Share),
                        _ => None,
                    };
                    if let Some(access) = access {
                        return self.reference_conversion(expr, base, arguments, access, expected);
                    }
                }
                let ty = self.expr(callee, None);
                if let Ty::Function(params, result) = ty {
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
                        let actual = self.expr(arg, params.get(i).map(|parameter| &parameter.ty));
                        if params
                            .get(i)
                            .is_none_or(|parameter| parameter.access == IrAccess::Owned)
                        {
                            self.reject_extraction(arg);
                        }
                        if let Some(param) = params.get(i) {
                            if matches!(param.ty, Ty::Array(..)) {
                                self.error(
                                    17,
                                    arg.span,
                                    "array call arguments require aggregate ownership support",
                                );
                            }
                            if param.access == IrAccess::Owned {
                                self.ensure(&actual, &param.ty, arg.span);
                            } else if !parameter_accepts(&actual, param) {
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
            ExprKind::Field { base, .. } => {
                self.expr(base, None);
                self.error(
                    12,
                    expr.span,
                    "field access requires unsupported user-defined type checking",
                );
                Ty::Error
            }
            ExprKind::Block(block) => {
                let ty = self.block(block, expected).0;
                if matches!(ty, Ty::Reference { .. }) {
                    self.error(
                        17,
                        expr.span,
                        "reference-valued block results are not supported",
                    );
                }
                ty
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let cond = read_type(self.expr(condition, Some(&BOOL)));
                self.ensure(&cond, &BOOL, condition.span);
                let (then_ty, _) = self.block(then_branch, expected);
                if matches!(then_ty, Ty::Reference { .. }) {
                    self.error(
                        17,
                        then_branch.span,
                        "reference-valued branch results are not supported",
                    );
                }
                if let Some(other) = else_branch {
                    let else_ty = self.expr(other, expected.or(Some(&then_ty)));
                    if matches!(else_ty, Ty::Reference { .. }) {
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
    check_standalone(module, false).0
}

/// Check a standalone module and retain canonical local and expression facts.
/// This returns no facts if type or control-flow diagnostics exist.
/// Fixed arrays report TE017 here until aggregate ownership and IR are supported.
pub fn check_typed_module(module: &Module) -> Result<TypedModule, Vec<Diagnostic>> {
    let (mut diagnostics, functions) = check_standalone(module, true);
    diagnostics.extend(crate::check_control_flow(module));
    if diagnostics.is_empty() {
        Ok(TypedModule { functions })
    } else {
        Err(diagnostics)
    }
}

fn check_standalone(module: &Module, capture: bool) -> (Vec<Diagnostic>, Vec<FunctionFacts>) {
    let mut c = Checker {
        diagnostics: Vec::new(),
        executable: capture,
        allowed_array: 0,
        index_base: 0,
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
                        ty: c.signature_type(&p.ty),
                    })
                    .collect();
                let result = result.as_ref().map(|t| c.signature_type(t)).unwrap_or(UNIT);
                if c.functions
                    .insert(name.clone(), Ty::Function(params, Box::new(result)))
                    .is_some()
                {
                    c.error(14, item.span, format!("duplicate function '{name}'"));
                }
            }
            ItemKind::Use { .. } => c.error(15, item.span, "imports require module resolution"),
            ItemKind::Type { .. } => c.error(
                16,
                item.span,
                "user-defined types are not supported by this type pass",
            ),
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
                    next_expr: 0,
                });
            }
            check_function_body(&mut c, parameters, body, params, *result);
            if let Some(facts) = c.facts.take() {
                functions.push(facts);
            }
        }
    }
    (c.diagnostics, functions)
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
    check_resolved_mode(project, resolution, false)
        .err()
        .unwrap_or_default()
        .into_iter()
        .filter(|diagnostic| !matches!(diagnostic.code.to_string().as_str(), "TE020" | "TE021"))
        .collect()
}

pub(crate) fn check_resolved_typed(
    project: &Project,
    resolution: &Resolution,
) -> Result<TypedModule, Vec<Diagnostic>> {
    check_resolved_mode(project, resolution, true)
}

fn check_resolved_mode(
    project: &Project,
    resolution: &Resolution,
    executable: bool,
) -> Result<TypedModule, Vec<Diagnostic>> {
    if !resolution.diagnostics.is_empty() {
        return Err(resolution.diagnostics.clone());
    }
    let mut diagnostics = Vec::new();
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
            executable,
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
                            ty: c.signature_type(&p.ty),
                        })
                        .collect();
                    let result = result.as_ref().map(|t| c.signature_type(t)).unwrap_or(UNIT);
                    signatures.insert(
                        format!("{module_name}::{name}"),
                        Ty::Function(params, Box::new(result)),
                    );
                }
                ItemKind::Type { .. } => c.error(
                    16,
                    item.span,
                    "user-defined types are not supported by this type pass",
                ),
                ItemKind::Use { .. } => {}
            }
        }
        diagnostics.extend(c.diagnostics);
        diagnostics.extend(crate::check_control_flow(&source.syntax));
    }
    let mut all_facts = Vec::with_capacity(next_id as usize);
    for (module_name, source) in &resolution.modules {
        let mut c = Checker {
            executable,
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
                    let Some(ty) = ir_type(&Ty::Function(params.clone(), result.clone())) else {
                        check_function_body(
                            &mut c,
                            parameters,
                            body,
                            params.clone(),
                            *result.clone(),
                        );
                        continue;
                    };
                    let IrType::Function(signature) = ty else {
                        unreachable!()
                    };
                    c.facts = Some(FunctionFacts {
                        id: *id,
                        span: item.span,
                        signature,
                        locals: Vec::new(),
                        expressions: Vec::new(),
                        path_uses: Vec::new(),
                        next_expr: 0,
                    });
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
        })
    } else {
        Err(diagnostics)
    }
}

fn checker() -> Checker {
    Checker {
        diagnostics: Vec::new(),
        executable: true,
        allowed_array: 0,
        index_base: 0,
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
    if p.access != Access::Owned && matches!(ty, Ty::Array(..)) {
        c.error(
            17,
            p.span,
            "array references require aggregate ownership support",
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
