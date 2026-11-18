//! Lower a successfully checked standalone primitive module to control-flow IR.
use std::collections::{HashMap, HashSet};

use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, Span};
use memobits_ir::{
    Access, ArrayInit, BinaryOp, Block as IrBlock, BlockId, CanonicalFunction, CanonicalType,
    Constant, Edge, ErrorAncestry, FieldDef, Function, Instruction, InstructionKind, LoanId, Local,
    LocalId, Operand, Primitive, Program, Source, Terminator, TerminatorKind, Type, TypeDef,
    TypeDefKind, UnaryOp, UseMode, ValueId, VariantDef,
};
use memobits_project::Project;
use memobits_resolve::Resolution;
use memobits_syntax::{
    Block, Expr, ExprKind, FieldPattern, ItemKind, MatchArm, Module, Statement, StatementKind,
};

use crate::types::{
    check_resolved_mode, check_typed_module, CheckMode, ExprId, FunctionFacts, MatchFact,
    PathTarget, TypeFact, VariantUse,
};

/// IR type definitions for the checked structs. `module_path` names the module
/// of a standalone definition (whose fact module is empty).
fn program_types(
    structs: &[TypeFact],
    package: &str,
    module_of: impl Fn(&str) -> Vec<String>,
) -> Vec<TypeDef> {
    structs
        .iter()
        .map(|definition| TypeDef {
            path: CanonicalType {
                package: package.into(),
                module: if definition.error_ancestry == Some(ErrorAncestry::Root) {
                    vec![definition.module.clone()]
                } else {
                    module_of(&definition.module)
                },
                name: definition.name.clone(),
            },
            span: definition.span,
            error_ancestry: definition.error_ancestry,
            entry_outcome: definition.entry_outcome,
            kind: if definition.is_enum {
                TypeDefKind::Enum {
                    variants: definition
                        .variants
                        .iter()
                        .map(|variant| VariantDef {
                            name: variant.name.clone(),
                            payload: variant.payload.clone(),
                        })
                        .collect(),
                }
            } else {
                TypeDefKind::Struct {
                    fields: definition
                        .fields
                        .iter()
                        .map(|field| FieldDef {
                            name: field.name.clone(),
                            ty: field.ty.clone(),
                        })
                        .collect(),
                }
            },
        })
        .collect()
}
fn error(span: Span, message: impl Into<String>) -> Diagnostic {
    let mut d = Diagnostic::new(
        DiagnosticCode::new(Category::Type, 18).expect("static TE code"),
        Severity::Error,
        message,
    );
    d.span = Some(span);
    d
}

/// Lower a checked standalone module to validated typed IR.
///
/// `package` and `module_path` name the definitions in the resulting program.
/// Type and control-flow errors are returned as diagnostics. Ownership is checked
/// separately with `memobits_ownership::check_moves`.
pub fn lower_module(
    module: &Module,
    package: &str,
    module_path: &[String],
) -> Result<Program, Vec<Diagnostic>> {
    let facts = check_typed_module(module)?;
    let constant_errors = crate::constants::check_module(module, &facts.functions);
    if !constant_errors.is_empty() {
        return Err(constant_errors);
    }
    let mut diagnostics = Vec::new();
    if package.is_empty() || module_path.is_empty() || module_path.iter().any(String::is_empty) {
        let span = module.items.first().map(|i| i.span).unwrap_or(Span {
            source: memobits_diagnostics::SourceId(0),
            start: 0,
            end: 0,
        });
        diagnostics.push(error(span, "package and module path must be nonempty"));
        return Err(diagnostics);
    }
    let mut functions = Vec::new();
    for (item, fact) in module
        .items
        .iter()
        .filter(|i| matches!(i.kind, ItemKind::Function { .. }))
        .zip(&facts.functions)
    {
        let ItemKind::Function {
            name,
            body,
            parameters,
            ..
        } = &item.kind
        else {
            unreachable!()
        };
        let function = Function {
            path: CanonicalFunction {
                package: package.into(),
                module: module_path.to_vec(),
                name: name.clone(),
            },
            span: item.span,
            signature: fact.signature.clone(),
            parameter_locals: fact
                .locals
                .iter()
                .take(parameters.len())
                .map(|l| l.id)
                .collect(),
            locals: fact
                .locals
                .iter()
                .map(|l| Local {
                    name: l.name.clone(),
                    ty: l.ty.clone(),
                    mutable: l.mutable,
                    span: l.span,
                })
                .collect(),
            values: Vec::new(),
            blocks: vec![IrBlock {
                parameters: Vec::new(),
                instructions: Vec::new(),
                terminator: Terminator {
                    span: None,
                    kind: TerminatorKind::Unreachable,
                },
            }],
            entry: BlockId(0),
        };
        let mut builder = Builder::new(function, fact, &facts.types);
        builder.lower_body(body);
        functions.push(builder.function);
    }
    let program = Program {
        functions,
        types: program_types(&facts.types, package, |_| module_path.to_vec()),
    };
    if let Err(errors) = program.validate() {
        for failure in errors {
            let span = failure
                .function
                .and_then(|id| program.functions.get(id.0 as usize))
                .map_or_else(
                    || {
                        module.items.first().map(|i| i.span).unwrap_or(Span {
                            source: memobits_diagnostics::SourceId(0),
                            start: 0,
                            end: 0,
                        })
                    },
                    |f| f.span,
                );
            diagnostics.push(error(
                span,
                format!("IR lowering failed validation: {}", failure.message),
            ));
        }
    }
    if diagnostics.is_empty() {
        Ok(program)
    } else {
        Err(diagnostics)
    }
}

/// Lower all modules retained by a successful target-rooted resolution.
/// Function IDs follow the sorted module and source function order used by the
/// typed facts, so calls preserve canonical identity across module boundaries.
pub fn lower_resolved(
    project: &Project,
    resolution: &Resolution,
) -> Result<Program, Vec<Diagnostic>> {
    let typed = check_resolved_mode(project, resolution, CheckMode::Execution)?;
    let mut constant_errors = Vec::new();
    let mut fact_start = 0;
    for source in resolution.modules.values() {
        let function_count = source
            .syntax
            .items
            .iter()
            .filter(|item| matches!(item.kind, ItemKind::Function { .. }))
            .count();
        let fact_end = fact_start + function_count;
        let Some(module_facts) = typed.functions.get(fact_start..fact_end) else {
            return Err(vec![error(
                source
                    .syntax
                    .items
                    .first()
                    .map(|item| item.span)
                    .unwrap_or(Span {
                        source: source.id,
                        start: 0,
                        end: 0,
                    }),
                "typed project facts do not match resolved modules",
            )]);
        };
        constant_errors.extend(crate::constants::check_module(&source.syntax, module_facts));
        fact_start = fact_end;
    }
    if !constant_errors.is_empty() {
        return Err(constant_errors);
    }
    let mut functions = Vec::with_capacity(typed.functions.len());
    for (module_name, source) in &resolution.modules {
        let module_path = module_name
            .split("::")
            .map(str::to_owned)
            .collect::<Vec<_>>();
        for item in &source.syntax.items {
            if let ItemKind::Function {
                name,
                body,
                parameters,
                ..
            } = &item.kind
            {
                let Some(fact) = typed.functions.get(functions.len()) else {
                    return Err(vec![error(
                        item.span,
                        "typed project facts do not match resolved function order",
                    )]);
                };
                if fact.id.0 as usize != functions.len() {
                    return Err(vec![error(
                        item.span,
                        "typed project function ID differs from canonical program order",
                    )]);
                }
                let function = Function {
                    path: CanonicalFunction {
                        package: project.manifest.package.name.clone(),
                        module: module_path.clone(),
                        name: name.clone(),
                    },
                    span: item.span,
                    signature: fact.signature.clone(),
                    parameter_locals: fact
                        .locals
                        .iter()
                        .take(parameters.len())
                        .map(|l| l.id)
                        .collect(),
                    locals: fact
                        .locals
                        .iter()
                        .map(|l| Local {
                            name: l.name.clone(),
                            ty: l.ty.clone(),
                            mutable: l.mutable,
                            span: l.span,
                        })
                        .collect(),
                    values: Vec::new(),
                    blocks: vec![IrBlock {
                        parameters: Vec::new(),
                        instructions: Vec::new(),
                        terminator: Terminator {
                            span: None,
                            kind: TerminatorKind::Unreachable,
                        },
                    }],
                    entry: BlockId(0),
                };
                let mut builder = Builder::new(function, fact, &typed.types);
                builder.lower_body(body);
                functions.push(builder.function);
            }
        }
    }
    let program = Program {
        functions,
        types: program_types(&typed.types, &project.manifest.package.name, |module| {
            module.split("::").map(str::to_owned).collect()
        }),
    };
    if let Err(errors) = program.validate() {
        let fallback = program
            .functions
            .first()
            .map(|function| function.span)
            .unwrap_or(Span {
                source: memobits_diagnostics::SourceId(0),
                start: 0,
                end: 0,
            });
        return Err(errors
            .into_iter()
            .map(|failure| {
                error(
                    failure
                        .function
                        .and_then(|id| program.functions.get(id.0 as usize))
                        .map_or(fallback, |f| f.span),
                    format!("IR lowering failed validation: {}", failure.message),
                )
            })
            .collect());
    }
    Ok(program)
}

fn consume(mut operand: Operand) -> Operand {
    if !matches!(operand.source, Source::Function(_)) {
        operand.mode = UseMode::Consume;
    }
    operand
}
fn read(mut operand: Operand) -> Operand {
    operand.mode = UseMode::Read;
    operand
}
fn op(source: Source, span: Span) -> Operand {
    Operand {
        source,
        mode: UseMode::Read,
        span: Some(span),
    }
}
fn binary_op(value: &str) -> BinaryOp {
    match value {
        "+" | "+=" => BinaryOp::Add,
        "-" | "-=" => BinaryOp::Subtract,
        "*" | "*=" => BinaryOp::Multiply,
        "/" | "/=" => BinaryOp::Divide,
        "%" | "%=" => BinaryOp::Remainder,
        "<" => BinaryOp::Less,
        "<=" => BinaryOp::LessEqual,
        ">" => BinaryOp::Greater,
        ">=" => BinaryOp::GreaterEqual,
        "==" => BinaryOp::Equal,
        "!=" => BinaryOp::NotEqual,
        "&&" => BinaryOp::And,
        "||" => BinaryOp::Or,
        _ => unreachable!("checked operator"),
    }
}
fn unary_op(value: &str) -> UnaryOp {
    match value {
        "+" => UnaryOp::Plus,
        "-" => UnaryOp::Negate,
        "!" => UnaryOp::Not,
        _ => unreachable!("checked operator"),
    }
}
/// One step of a place: an indexed element (its position already evaluated and
/// captured) or a named field.
enum Projection {
    Index(Operand),
    Field(String),
}
struct LoopTargets {
    header: BlockId,
    exit: BlockId,
    had_break: bool,
    scope_start: usize,
}
struct Builder<'a> {
    function: Function,
    facts: &'a FunctionFacts,
    types: &'a [TypeFact],
    expression_ids: HashMap<usize, ExprId>,
    expressions: HashMap<ExprId, Option<Type>>,
    paths: HashMap<ExprId, PathTarget>,
    variants: HashMap<ExprId, VariantUse>,
    matches: HashMap<ExprId, &'a MatchFact>,
    current: Option<BlockId>,
    string_locals: Vec<LocalId>,
    loops: Vec<LoopTargets>,
    next_loan: u32,
    /// Values produced by `Load`: read-only provenance that must be copied
    /// before it can be used as an owned value.
    loaded: HashSet<u32>,
}
impl<'a> Builder<'a> {
    fn new(function: Function, facts: &'a FunctionFacts, types: &'a [TypeFact]) -> Self {
        let expression_ids = facts
            .expressions
            .iter()
            .map(|f| (f.node_addr, f.id))
            .collect();
        let expressions = facts
            .expressions
            .iter()
            .map(|f| (f.id, f.ty.clone()))
            .collect();
        let paths = facts
            .path_uses
            .iter()
            .map(|u| (u.expression, u.target))
            .collect();
        let variants = facts
            .variant_uses
            .iter()
            .map(|u| (u.expression, *u))
            .collect();
        let matches = facts.matches.iter().map(|m| (m.expression, m)).collect();
        let string_locals = function
            .parameter_locals
            .iter()
            .copied()
            .filter(|local| function.locals[local.0 as usize].ty == Type::String)
            .collect();
        Self {
            function,
            facts,
            types,
            expression_ids,
            expressions,
            paths,
            variants,
            matches,
            current: Some(BlockId(0)),
            string_locals,
            loops: Vec::new(),
            next_loan: 0,
            loaded: HashSet::new(),
        }
    }
    fn id(&self, expr: &Expr) -> ExprId {
        self.expression_ids[&(expr as *const Expr as usize)]
    }
    fn ty(&self, expr: &Expr) -> Option<Type> {
        self.expressions[&self.id(expr)].clone()
    }
    fn path(&self, expr: &Expr) -> PathTarget {
        self.paths[&self.id(expr)]
    }
    /// Whole-value destructuring. The initialiser is lowered once. Every field
    /// is then read out of that value with `Extract` (a primitive is copied, an
    /// aggregate field is moved by a bitwise copy) and assigned to its own
    /// local, in pattern order. The last extraction takes the whole value with
    /// `Consume`, so the ownership pass sees the source consumed exactly once
    /// (a source local becomes unavailable, BE001 on later use). A struct with no
    /// fields is consumed by a capture instead.
    fn lower_destructure(&mut self, fields: &[FieldPattern], value: &Expr) {
        let Some(source) = self.lower_expr(value) else {
            return;
        };
        let Some(Type::Struct(id)) = self.operand_type(source) else {
            unreachable!("checked destructuring source");
        };
        let types = self.types;
        let definition = &types[id.0 as usize];
        if fields.is_empty() {
            self.capture_consumed(source);
            return;
        }
        for (position, pattern) in fields.iter().enumerate() {
            let index = definition
                .fields
                .iter()
                .position(|field| field.name == pattern.field)
                .expect("checked destructuring field");
            let field_ty = definition.fields[index].ty.clone();
            let mut base = source;
            base.mode = if position + 1 == fields.len() {
                UseMode::Consume
            } else {
                UseMode::Read
            };
            let Some(extracted) = self.emit(
                pattern.span,
                InstructionKind::Extract {
                    base,
                    field: index as u32,
                },
                Some(field_ty),
            ) else {
                return;
            };
            let target = self.local_at(pattern as *const FieldPattern as usize);
            self.initialize_local(target, consume(extracted), pattern.span);
        }
    }
    fn capture_consumed(&mut self, source: Operand) {
        if matches!(source.source, Source::Local(_)) {
            self.emit(
                source.span.unwrap_or(self.function.span),
                InstructionKind::Capture(consume(source)),
                self.operand_type(source),
            );
        }
    }
    fn local_at(&self, addr: usize) -> LocalId {
        self.facts
            .locals
            .iter()
            .find(|l| l.node_addr == addr)
            .expect("checked binding fact")
            .id
    }
    fn local(&self, statement: &Statement) -> LocalId {
        self.facts
            .locals
            .iter()
            .find(|l| l.node_addr == statement as *const Statement as usize)
            .expect("checked binding fact")
            .id
    }
    fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.function.blocks.len() as u32);
        self.function.blocks.push(IrBlock {
            parameters: Vec::new(),
            instructions: Vec::new(),
            terminator: Terminator {
                span: None,
                kind: TerminatorKind::Unreachable,
            },
        });
        id
    }
    fn new_value(&mut self, ty: Type) -> ValueId {
        let id = ValueId(self.function.values.len() as u32);
        self.function.values.push(ty);
        id
    }
    fn emit(&mut self, span: Span, kind: InstructionKind, ty: Option<Type>) -> Option<Operand> {
        let current = self.current?;
        let output = ty.map(|ty| self.new_value(ty));
        self.function.blocks[current.0 as usize]
            .instructions
            .push(Instruction {
                span: Some(span),
                output,
                kind,
            });
        output.map(|id| op(Source::Value(id), span))
    }
    fn constant(&mut self, span: Span, value: Constant, ty: Type) -> Option<Operand> {
        self.emit(span, InstructionKind::Constant(value), Some(ty))
    }
    fn unit(&mut self, span: Span) -> Option<Operand> {
        self.constant(span, Constant::Unit, Type::Primitive(Primitive::Unit))
    }
    fn operand_type(&self, operand: Operand) -> Option<Type> {
        match operand.source {
            Source::Local(id) => Some(self.function.locals[id.0 as usize].ty.clone()),
            Source::Value(id) => Some(self.function.values[id.0 as usize].clone()),
            Source::Function(_) => None,
        }
    }
    fn scalar(&mut self, mut operand: Operand) -> Option<Operand> {
        if let Some(Type::Reference { access, inner }) = self.operand_type(operand) {
            operand.mode = access_mode(access);
            let span = operand.span.unwrap_or(self.function.span);
            self.load(operand, *inner, span)
        } else {
            Some(operand)
        }
    }
    fn load(&mut self, reference: Operand, inner: Type, span: Span) -> Option<Operand> {
        let value = self.emit(span, InstructionKind::Load { reference }, Some(inner))?;
        if let Source::Value(id) = value.source {
            self.loaded.insert(id.0);
        }
        Some(value)
    }
    /// Operand for an owned position. Primitive locals and loaded primitives
    /// (read-only provenance) are copied implicitly into a fresh owned value
    /// with an IR `Copy`, which only reads its source. Other temporaries and
    /// aggregates are consumed (moved).
    fn owned(&mut self, operand: Operand) -> Option<Operand> {
        let primitive = matches!(
            self.operand_type(operand),
            Some(Type::Primitive(kind)) if kind != Primitive::Unit
        );
        match operand.source {
            Source::Local(_) if primitive => self.copy_of(operand),
            Source::Value(id) if primitive && self.loaded.contains(&id.0) => self.copy_of(operand),
            _ => Some(consume(operand)),
        }
    }
    fn copy_of(&mut self, operand: Operand) -> Option<Operand> {
        let ty = self.operand_type(operand);
        let span = operand.span.unwrap_or(self.function.span);
        let copy = self.emit(
            span,
            InstructionKind::Copy {
                source: read(operand),
            },
            ty,
        )?;
        Some(consume(copy))
    }
    /// `owned` for a destination of type `target`: a reference read into a
    /// non-reference destination is loaded first (the checker only allows this
    /// for primitive referents).
    fn owned_to(&mut self, operand: Operand, target: &Type) -> Option<Operand> {
        let operand = if matches!(target, Type::Reference { .. }) {
            operand
        } else {
            self.scalar(operand)?
        };
        self.owned(operand)
    }
    /// `owned_to` followed by a capture, so locals are read in source order.
    fn owned_captured(&mut self, operand: Operand, target: &Type) -> Option<Operand> {
        let operand = self.owned_to(operand, target)?;
        Some(consume(self.capture(operand)?))
    }
    fn borrow(&mut self, mut owner: Operand, access: Access) -> Option<Operand> {
        let ty = self.operand_type(owner).expect("checked borrow source");
        let inner = match ty {
            Type::Reference { inner, .. } => inner,
            ty => Box::new(ty),
        };
        owner.mode = access_mode(access);
        let loan = LoanId(self.next_loan);
        self.next_loan += 1;
        self.emit(
            owner.span.unwrap_or(self.function.span),
            InstructionKind::Borrow {
                loan,
                owner,
                access,
            },
            Some(Type::Reference { access, inner }),
        )
    }
    fn capture(&mut self, operand: Operand) -> Option<Operand> {
        if !matches!(operand.source, Source::Local(_)) {
            return Some(operand);
        }
        let ty = match operand.source {
            Source::Local(local) => self.function.locals[local.0 as usize].ty.clone(),
            _ => unreachable!(),
        };
        let span = operand.span.unwrap_or(self.function.span);
        self.emit(
            span,
            InstructionKind::Capture(if matches!(ty, Type::Reference { .. }) {
                consume(operand)
            } else {
                operand
            }),
            Some(ty),
        )
    }
    fn finish(&mut self, block: BlockId, kind: TerminatorKind, span: Option<Span>) {
        self.function.blocks[block.0 as usize].terminator = Terminator { span, kind };
        if self.current == Some(block) {
            self.current = None;
        }
    }
    fn goto(&mut self, target: BlockId, arguments: Vec<Operand>, span: Span) {
        if let Some(current) = self.current {
            self.finish(
                current,
                TerminatorKind::Goto(Edge { target, arguments }),
                Some(span),
            );
        }
    }
    fn initialize_local(&mut self, local: LocalId, value: Operand, span: Span) {
        self.emit(
            span,
            InstructionKind::Assign {
                target: local,
                value,
                initialize: true,
            },
            None,
        );
        if self.function.locals[local.0 as usize].ty == Type::String {
            self.string_locals.push(local);
        }
    }

    fn lower_concat_initializer(
        &mut self,
        binding: &Statement,
        left: &Expr,
        right: &Expr,
        span: Span,
    ) {
        let Some(left) = self
            .lower_expr(left)
            .and_then(|value| self.borrow(value, Access::Borrow))
        else {
            return;
        };
        let Some(right) = self
            .lower_expr(right)
            .and_then(|value| self.borrow(value, Access::Borrow))
        else {
            return;
        };
        let target = self.local(binding);
        self.emit(
            span,
            InstructionKind::InitConcatString {
                target,
                strings: [read(left), read(right)],
            },
            None,
        );
        self.string_locals.push(target);
    }

    fn end_string_locals(&mut self, from: usize, span: Span) {
        for index in (from..self.string_locals.len()).rev() {
            let local = self.string_locals[index];
            self.emit(span, InstructionKind::EndStringLocal { local }, None);
        }
    }

    fn preserve_scope_result(&mut self, value: Operand, from: usize) -> Option<Operand> {
        if matches!(value.source, Source::Local(local) if self.string_locals[from..].contains(&local))
        {
            self.capture(consume(value))
        } else {
            Some(value)
        }
    }

    fn return_from_body(&mut self, returned: Option<Operand>, span: Span) {
        if let Some(current) = self.current {
            let returned = returned.and_then(|value| self.preserve_scope_result(value, 0));
            self.end_string_locals(0, span);
            self.finish(current, TerminatorKind::Return(returned), Some(span));
        }
    }

    fn lower_body(&mut self, body: &Block) {
        let value = self.lower_block(body);
        let result = self.function.signature.result.as_ref().clone();
        let returned = if result == Type::Primitive(Primitive::Unit) {
            None
        } else {
            value.and_then(|value| self.owned_to(value, &result))
        };
        self.return_from_body(returned, body.span);
    }

    fn lower_block(&mut self, block: &Block) -> Option<Operand> {
        let scope_start = self.string_locals.len();
        for statement in &block.statements {
            if self.current.is_none() {
                break;
            }
            match &statement.kind {
                StatementKind::Binding { value, .. } => {
                    if let ExprKind::Call { callee, arguments } = &value.kind {
                        if let ExprKind::Field { base, name } = &callee.kind {
                            if name == "concat" {
                                self.lower_concat_initializer(
                                    statement,
                                    base,
                                    &arguments[0],
                                    value.span,
                                );
                                continue;
                            }
                        }
                    }
                    let rhs = self.lower_expr(value);
                    if let Some(rhs) = rhs {
                        let target = self.local(statement);
                        let ty = self.function.locals[target.0 as usize].ty.clone();
                        if let Some(rhs) = self.owned_to(rhs, &ty) {
                            self.initialize_local(target, rhs, statement.span);
                        }
                    }
                }
                StatementKind::Destructure { fields, value, .. } => {
                    self.lower_destructure(fields, value);
                }
                StatementKind::Assign {
                    target,
                    operator,
                    value,
                } => {
                    if matches!(target.kind, ExprKind::Index { .. } | ExprKind::Field { .. }) {
                        self.lower_place_assign(statement.span, target, operator, value);
                        continue;
                    }
                    let PathTarget::Local(local) = self.path(target) else {
                        unreachable!("checked assignment")
                    };
                    let previous = (operator != "=").then(|| op(Source::Local(local), target.span));
                    let previous = previous
                        .and_then(|operand| self.scalar(operand))
                        .and_then(|operand| self.capture(operand));
                    let rhs = self
                        .lower_expr(value)
                        .and_then(|operand| self.scalar(operand));
                    if let Some(rhs) = rhs {
                        let assigned = if operator == "=" {
                            rhs
                        } else {
                            let ty = match self.function.locals[local.0 as usize].ty.clone() {
                                Type::Reference { inner, .. } => *inner,
                                ty => ty,
                            };
                            self.emit(
                                statement.span,
                                InstructionKind::Binary {
                                    op: binary_op(operator),
                                    left: read(previous.expect("compound old value captured")),
                                    right: read(rhs),
                                },
                                Some(ty),
                            )
                            .expect("live compound result")
                        };
                        let Some(assigned) = self.owned(assigned) else {
                            continue;
                        };
                        let kind = if matches!(
                            self.function.locals[local.0 as usize].ty,
                            Type::Reference { .. }
                        ) {
                            let mut reference = op(Source::Local(local), target.span);
                            reference.mode = UseMode::Share;
                            InstructionKind::Store {
                                reference,
                                value: assigned,
                            }
                        } else {
                            InstructionKind::Assign {
                                target: local,
                                value: assigned,
                                initialize: false,
                            }
                        };
                        self.emit(statement.span, kind, None);
                    }
                }
                StatementKind::Expression(expr) => {
                    self.lower_expr(expr);
                }
                StatementKind::Return(value) => {
                    let returned = match value {
                        Some(expr) => {
                            let result = self.function.signature.result.as_ref().clone();
                            self.lower_expr(expr)
                                .and_then(|value| self.owned_to(value, &result))
                        }
                        None => None,
                    };
                    self.return_from_body(returned, statement.span);
                }
                StatementKind::Loop(body) => self.lower_loop(body, statement.span),
                StatementKind::Break => {
                    let loop_targets = self.loops.last_mut().expect("checked break");
                    loop_targets.had_break = true;
                    let (target, start) = (loop_targets.exit, loop_targets.scope_start);
                    self.end_string_locals(start, statement.span);
                    self.goto(target, Vec::new(), statement.span);
                }
                StatementKind::Continue => {
                    let loop_targets = self.loops.last().expect("checked continue");
                    let (target, start) = (loop_targets.header, loop_targets.scope_start);
                    self.end_string_locals(start, statement.span);
                    self.goto(target, Vec::new(), statement.span);
                }
            }
        }
        let value = if self.current.is_some() {
            match block.tail.as_deref() {
                Some(tail) => self.lower_expr(tail),
                None => self.unit(block.span),
            }
        } else {
            None
        };
        let value = value.and_then(|value| self.preserve_scope_result(value, scope_start));
        if self.current.is_some() {
            self.end_string_locals(scope_start, block.span);
        }
        self.string_locals.truncate(scope_start);
        value
    }
    /// Address one element of an array operand. The bounds check is part of the
    /// instruction; the result is a reference with the requested access.
    fn element_addr(
        &mut self,
        mut array: Operand,
        position: Operand,
        access: Access,
        span: Span,
    ) -> Option<Operand> {
        let element = self.array_element(array);
        let loan = LoanId(self.next_loan);
        self.next_loan += 1;
        array.mode = access_mode(access);
        let mut reference = self.emit(
            span,
            InstructionKind::ElementAddr {
                loan,
                base: array,
                index: read(position),
                access,
            },
            Some(Type::Reference {
                access,
                inner: element,
            }),
        )?;
        reference.mode = access_mode(access);
        Some(reference)
    }
    /// Element type of an array owner or of a reference to an array.
    fn array_element(&self, array: Operand) -> Box<Type> {
        match self.operand_type(array) {
            Some(Type::Array { element, .. }) => element,
            Some(Type::Reference { inner, .. }) => match *inner {
                Type::Array { element, .. } => element,
                _ => unreachable!("checked array index base"),
            },
            _ => unreachable!("checked array index base"),
        }
    }
    /// Evaluate the root and every index of a projection chain such as
    /// `a[i].pts[j].x` left to right, each index captured at its evaluation
    /// point. No address is formed yet, so index effects precede any bounds
    /// check and the right-hand side of a write.
    fn lower_place(&mut self, expr: &Expr) -> Option<(Operand, Vec<Projection>)> {
        let (base, step) = match &expr.kind {
            ExprKind::Index { base, .. } => (base, None),
            ExprKind::Field { base, name } => (base, Some(name)),
            _ => unreachable!("checked projection place"),
        };
        let (root, mut projections) =
            if matches!(base.kind, ExprKind::Index { .. } | ExprKind::Field { .. }) {
                self.lower_place(base)?
            } else {
                (self.lower_expr(base)?, Vec::new())
            };
        match (&expr.kind, step) {
            (ExprKind::Index { index, .. }, _) => {
                let position = self.lower_expr(index)?;
                let position = self.scalar(position)?;
                projections.push(Projection::Index(self.capture(position)?));
            }
            (_, Some(name)) => projections.push(Projection::Field(name.clone())),
            _ => unreachable!(),
        }
        Some((root, projections))
    }
    /// Chain of checked element and field addresses from `root` through
    /// `projections`. Every level carries `access`, so a write needs `Share`
    /// references down to the target.
    fn address_chain(
        &mut self,
        root: Operand,
        projections: &[Projection],
        access: Access,
        span: Span,
    ) -> Option<Operand> {
        let mut current = root;
        for projection in projections {
            current = match projection {
                Projection::Index(position) => {
                    self.element_addr(current, *position, access, span)?
                }
                Projection::Field(name) => self.field_addr(current, name, access, span)?,
            };
        }
        Some(current)
    }
    fn load_element(&mut self, reference: Operand, span: Span) -> Option<Operand> {
        let Some(Type::Reference { inner, .. }) = self.operand_type(reference) else {
            unreachable!("element address is a reference")
        };
        self.load(reference, *inner, span)
    }
    /// `a[i] = v`, `p.x = v`, `a[i].pts[j] += v` and every other projection
    /// chain, plain or compound. The root and every index are evaluated and
    /// captured first, then the right-hand side; the checked address chain and
    /// the store are adjacent, so a bounds trap fires after the right-hand
    /// side's effects. A compound write reads the place first. A
    /// whole-aggregate target (`l.a = P { .. }`, `m[i] = [..]`) stores the
    /// consumed aggregate with a memory copy.
    fn lower_place_assign(
        &mut self,
        span: Span,
        target: &Expr,
        operator: &str,
        value: &Expr,
    ) -> Option<()> {
        let (array, positions) = self.lower_place(target)?;
        let previous = if operator == "=" {
            None
        } else {
            let reference = self.address_chain(array, &positions, Access::Borrow, span)?;
            Some(self.load_element(reference, span)?)
        };
        let rhs = self.lower_expr(value)?;
        let rhs = self.scalar(rhs)?;
        let assigned = match previous {
            None => rhs,
            Some(previous) => {
                let element = self
                    .operand_type(previous)
                    .expect("compound element read is a value");
                self.emit(
                    span,
                    InstructionKind::Binary {
                        op: binary_op(operator),
                        left: read(previous),
                        right: read(rhs),
                    },
                    Some(element),
                )?
            }
        };
        let assigned = self.owned(assigned)?;
        let reference = self.address_chain(array, &positions, Access::Share, span)?;
        self.emit(
            span,
            InstructionKind::Store {
                reference,
                value: assigned,
            },
            None,
        );
        Some(())
    }
    /// Address one field of a struct owner or of a reference to a struct. The
    /// result is a reference with the requested access.
    fn field_addr(
        &mut self,
        mut owner: Operand,
        field_name: &str,
        access: Access,
        span: Span,
    ) -> Option<Operand> {
        let id = match self.operand_type(owner) {
            Some(Type::Struct(id)) => id,
            Some(Type::Reference { inner, .. }) => match *inner {
                Type::Struct(id) => id,
                _ => unreachable!("checked struct field base"),
            },
            _ => unreachable!("checked struct field base"),
        };
        let definition = &self.types[id.0 as usize];
        let index = definition
            .fields
            .iter()
            .position(|field| field.name == field_name)
            .expect("checked struct field");
        let field_type = definition.fields[index].ty.clone();
        let loan = LoanId(self.next_loan);
        self.next_loan += 1;
        owner.mode = access_mode(access);
        let mut reference = self.emit(
            span,
            InstructionKind::FieldAddr {
                loan,
                base: owner,
                field: index as u32,
                access,
            },
            Some(Type::Reference {
                access,
                inner: Box::new(field_type),
            }),
        )?;
        reference.mode = access_mode(access);
        Some(reference)
    }
    fn hidden_local(&mut self, name: &str, ty: Type, span: Span) -> LocalId {
        let id = LocalId(self.function.locals.len() as u32);
        self.function.locals.push(Local {
            name: name.into(),
            ty,
            mutable: true,
            span,
        });
        id
    }
    /// `[expr; N]`. Zero evaluates nothing and one evaluates once without a
    /// loop. Larger counts always lower to a loop over a hidden zeroed
    /// accumulator and a hidden counter, so the IR size does not depend on N and
    /// an owned element expression is a repeated move that ownership rejects.
    fn lower_repeat(&mut self, expr: &Expr, value: &Expr) -> Option<Operand> {
        let ty = self.ty(expr).expect("checked repeat type");
        let Type::Array {
            len,
            element: element_ty,
        } = ty.clone()
        else {
            unreachable!("checked repeat type")
        };
        let span = expr.span;
        if len == 0 {
            return self.emit(
                span,
                InstructionKind::ArrayNew {
                    init: ArrayInit::Zeroed,
                },
                Some(ty),
            );
        }
        if len == 1 {
            let element = self.lower_expr(value)?;
            let element = self.owned_captured(element, &element_ty)?;
            return self.emit(
                span,
                InstructionKind::ArrayNew {
                    init: ArrayInit::Elements(vec![element]),
                },
                Some(ty),
            );
        }
        let u32_ty = Type::Primitive(Primitive::U32);
        let accumulator = self.hidden_local("repeat array", ty.clone(), span);
        let counter = self.hidden_local("repeat index", u32_ty.clone(), span);
        let zeroed = self.emit(
            span,
            InstructionKind::ArrayNew {
                init: ArrayInit::Zeroed,
            },
            Some(ty.clone()),
        )?;
        self.emit(
            span,
            InstructionKind::Assign {
                target: accumulator,
                value: consume(zeroed),
                initialize: true,
            },
            None,
        );
        let start = self.constant(span, Constant::Integer("0".into()), u32_ty.clone())?;
        self.emit(
            span,
            InstructionKind::Assign {
                target: counter,
                value: consume(start),
                initialize: true,
            },
            None,
        );
        let header = self.new_block();
        let body = self.new_block();
        let exit = self.new_block();
        self.goto(header, Vec::new(), span);
        self.current = Some(header);
        let current_count = self.capture(op(Source::Local(counter), span))?;
        let limit = self.constant(span, Constant::Integer(len.to_string()), u32_ty.clone())?;
        let more = self.emit(
            span,
            InstructionKind::Binary {
                op: BinaryOp::Less,
                left: read(current_count),
                right: read(limit),
            },
            Some(Type::Primitive(Primitive::Bool)),
        )?;
        self.finish(
            header,
            TerminatorKind::Branch {
                condition: read(more),
                then_edge: Edge {
                    target: body,
                    arguments: Vec::new(),
                },
                else_edge: Edge {
                    target: exit,
                    arguments: Vec::new(),
                },
            },
            Some(span),
        );
        self.current = Some(body);
        let produced = self
            .lower_expr(value)
            .and_then(|operand| self.owned_to(operand, &element_ty))
            .and_then(|operand| self.capture(operand));
        if let Some(produced) = produced {
            let position = self.capture(op(Source::Local(counter), span))?;
            let reference = self.element_addr(
                op(Source::Local(accumulator), span),
                position,
                Access::Share,
                span,
            )?;
            self.emit(
                span,
                InstructionKind::Store {
                    reference,
                    value: consume(produced),
                },
                None,
            );
            let current_count = self.capture(op(Source::Local(counter), span))?;
            let one = self.constant(span, Constant::Integer("1".into()), u32_ty.clone())?;
            let next = self.emit(
                span,
                InstructionKind::Binary {
                    op: BinaryOp::Add,
                    left: read(current_count),
                    right: read(one),
                },
                Some(u32_ty),
            )?;
            self.emit(
                span,
                InstructionKind::Assign {
                    target: counter,
                    value: consume(next),
                    initialize: false,
                },
                None,
            );
            self.goto(header, Vec::new(), span);
        }
        self.current = Some(exit);
        self.emit(
            span,
            InstructionKind::Capture(consume(op(Source::Local(accumulator), span))),
            Some(ty),
        )
    }
    fn lower_loop(&mut self, body: &Block, span: Span) {
        let header = self.new_block();
        let exit = self.new_block();
        self.goto(header, Vec::new(), span);
        self.current = Some(header);
        self.loops.push(LoopTargets {
            header,
            exit,
            had_break: false,
            scope_start: self.string_locals.len(),
        });
        self.lower_block(body);
        if self.current.is_some() {
            self.goto(header, Vec::new(), body.span);
        }
        let had_break = self.loops.pop().unwrap().had_break;
        self.current = had_break.then_some(exit);
    }
    fn lower_expr(&mut self, expr: &Expr) -> Option<Operand> {
        self.current?;
        match &expr.kind {
            ExprKind::Array(elements) => {
                let Some(Type::Array {
                    element: element_ty,
                    ..
                }) = self.ty(expr)
                else {
                    unreachable!("checked array literal type")
                };
                let mut operands = Vec::with_capacity(elements.len());
                for element in elements {
                    let value = self.lower_expr(element)?;
                    // Capture locals now so every element is read in source order.
                    operands.push(self.owned_captured(value, &element_ty)?);
                }
                self.emit(
                    expr.span,
                    InstructionKind::ArrayNew {
                        init: ArrayInit::Elements(operands),
                    },
                    self.ty(expr),
                )
            }
            ExprKind::Index { .. } | ExprKind::Field { .. } => {
                let (root, projections) = self.lower_place(expr)?;
                let reference =
                    self.address_chain(root, &projections, Access::Borrow, expr.span)?;
                self.load_element(reference, expr.span)
            }
            ExprKind::RepeatArray { value, .. } => self.lower_repeat(expr, value),
            ExprKind::Number(raw) => {
                let ty = self.ty(expr).expect("checked number type");
                let value = if raw.contains(['.', 'e', 'E']) {
                    Constant::Float(raw.clone())
                } else {
                    Constant::Integer(raw.clone())
                };
                self.constant(expr.span, value, ty)
            }
            ExprKind::StringLiteral(text) => {
                self.constant(expr.span, Constant::String(text.clone()), Type::String)
            }
            ExprKind::Bool(value) => self.constant(
                expr.span,
                Constant::Bool(*value),
                Type::Primitive(Primitive::Bool),
            ),
            ExprKind::Path(_) if self.variants.contains_key(&self.id(expr)) => {
                self.lower_variant(expr, &[])
            }
            ExprKind::Path(_) => {
                let source = match self.path(expr) {
                    PathTarget::Local(id) => Source::Local(id),
                    PathTarget::Function(id) => Source::Function(id),
                };
                Some(op(source, expr.span))
            }
            ExprKind::Unary { operator, operand } => {
                // Signed minimum is a single negative constant: its positive
                // literal cannot be represented in the target signed type.
                if operator == "-"
                    && self
                        .facts
                        .expressions
                        .iter()
                        .all(|f| f.node_addr != operand.as_ref() as *const Expr as usize)
                {
                    if let ExprKind::Number(raw) = &operand.kind {
                        return self.constant(
                            expr.span,
                            Constant::Integer(format!("-{raw}")),
                            self.ty(expr).expect("checked negative type"),
                        );
                    }
                }
                let input = self.lower_expr(operand)?;
                let input = self.scalar(input)?;
                self.emit(
                    expr.span,
                    InstructionKind::Unary {
                        op: unary_op(operator),
                        operand: read(input),
                    },
                    self.ty(expr),
                )
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } if operator == "&&" || operator == "||" => {
                self.lower_short_circuit(expr, operator, left, right)
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                let lhs = self.lower_expr(left)?;
                let lhs = self.scalar(lhs)?;
                let lhs = self.capture(lhs)?;
                let rhs = self.lower_expr(right)?;
                let rhs = self.scalar(rhs)?;
                self.emit(
                    expr.span,
                    InstructionKind::Binary {
                        op: binary_op(operator),
                        left: read(lhs),
                        right: read(rhs),
                    },
                    self.ty(expr),
                )
            }
            ExprKind::Call { arguments, .. } if self.variants.contains_key(&self.id(expr)) => {
                self.lower_variant(expr, arguments)
            }
            ExprKind::Call { callee, arguments } => {
                if let ExprKind::Field { base, name } = &callee.kind {
                    if name == "copy" {
                        // Read the receiver (loading through a reference or
                        // element address) and produce a fresh owned value.
                        let source = self.lower_expr(base)?;
                        let source = self.scalar(source)?;
                        return self.emit(
                            expr.span,
                            InstructionKind::Copy {
                                source: read(source),
                            },
                            self.ty(expr),
                        );
                    }
                    if matches!(name.as_str(), "is_char_boundary" | "byte_at" | "scalar_at") {
                        let receiver = self.lower_expr(base)?;
                        // Keep the receiver loan live while evaluating the offset.
                        let source = self.borrow(receiver, Access::Borrow)?;
                        let offset = self.lower_expr(&arguments[0])?;
                        let offset = read(self.scalar(offset)?);
                        let source = read(source);
                        let instruction = match name.as_str() {
                            "byte_at" => InstructionKind::StringByteAt { source, offset },
                            "scalar_at" => InstructionKind::StringScalarAt { source, offset },
                            _ => InstructionKind::StringIsCharBoundary { source, offset },
                        };
                        return self.emit(expr.span, instruction, self.ty(expr));
                    }
                    if name == "len" {
                        let source = self.lower_expr(base)?;
                        return self.emit(
                            expr.span,
                            InstructionKind::StringLen {
                                source: read(source),
                            },
                            self.ty(expr),
                        );
                    }
                    let access = match name.as_str() {
                        "borrow" => Access::Borrow,
                        "share" => Access::Share,
                        _ => unreachable!("checked conversion"),
                    };
                    if matches!(base.kind, ExprKind::Index { .. } | ExprKind::Field { .. }) {
                        // A row, element or field that is itself an aggregate: the
                        // chain of addresses is the reference, with `access` on
                        // every level.
                        let (root, projections) = self.lower_place(base)?;
                        return self.address_chain(root, &projections, access, expr.span);
                    }
                    let owner = self.lower_expr(base)?;
                    return self.borrow(owner, access);
                }
                let Type::Function(signature) = self.ty(callee).expect("checked callee") else {
                    unreachable!("checked function")
                };
                let callee = self.lower_expr(callee)?;
                let callee = self.capture(callee)?;
                let mut args = Vec::new();
                for (index, (argument, parameter)) in
                    arguments.iter().zip(&signature.parameters).enumerate()
                {
                    let argument = self.lower_expr(argument)?;
                    if parameter.access == Access::Owned {
                        if parameter.ty == Type::String && index + 1 == arguments.len() {
                            // No later argument can exit before this move reaches the call.
                            args.push(self.owned_to(argument, &parameter.ty)?);
                        } else {
                            args.push(self.owned_captured(argument, &parameter.ty)?);
                        }
                    } else {
                        // Keep the original pointee and loan. Only the call
                        // boundary can view an error reference as its ancestor.
                        let mut argument = self.borrow(argument, parameter.access)?;
                        argument.mode = access_mode(parameter.access);
                        args.push(argument);
                    }
                }
                self.emit(
                    expr.span,
                    InstructionKind::Call {
                        callee: read(callee),
                        arguments: args,
                    },
                    self.ty(expr),
                )
            }
            ExprKind::Struct { fields, .. } => {
                let Some(Type::Struct(id)) = self.ty(expr) else {
                    unreachable!("checked struct literal type")
                };
                let types = self.types;
                let definition = &types[id.0 as usize];
                // Evaluate and capture every initialiser in source order, then
                // hand them to StructNew in declaration order.
                let mut slots: Vec<Option<Operand>> = vec![None; definition.fields.len()];
                for init in fields {
                    let value = self.lower_expr(&init.value)?;
                    let index = definition
                        .fields
                        .iter()
                        .position(|field| field.name == init.name)
                        .expect("checked struct field");
                    let operand =
                        self.owned_captured(value, &definition.fields[index].ty.clone())?;
                    slots[index] = Some(operand);
                }
                self.emit(
                    expr.span,
                    InstructionKind::StructNew {
                        ty: id,
                        fields: slots
                            .into_iter()
                            .map(|slot| slot.expect("checked complete struct literal"))
                            .collect(),
                    },
                    Some(Type::Struct(id)),
                )
            }
            ExprKind::Block(block) => self.lower_block(block),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => self.lower_if(expr, condition, then_branch, else_branch.as_deref()),
            ExprKind::Match { scrutinee, arms } => self.lower_match(expr, scrutinee, arms),
        }
    }
    /// `match` on an owned enum. The scrutinee is consumed once, into a hidden
    /// local, so every arm reads the same cell. The tag is read once and a
    /// `Switch` dispatches to one block per arm; an arm moves out the payloads
    /// it binds with `VariantExtract` (the last one consumes the cell) and
    /// joins its value like an `if` branch.
    fn lower_match(&mut self, expr: &Expr, scrutinee: &Expr, arms: &[MatchArm]) -> Option<Operand> {
        let fact = self.matches[&self.id(expr)];
        let span = scrutinee.span;
        // `cell` is the hidden owner of a consuming match, or the reference to
        // the matched place of a borrowing one.
        let (cell, enum_id, tag) = if fact.borrowed {
            let reference = if matches!(
                scrutinee.kind,
                ExprKind::Index { .. } | ExprKind::Field { .. }
            ) {
                let (root, projections) = self.lower_place(scrutinee)?;
                self.address_chain(root, &projections, Access::Borrow, span)?
            } else {
                self.lower_expr(scrutinee)?
            };
            let Some(Type::Reference { access, inner }) = self.operand_type(reference) else {
                unreachable!("checked borrowing match scrutinee")
            };
            let Type::Enum(enum_id) = *inner else {
                unreachable!("checked borrowing match scrutinee")
            };
            let cell = match reference.source {
                Source::Local(local) => local,
                _ => {
                    let local = self.hidden_local(
                        "match scrutinee",
                        Type::Reference {
                            access,
                            inner: Box::new(Type::Enum(enum_id)),
                        },
                        span,
                    );
                    self.emit(
                        span,
                        InstructionKind::Assign {
                            target: local,
                            value: consume(reference),
                            initialize: true,
                        },
                        None,
                    );
                    local
                }
            };
            let mut base = op(Source::Local(cell), span);
            base.mode = UseMode::Borrow;
            let tag = self.emit(
                span,
                InstructionKind::EnumTag { base },
                Some(Type::Primitive(Primitive::U32)),
            )?;
            (cell, enum_id, tag)
        } else {
            let source = self.lower_expr(scrutinee)?;
            let Some(Type::Enum(enum_id)) = self.operand_type(source) else {
                unreachable!("checked match scrutinee")
            };
            let cell = self.hidden_local("match scrutinee", Type::Enum(enum_id), span);
            let moved = self.owned(source)?;
            self.emit(
                span,
                InstructionKind::Assign {
                    target: cell,
                    value: moved,
                    initialize: true,
                },
                None,
            );
            let tag = self.emit(
                span,
                InstructionKind::EnumTag {
                    base: read(op(Source::Local(cell), span)),
                },
                Some(Type::Primitive(Primitive::U32)),
            )?;
            (cell, enum_id, tag)
        };
        let types = self.types;
        let definition = &types[enum_id.0 as usize];
        let join_id = self.new_block();
        let parameter = self.ty(expr).map(|ty| {
            let id = self.new_value(ty);
            self.function.blocks[join_id.0 as usize].parameters.push(id);
            id
        });
        let mut targets = Vec::new();
        let mut default = None;
        let mut arm_blocks = Vec::new();
        for arm_fact in &fact.arms {
            let block = self.new_block();
            arm_blocks.push(block);
            let edge = Edge {
                target: block,
                arguments: Vec::new(),
            };
            match arm_fact.variant {
                Some(variant) => targets.push((variant, edge)),
                None => default = Some(edge),
            }
        }
        let current = self.current.expect("scrutinee completed");
        self.finish(
            current,
            TerminatorKind::Switch {
                tag: read(tag),
                ty: enum_id,
                targets,
                default,
            },
            Some(span),
        );
        let mut reaches = false;
        for ((arm, arm_fact), block) in arms.iter().zip(&fact.arms).zip(arm_blocks) {
            let scope_start = self.string_locals.len();
            self.current = Some(block);
            if let Some(variant) = arm_fact.variant {
                let payload = &definition.variants[variant as usize].payload;
                let bound: Vec<(usize, LocalId)> = arm_fact
                    .bindings
                    .iter()
                    .enumerate()
                    .filter_map(|(index, local)| local.map(|local| (index, local)))
                    .collect();
                if fact.borrowed {
                    for (index, local) in &bound {
                        let ty = payload[*index].clone();
                        let loan = LoanId(self.next_loan);
                        self.next_loan += 1;
                        let mut base = op(Source::Local(cell), arm.pattern.span);
                        base.mode = UseMode::Borrow;
                        let mut reference = self.emit(
                            arm.pattern.span,
                            InstructionKind::VariantAddr {
                                loan,
                                base,
                                variant,
                                field: *index as u32,
                                access: Access::Borrow,
                            },
                            Some(Type::Reference {
                                access: Access::Borrow,
                                inner: Box::new(ty.clone()),
                            }),
                        )?;
                        reference.mode = UseMode::Borrow;
                        let value = if matches!(ty, Type::Primitive(_)) {
                            let loaded = self.load_element(reference, arm.pattern.span)?;
                            self.owned(loaded)?
                        } else {
                            consume(reference)
                        };
                        self.emit(
                            arm.pattern.span,
                            InstructionKind::Assign {
                                target: *local,
                                value,
                                initialize: true,
                            },
                            None,
                        );
                    }
                }
                for (position, (index, local)) in bound.iter().enumerate() {
                    if fact.borrowed {
                        break; // borrowing bindings were addressed above
                    }
                    let mut base = op(Source::Local(cell), arm.pattern.span);
                    base.mode = if position + 1 == bound.len() {
                        UseMode::Consume
                    } else {
                        UseMode::Read
                    };
                    let extracted = self.emit(
                        arm.pattern.span,
                        InstructionKind::VariantExtract {
                            base,
                            variant,
                            field: *index as u32,
                        },
                        Some(payload[*index].clone()),
                    )?;
                    self.initialize_local(*local, consume(extracted), arm.pattern.span);
                }
            }
            if let Some(value) = self.lower_expr(&arm.body) {
                if let Some(value) = self.preserve_scope_result(value, scope_start) {
                    self.end_string_locals(scope_start, arm.body.span);
                    self.join(join_id, value, arm.body.span);
                    reaches = true;
                }
            }
            self.string_locals.truncate(scope_start);
        }
        self.current = reaches.then_some(join_id);
        parameter.map(|id| op(Source::Value(id), expr.span))
    }
    /// An enum variant construction. Payload arguments are evaluated and
    /// captured left to right, then handed to `EnumNew` in declaration order.
    fn lower_variant(&mut self, expr: &Expr, arguments: &[Expr]) -> Option<Operand> {
        let VariantUse {
            enum_id, variant, ..
        } = self.variants[&self.id(expr)];
        let Some(id) = enum_id else {
            // Inference stopped at a diverging payload, so there is no enum to build.
            for argument in arguments {
                self.lower_expr(argument)?;
            }
            unreachable!("variant without an inferred type must diverge");
        };
        let types = self.types;
        let declared = &types[id.0 as usize].variants[variant as usize];
        let mut payload = Vec::with_capacity(arguments.len());
        for (argument, ty) in arguments.iter().zip(&declared.payload) {
            let value = self.lower_expr(argument)?;
            payload.push(self.owned_captured(value, ty)?);
        }
        self.emit(
            expr.span,
            InstructionKind::EnumNew {
                ty: id,
                variant,
                payload,
            },
            Some(Type::Enum(id)),
        )
    }
    fn join(&mut self, target: BlockId, value: Operand, span: Span) {
        let Some(value) = self.owned(value) else {
            return;
        };
        self.goto(target, vec![value], span);
    }
    fn lower_if(
        &mut self,
        expr: &Expr,
        condition: &Expr,
        then_branch: &Block,
        else_branch: Option<&Expr>,
    ) -> Option<Operand> {
        let condition_value = self.lower_expr(condition)?;
        let condition_value = self.scalar(condition_value)?;
        let then_id = self.new_block();
        let else_id = self.new_block();
        let join_id = self.new_block();
        let result_ty = self.ty(expr);
        let parameter = result_ty.map(|ty| {
            let id = self.new_value(ty);
            self.function.blocks[join_id.0 as usize].parameters.push(id);
            id
        });
        let current = self.current.expect("condition completed");
        self.finish(
            current,
            TerminatorKind::Branch {
                condition: read(condition_value),
                then_edge: Edge {
                    target: then_id,
                    arguments: Vec::new(),
                },
                else_edge: Edge {
                    target: else_id,
                    arguments: Vec::new(),
                },
            },
            Some(condition.span),
        );
        self.current = Some(then_id);
        let then_value = self.lower_block(then_branch);
        let mut reaches = false;
        if let Some(value) = then_value {
            self.join(join_id, value, then_branch.span);
            reaches = true;
        }
        self.current = Some(else_id);
        let else_value = match else_branch {
            Some(other) => self.lower_expr(other),
            None => self.unit(expr.span),
        };
        if let Some(value) = else_value {
            self.join(join_id, value, expr.span);
            reaches = true;
        }
        self.current = reaches.then_some(join_id);
        parameter.map(|id| op(Source::Value(id), expr.span))
    }
    fn lower_short_circuit(
        &mut self,
        expr: &Expr,
        operator: &str,
        left: &Expr,
        right: &Expr,
    ) -> Option<Operand> {
        let lhs = self.lower_expr(left)?;
        let lhs = self.scalar(lhs)?;
        let rhs_id = self.new_block();
        let bypass_id = self.new_block();
        let join_id = self.new_block();
        let result = self.new_value(Type::Primitive(Primitive::Bool));
        self.function.blocks[join_id.0 as usize]
            .parameters
            .push(result);
        let current = self.current.expect("left operand completed");
        let (then_id, else_id) = if operator == "&&" {
            (rhs_id, bypass_id)
        } else {
            (bypass_id, rhs_id)
        };
        self.finish(
            current,
            TerminatorKind::Branch {
                condition: read(lhs),
                then_edge: Edge {
                    target: then_id,
                    arguments: Vec::new(),
                },
                else_edge: Edge {
                    target: else_id,
                    arguments: Vec::new(),
                },
            },
            Some(left.span),
        );
        self.current = Some(rhs_id);
        let rhs = self
            .lower_expr(right)
            .and_then(|operand| self.scalar(operand));
        if let Some(rhs) = rhs {
            // A logical operator produces an owned Bool, even when its RHS
            // reads a reference. Do not forward the read-only Load result
            // into the join as an owned value.
            let rhs = if matches!(self.ty(right), Some(Type::Reference { .. }))
                || matches!(right.kind, ExprKind::Index { .. } | ExprKind::Field { .. })
            {
                let neutral = self.constant(
                    right.span,
                    Constant::Bool(true),
                    Type::Primitive(Primitive::Bool),
                )?;
                self.emit(
                    right.span,
                    InstructionKind::Binary {
                        op: BinaryOp::Equal,
                        left: read(neutral),
                        right: read(rhs),
                    },
                    Some(Type::Primitive(Primitive::Bool)),
                )?
            } else {
                rhs
            };
            self.join(join_id, rhs, right.span);
        }
        self.current = Some(bypass_id);
        let bypass = self
            .constant(
                expr.span,
                Constant::Bool(operator == "||"),
                Type::Primitive(Primitive::Bool),
            )
            .expect("live bypass");
        self.join(join_id, bypass, expr.span);
        self.current = Some(join_id);
        Some(op(Source::Value(result), expr.span))
    }
}

fn access_mode(access: Access) -> UseMode {
    match access {
        Access::Owned => UseMode::Consume,
        Access::Borrow => UseMode::Borrow,
        Access::Share => UseMode::Share,
    }
}
