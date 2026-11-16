//! Lower a successfully checked standalone primitive module to control-flow IR.
use std::collections::HashMap;

use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, Span};
use memobits_ir::{
    Access, ArrayInit, BinaryOp, Block as IrBlock, BlockId, CanonicalFunction, Constant, Edge,
    Function, Instruction, InstructionKind, LoanId, Local, LocalId, Operand, Primitive, Program,
    Source, Terminator, TerminatorKind, Type, UnaryOp, UseMode, ValueId,
};
use memobits_project::Project;
use memobits_resolve::Resolution;
use memobits_syntax::{Block, Expr, ExprKind, ItemKind, Module, Statement, StatementKind};

use crate::types::{check_resolved_typed, check_typed_module, ExprId, FunctionFacts, PathTarget};

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
        let mut builder = Builder::new(function, fact);
        builder.lower_block(body);
        if let Some(current) = builder.current {
            let value = builder.last_value.take();
            let result = builder.function.signature.result.as_ref();
            let returned = if result == &Type::Primitive(Primitive::Unit) {
                None
            } else {
                value.map(consume)
            };
            builder.finish(current, TerminatorKind::Return(returned), Some(body.span));
        }
        functions.push(builder.function);
    }
    let program = Program { functions };
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
    let typed = check_resolved_typed(project, resolution)?;
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
                let mut builder = Builder::new(function, fact);
                builder.lower_block(body);
                if let Some(current) = builder.current {
                    let value = builder.last_value.take();
                    let returned = if builder.function.signature.result.as_ref()
                        == &Type::Primitive(Primitive::Unit)
                    {
                        None
                    } else {
                        value.map(consume)
                    };
                    builder.finish(current, TerminatorKind::Return(returned), Some(body.span));
                }
                functions.push(builder.function);
            }
        }
    }
    let program = Program { functions };
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
struct LoopTargets {
    header: BlockId,
    exit: BlockId,
    had_break: bool,
}
struct Builder<'a> {
    function: Function,
    facts: &'a FunctionFacts,
    expression_ids: HashMap<usize, ExprId>,
    expressions: HashMap<ExprId, Option<Type>>,
    paths: HashMap<ExprId, PathTarget>,
    current: Option<BlockId>,
    last_value: Option<Operand>,
    loops: Vec<LoopTargets>,
    next_loan: u32,
}
impl<'a> Builder<'a> {
    fn new(function: Function, facts: &'a FunctionFacts) -> Self {
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
        Self {
            function,
            facts,
            expression_ids,
            expressions,
            paths,
            current: Some(BlockId(0)),
            last_value: None,
            loops: Vec::new(),
            next_loan: 0,
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
            self.emit(
                operand.span.unwrap_or(self.function.span),
                InstructionKind::Load { reference: operand },
                Some(*inner),
            )
        } else {
            Some(operand)
        }
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
    fn lower_block(&mut self, block: &Block) -> Option<Operand> {
        for statement in &block.statements {
            if self.current.is_none() {
                break;
            }
            match &statement.kind {
                StatementKind::Binding { value, .. } => {
                    let rhs = self.lower_expr(value);
                    if let Some(rhs) = rhs {
                        let target = self.local(statement);
                        self.emit(
                            statement.span,
                            InstructionKind::Assign {
                                target,
                                value: consume(rhs),
                                initialize: true,
                            },
                            None,
                        );
                    }
                }
                StatementKind::Assign {
                    target,
                    operator,
                    value,
                } => {
                    if matches!(target.kind, ExprKind::Index { .. }) {
                        self.lower_element_assign(statement.span, target, operator, value);
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
                        let kind = if matches!(
                            self.function.locals[local.0 as usize].ty,
                            Type::Reference { .. }
                        ) {
                            let mut reference = op(Source::Local(local), target.span);
                            reference.mode = UseMode::Share;
                            InstructionKind::Store {
                                reference,
                                value: consume(assigned),
                            }
                        } else {
                            InstructionKind::Assign {
                                target: local,
                                value: consume(assigned),
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
                        Some(expr) => self.lower_expr(expr).map(consume),
                        None => None,
                    };
                    if let Some(current) = self.current {
                        self.finish(
                            current,
                            TerminatorKind::Return(returned),
                            Some(statement.span),
                        );
                    }
                }
                StatementKind::Loop(body) => self.lower_loop(body, statement.span),
                StatementKind::Break => {
                    let target = self.loops.last().expect("checked break").exit;
                    self.loops.last_mut().unwrap().had_break = true;
                    self.goto(target, Vec::new(), statement.span);
                }
                StatementKind::Continue => {
                    let target = self.loops.last().expect("checked continue").header;
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
        self.last_value = value;
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
    /// Evaluate the root and every index of `a[i][j]...` left to right, each index
    /// captured at its evaluation point. No address is formed yet, so index
    /// effects precede any bounds check and the right-hand side of a write.
    fn lower_place(&mut self, expr: &Expr) -> Option<(Operand, Vec<Operand>)> {
        let ExprKind::Index { base, index } = &expr.kind else {
            unreachable!("checked index place")
        };
        let (root, mut positions) = if matches!(base.kind, ExprKind::Index { .. }) {
            self.lower_place(base)?
        } else {
            (self.lower_expr(base)?, Vec::new())
        };
        let position = self.lower_expr(index)?;
        let position = self.scalar(position)?;
        positions.push(self.capture(position)?);
        Some((root, positions))
    }
    /// Chain of checked element addresses from `root` through `positions`. Every
    /// level carries `access`, so a write needs `Share` rows down to the element.
    fn address_chain(
        &mut self,
        root: Operand,
        positions: &[Operand],
        access: Access,
        span: Span,
    ) -> Option<Operand> {
        let mut current = root;
        for position in positions {
            current = self.element_addr(current, *position, access, span)?;
        }
        Some(current)
    }
    fn load_element(&mut self, reference: Operand, span: Span) -> Option<Operand> {
        let Some(Type::Reference { inner, .. }) = self.operand_type(reference) else {
            unreachable!("element address is a reference")
        };
        self.emit(span, InstructionKind::Load { reference }, Some(*inner))
    }
    /// `a[i] = v` and `a[i] op= v`. The index is evaluated and captured first,
    /// then the right-hand side; the checked element address and the store are
    /// adjacent, so a bounds trap fires after the right-hand side's effects.
    fn lower_element_assign(
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
        let reference = self.address_chain(array, &positions, Access::Share, span)?;
        self.emit(
            span,
            InstructionKind::Store {
                reference,
                value: consume(assigned),
            },
            None,
        );
        Some(())
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
        let Type::Array { len, .. } = ty else {
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
            let element = self.scalar(element)?;
            let element = consume(self.capture(consume(element))?);
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
            .and_then(|operand| self.scalar(operand))
            .and_then(|operand| self.capture(consume(operand)));
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
                let mut operands = Vec::with_capacity(elements.len());
                for element in elements {
                    let value = self.lower_expr(element)?;
                    let value = self.scalar(value)?;
                    // Capture locals now so every element is read in source order.
                    operands.push(consume(self.capture(consume(value))?));
                }
                self.emit(
                    expr.span,
                    InstructionKind::ArrayNew {
                        init: ArrayInit::Elements(operands),
                    },
                    self.ty(expr),
                )
            }
            ExprKind::Index { .. } => {
                let (array, positions) = self.lower_place(expr)?;
                let reference = self.address_chain(array, &positions, Access::Borrow, expr.span)?;
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
            ExprKind::Bool(value) => self.constant(
                expr.span,
                Constant::Bool(*value),
                Type::Primitive(Primitive::Bool),
            ),
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
                    let access = match name.as_str() {
                        "borrow" => Access::Borrow,
                        "share" => Access::Share,
                        _ => unreachable!("checked conversion"),
                    };
                    if matches!(base.kind, ExprKind::Index { .. }) {
                        // A row of a nested array: the element address is itself
                        // the reference, with `access` on every level.
                        let (array, positions) = self.lower_place(base)?;
                        return self.address_chain(array, &positions, access, expr.span);
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
                for (argument, parameter) in arguments.iter().zip(&signature.parameters) {
                    let argument = self.lower_expr(argument)?;
                    if parameter.access == Access::Owned {
                        args.push(consume(self.capture(consume(argument))?));
                    } else {
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
            ExprKind::Field { .. } => unreachable!("unsupported field rejected before lowering"),
            ExprKind::Block(block) => self.lower_block(block),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => self.lower_if(expr, condition, then_branch, else_branch.as_deref()),
        }
    }
    fn join(&mut self, target: BlockId, value: Operand, span: Span) {
        self.goto(target, vec![consume(value)], span);
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
                || matches!(right.kind, ExprKind::Index { .. })
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
