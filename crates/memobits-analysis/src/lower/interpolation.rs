//! String interpolation. Each distinct shape (text pieces and the types of the
//! interpolated values) becomes one synthesized internal function that takes
//! the values as parameters and returns an owned heap String. A literal such
//! as `"x = {x}"` then lowers to an ordinary call that returns an owned
//! String, so every position that accepts a String-returning call (binding,
//! argument, return, field initializer, branch value) accepts it with the
//! same loans, moves and cleanup.

use std::cell::RefCell;
use std::rc::Rc;

use memobits_diagnostics::Span;
use memobits_ir::{
    Access, Block as IrBlock, BlockId, CanonicalFunction, Function, FunctionId, Instruction,
    InstructionKind, InterpolationPart, LoanId, Local, LocalId, LocalKind, Operand, ParameterType,
    Signature, Source, Terminator, TerminatorKind, Type, UseMode, ValueId,
};
use memobits_syntax::{Expr, InterpolationPart as SyntaxPart};

use super::{access_mode, consume, op, read, Builder};

/// One piece of an interpolation shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Shape {
    Text(String),
    /// A borrowed String (`true`) or a copied primitive of the given type.
    Value(Type),
}

/// The synthesized functions of one program. Their IDs follow the source
/// functions, so existing function IDs do not move.
pub(super) struct Interpolations {
    base: u32,
    package: String,
    module: Vec<String>,
    shapes: Vec<Vec<Shape>>,
    functions: Vec<Function>,
}

pub(super) type SharedInterpolations = Rc<RefCell<Interpolations>>;

pub(super) trait TakeFunctions {
    fn take_functions(&self) -> Vec<Function>;
}

impl TakeFunctions for SharedInterpolations {
    fn take_functions(&self) -> Vec<Function> {
        std::mem::take(&mut self.borrow_mut().functions)
    }
}

impl Interpolations {
    pub(super) fn new(source_functions: usize) -> SharedInterpolations {
        Rc::new(RefCell::new(Self {
            base: source_functions as u32,
            package: String::new(),
            module: Vec::new(),
            shapes: Vec::new(),
            functions: Vec::new(),
        }))
    }

    /// Name the module that the next requested functions belong to.
    pub(super) fn enter(&mut self, package: &str, module: &[String]) {
        self.package = package.to_owned();
        self.module = module.to_vec();
    }

    fn request(&mut self, shape: Vec<Shape>, span: Span) -> FunctionId {
        if let Some(index) = self.shapes.iter().position(|known| *known == shape) {
            return FunctionId(self.base + index as u32);
        }
        let index = self.shapes.len();
        let function = build(&shape, span, &self.package, &self.module, index);
        self.shapes.push(shape);
        self.functions.push(function);
        FunctionId(self.base + index as u32)
    }
}

fn build(shape: &[Shape], span: Span, package: &str, module: &[String], index: usize) -> Function {
    let mut signature = Vec::new();
    let mut locals = Vec::new();
    for piece in shape {
        let Shape::Value(ty) = piece else { continue };
        let position = locals.len();
        let (access, local_ty) = if *ty == Type::String {
            (
                Access::Borrow,
                Type::Reference {
                    access: Access::Borrow,
                    inner: Box::new(Type::String),
                },
            )
        } else {
            (Access::Owned, ty.clone())
        };
        signature.push(ParameterType {
            access,
            ty: ty.clone(),
        });
        locals.push(Local {
            name: format!("part{position}"),
            ty: local_ty,
            mutable: false,
            kind: LocalKind::Ordinary,
            span,
        });
    }
    let parameter_locals = (0..locals.len() as u32).map(LocalId).collect::<Vec<_>>();
    let target = LocalId(locals.len() as u32);
    locals.push(Local {
        name: "interpolated".into(),
        ty: Type::String,
        mutable: false,
        kind: LocalKind::Ordinary,
        span,
    });
    let mut values = Vec::new();
    let mut instructions = Vec::new();
    let mut parts = Vec::new();
    let mut next_parameter = 0u32;
    let mut next_loan = 0u32;
    for piece in shape {
        match piece {
            Shape::Text(text) => parts.push(InterpolationPart::Text(text.clone())),
            Shape::Value(ty) => {
                let local = LocalId(next_parameter);
                next_parameter += 1;
                if *ty == Type::String {
                    let reference = Type::Reference {
                        access: Access::Borrow,
                        inner: Box::new(Type::String),
                    };
                    let output = ValueId(values.len() as u32);
                    values.push(reference);
                    instructions.push(Instruction {
                        span: Some(span),
                        output: Some(output),
                        kind: InstructionKind::Borrow {
                            loan: LoanId(next_loan),
                            owner: Operand {
                                source: Source::Local(local),
                                mode: UseMode::Borrow,
                                span: Some(span),
                            },
                            access: Access::Borrow,
                        },
                    });
                    next_loan += 1;
                    parts.push(InterpolationPart::Value(read_value(output, span)));
                } else {
                    parts.push(InterpolationPart::Value(Operand {
                        source: Source::Local(local),
                        mode: UseMode::Read,
                        span: Some(span),
                    }));
                }
            }
        }
    }
    instructions.push(Instruction {
        span: Some(span),
        output: None,
        kind: InstructionKind::InitInterpolatedString { target, parts },
    });
    let captured = ValueId(values.len() as u32);
    values.push(Type::String);
    instructions.push(Instruction {
        span: Some(span),
        output: Some(captured),
        kind: InstructionKind::Capture(Operand {
            source: Source::Local(target),
            mode: UseMode::Consume,
            span: Some(span),
        }),
    });
    instructions.push(Instruction {
        span: Some(span),
        output: None,
        kind: InstructionKind::EndStringLocal { local: target },
    });
    Function {
        path: CanonicalFunction {
            package: package.to_owned(),
            module: module.to_vec(),
            name: format!("$interpolate${index}"),
        },
        span,
        signature: Signature {
            parameters: signature,
            result: Box::new(Type::String),
        },
        parameter_locals,
        locals,
        values,
        blocks: vec![IrBlock {
            parameters: Vec::new(),
            instructions,
            terminator: Terminator {
                span: Some(span),
                kind: TerminatorKind::Return(Some(Operand {
                    source: Source::Value(captured),
                    mode: UseMode::Consume,
                    span: Some(span),
                })),
            },
        }],
        entry: BlockId(0),
    }
}

fn read_value(value: ValueId, span: Span) -> Operand {
    Operand {
        source: Source::Value(value),
        mode: UseMode::Read,
        span: Some(span),
    }
}

impl Builder<'_> {
    /// Lower `"text {a} text {b}"` to a call of the synthesized function. The
    /// identifiers are read left to right, once each: a String is borrowed
    /// for the call, a primitive is copied.
    pub(super) fn lower_interpolation(
        &mut self,
        expr: &Expr,
        parts: &[SyntaxPart],
    ) -> Option<Operand> {
        let mut shape = Vec::new();
        let mut arguments = Vec::new();
        for part in parts {
            match part {
                SyntaxPart::Text(text) => shape.push(Shape::Text(text.clone())),
                SyntaxPart::Value(value) => {
                    let ty = self.ty(value)?;
                    let operand = self.lower_expr(value)?;
                    let inner = match &ty {
                        Type::Reference { inner, .. } => (**inner).clone(),
                        other => other.clone(),
                    };
                    if inner == Type::String {
                        let mut reference = self.borrow(operand, Access::Borrow)?;
                        reference.mode = access_mode(Access::Borrow);
                        arguments.push(reference);
                    } else {
                        let scalar = self.scalar(operand)?;
                        arguments.push(self.owned(scalar)?);
                    }
                    shape.push(Shape::Value(inner));
                }
            }
        }
        let function = self.interpolations.borrow_mut().request(shape, expr.span);
        let result = self.emit(
            expr.span,
            InstructionKind::Call {
                callee: read(op(Source::Function(function), expr.span)),
                arguments,
            },
            Some(Type::String),
        )?;
        // Stage the heap String in a named owner so that every consumer sees a
        // plain String move, with the owner released by its lexical scope.
        let staged = self.hidden_local("interpolated String", Type::String, expr.span);
        self.initialize_local(staged, consume(result), expr.span);
        Some(consume(op(Source::Local(staged), expr.span)))
    }
}
