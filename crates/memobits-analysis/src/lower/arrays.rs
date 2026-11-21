//! Fixed-array construction and repetition lowering.
use super::*;

impl Builder<'_> {
    pub(super) fn lower_repeat(&mut self, expr: &Expr, value: &Expr) -> Option<Operand> {
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
}
