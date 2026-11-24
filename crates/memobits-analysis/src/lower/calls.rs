//! Lowering of direct, selected receiver and indirect calls: argument staging
//! and owned-temporary cleanup.
use super::*;

impl Builder<'_> {
    pub(super) fn lower_call(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        arguments: &[Expr],
    ) -> Option<Operand> {
        let Type::Function(signature) = self.ty(callee).expect("checked callee") else {
            unreachable!("checked function")
        };
        let callee = match (&callee.kind, self.paths_function(callee)) {
            // A named function is called directly, not through its value.
            (ExprKind::Path(_), Some(id)) => op(Source::Function(id), callee.span),
            _ => self.lower_expr(callee)?,
        };
        let callee = self.capture(callee)?;
        let scope_start = self.owned_locals.len();
        let result = (|| {
            let mut args = Vec::new();
            for (index, (argument, parameter)) in
                arguments.iter().zip(&signature.parameters).enumerate()
            {
                // A function value always names an internal function, so its
                // arguments follow the same moves as a direct call's.
                let direct = true;
                let value = self.lower_call_argument(
                    argument,
                    parameter,
                    direct,
                    index + 1 < arguments.len(),
                )?;
                args.push(value);
            }
            self.emit(
                expr.span,
                InstructionKind::Call {
                    callee: read(callee),
                    arguments: args,
                },
                self.ty(expr),
            )
        })();
        if result.is_some() {
            self.end_owned_locals(scope_start, expr.span);
        }
        self.owned_locals.truncate(scope_start);
        result
    }

    /// The function a path expression names, if it names one directly.
    fn paths_function(&self, expr: &Expr) -> Option<memobits_ir::FunctionId> {
        match self.paths.get(
            &self
                .expression_ids
                .get(&(expr as *const Expr as usize))
                .copied()?,
        )? {
            PathTarget::Function(id) => Some(*id),
            PathTarget::Local(_) => None,
        }
    }

    /// Lower one ordinary call argument (never a method receiver) against its
    /// parameter. Owned Strings, Lists and String-owning aggregates are moved
    /// in (temporaries staged in hidden owner locals), borrow and share
    /// parameters take an explicit reference conversion.
    pub(super) fn lower_call_argument(
        &mut self,
        argument: &Expr,
        parameter: &memobits_ir::ParameterType,
        direct: bool,
        has_later_argument: bool,
    ) -> Option<Operand> {
        let direct_string = direct && parameter.ty == Type::String;
        let direct_list = direct && matches!(parameter.ty, Type::List(_));
        let direct_owned_string_aggregate = direct
            && parameter.access == Access::Owned
            && (self.is_string_transport_owner(&parameter.ty)
                || matches!(parameter.ty, Type::Enum(_) | Type::Array { .. })
                    && self.is_string_owner_struct(&parameter.ty));
        let temporary_receiver = match &argument.kind {
            ExprKind::Call { .. } | ExprKind::Interpolation(_)
                if (direct_string || direct_list) && parameter.access == Access::Owned =>
            {
                Some(argument)
            }
            ExprKind::Call {
                callee: conversion, ..
            } if (direct_string || direct_list) && parameter.access == Access::Borrow => {
                match &conversion.kind {
                    ExprKind::Field { base, name }
                        if name == "borrow"
                            && matches!(
                                base.kind,
                                ExprKind::Call { .. } | ExprKind::Interpolation(_)
                            ) =>
                    {
                        Some(base.as_ref())
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        let value = if let Some(base) = temporary_receiver {
            self.lower_with_temporary_owner(base)?
        } else {
            self.lower_expr(argument)?
        };
        let value = if parameter.access != Access::Owned {
            // Keep the original pointee and loan.
            let mut reference = self.borrow(value, parameter.access)?;
            reference.mode = access_mode(parameter.access);
            reference
        } else if direct_string || direct_list || direct_owned_string_aggregate {
            let owned = self.owned_to(value, &parameter.ty)?;
            // An owner temporary (literal or call result) is staged in
            // a hidden local first, like tuple and array elements, so
            // the callee receives a named, exactly-cleaned owner.
            let must_stage_owned_aggregate_temporary =
                direct_owned_string_aggregate && matches!(owned.source, Source::Value(_));
            let must_stage_before_later_argument = has_later_argument
                && temporary_receiver.is_none()
                && matches!(owned.source, Source::Local(_));
            if must_stage_owned_aggregate_temporary || must_stage_before_later_argument {
                // Give an owned tuple temporary a local descriptor
                // before transfer. This also keeps ownership
                // available for cleanup if a later argument exits.
                let staged =
                    self.hidden_local("owned call argument", parameter.ty.clone(), argument.span);
                self.function.locals[staged.0 as usize].mutable = false;
                self.initialize_local(staged, owned, argument.span);
                consume(op(Source::Local(staged), argument.span))
            } else {
                owned
            }
        } else {
            self.owned_captured(value, &parameter.ty)?
        };
        Some(value)
    }

    pub(super) fn lower_selected_call(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        arguments: &[Expr],
    ) -> Option<Operand> {
        let selected = self.selected_calls[&self.id(expr)].clone();
        let ExprKind::Field { base, .. } = &callee.kind else {
            unreachable!("selected call has a receiver method callee")
        };
        let scope_start = self.owned_locals.len();
        let result = (|| {
            let mut values = Vec::with_capacity(arguments.len() + 1);
            let receiver_parameter = &selected.signature.parameters[0];
            if receiver_parameter.access != Access::Owned
                && matches!(base.kind, ExprKind::Index { .. } | ExprKind::Field { .. })
            {
                // A projected receiver (`t.first.read()`, `xs[0].m()`) is
                // addressed in place, never loaded as a whole aggregate.
                let (root, projections) = self.lower_place(base)?;
                let mut reference =
                    self.address_chain(root, &projections, receiver_parameter.access, base.span)?;
                reference.mode = access_mode(receiver_parameter.access);
                values.push(reference);
            } else {
                let receiver = self.lower_expr(base)?;
                values.push(self.lower_selected_argument(receiver, receiver_parameter)?);
            }
            for (index, (argument, parameter)) in arguments
                .iter()
                .zip(selected.signature.parameters.iter().skip(1))
                .enumerate()
            {
                values.push(self.lower_call_argument(
                    argument,
                    parameter,
                    true,
                    index + 1 < arguments.len(),
                )?);
            }
            self.emit(
                expr.span,
                InstructionKind::Call {
                    callee: read(op(Source::Function(selected.function), expr.span)),
                    arguments: values,
                },
                self.ty(expr),
            )
        })();
        if result.is_some() {
            self.end_owned_locals(scope_start, expr.span);
        }
        self.owned_locals.truncate(scope_start);
        result
    }
    pub(super) fn lower_selected_operator(
        &mut self,
        expr: &Expr,
        left: &Expr,
        right: &Expr,
    ) -> Option<Operand> {
        let selected = self.selected_operators[&self.id(expr)].clone();
        let negate_result =
            matches!(expr.kind, ExprKind::Binary { ref operator, .. } if operator == "!=");
        let scope_start = self.owned_locals.len();
        let result = (|| {
            let lhs = self.lower_expr(left)?;
            let lhs = self.lower_selected_argument(lhs, &selected.signature.parameters[0])?;
            let rhs = self.lower_expr(right)?;
            let rhs = self.lower_selected_argument(rhs, &selected.signature.parameters[1])?;
            let call = self.emit(
                expr.span,
                InstructionKind::Call {
                    callee: read(op(Source::Function(selected.function), expr.span)),
                    arguments: vec![lhs, rhs],
                },
                self.ty(expr),
            )?;
            if negate_result {
                self.emit(
                    expr.span,
                    InstructionKind::Unary {
                        op: UnaryOp::Not,
                        operand: read(call),
                    },
                    self.ty(expr),
                )
            } else {
                Some(call)
            }
        })();
        if result.is_some() {
            self.end_owned_locals(scope_start, expr.span);
        }
        self.owned_locals.truncate(scope_start);
        result
    }

    pub(super) fn lower_selected_unary_operator(
        &mut self,
        expr: &Expr,
        operand: &Expr,
    ) -> Option<Operand> {
        let selected = self.selected_operators[&self.id(expr)].clone();
        let scope_start = self.owned_locals.len();
        let result = (|| {
            let value = self.lower_expr(operand)?;
            let value = self.lower_selected_argument(value, &selected.signature.parameters[0])?;
            self.emit(
                expr.span,
                InstructionKind::Call {
                    callee: read(op(Source::Function(selected.function), expr.span)),
                    arguments: vec![value],
                },
                self.ty(expr),
            )
        })();
        if result.is_some() {
            self.end_owned_locals(scope_start, expr.span);
        }
        self.owned_locals.truncate(scope_start);
        result
    }

    pub(super) fn lower_selected_argument(
        &mut self,
        value: Operand,
        parameter: &memobits_ir::ParameterType,
    ) -> Option<Operand> {
        if parameter.access != Access::Owned {
            let mut reference = self.borrow(value, parameter.access)?;
            reference.mode = access_mode(parameter.access);
            Some(reference)
        } else {
            self.owned_captured(value, &parameter.ty)
        }
    }
}
