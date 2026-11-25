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
        let callee_expr = callee;
        let callee_ty = self.ty(callee).expect("checked callee");
        // A `borrow fn` / `share fn` parameter is called through its reference.
        let through_reference = matches!(callee_ty, Type::Reference { .. });
        let (signature, wrapped) = self
            .function_signature_of(&callee_ty)
            .expect("checked function");
        let callee = match (&callee.kind, self.paths_function(callee)) {
            // A named function is called directly, not through its value.
            (ExprKind::Path(_), Some(id)) => op(Source::Function(id), callee.span),
            _ if wrapped && !through_reference => {
                // An owned function value: read its callable word in place.
                let place =
                    if matches!(callee.kind, ExprKind::Index { .. } | ExprKind::Field { .. }) {
                        self.lower_read_receiver(callee)?
                    } else {
                        let value = self.lower_expr(callee)?;
                        let value = self.stage_fresh_call(value, &callee_ty, callee.span);
                        let value = if matches!(value.source, Source::Value(_)) {
                            let staged =
                                self.hidden_local("function value", callee_ty.clone(), callee.span);
                            self.initialize_local(staged, consume(value), callee.span);
                            op(Source::Local(staged), callee.span)
                        } else {
                            value
                        };
                        self.borrow(value, Access::Borrow)?
                    };
                let word = self.field_addr_index(place, 0, Access::Borrow, callee.span)?;
                self.scalar(word)?
            }
            _ if wrapped => {
                let place = self.lower_expr(callee)?;
                let word = self.field_addr_index(place, 0, Access::Borrow, callee.span)?;
                self.scalar(word)?
            }
            _ => self.lower_expr(callee)?,
        };
        let callee = if through_reference && !wrapped {
            self.scalar(callee)?
        } else {
            callee
        };
        if wrapped
            && !matches!(callee.source, Source::Function(_))
            && !self.callee_is_mutable(callee_expr)
        {
            // A closure that mutates its environment needs a mutable place.
            self.emit(
                callee_expr.span,
                InstructionKind::ClosureReadOnly {
                    value: read(callee),
                },
                None,
            );
        }
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

    /// Whether a call through this place may mutate the environment of an
    /// owned closure: the place is rooted in a `var`, a `share` reference, or
    /// is a temporary.
    fn callee_is_mutable(&self, callee: &Expr) -> bool {
        match &callee.kind {
            ExprKind::Path(_) => match self.path(callee) {
                PathTarget::Local(id) => {
                    let local = &self.function.locals[id.0 as usize];
                    match &local.ty {
                        Type::Reference { access, .. } => {
                            *access == Access::Share
                                || self
                                    .facts
                                    .locals
                                    .get(id.0 as usize)
                                    .is_some_and(|fact| fact.share_function)
                        }
                        _ => local.mutable,
                    }
                }
                PathTarget::Function(_) => true,
            },
            ExprKind::Field { base, .. } | ExprKind::Index { base, .. } => {
                self.callee_is_mutable(base)
            }
            _ => true,
        }
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
        let direct_list = direct && matches!(parameter.ty, Type::List(_) | Type::Box(_));
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
            // A function value (a name, a literal, a closure) is lent from a
            // local: stage a temporary one in a hidden local first.
            let value = if self.operand_type(value).is_some_and(|ty| {
                matches!(ty, Type::Function(_)) || self.closure_wrapper(&ty).is_some()
            }) && !matches!(value.source, Source::Local(_))
            {
                let ty = self.operand_type(value)?;
                let staged = self.hidden_local("function argument", ty, argument.span);
                let owned = self.owned(value)?;
                self.initialize_local(staged, owned, argument.span);
                op(Source::Local(staged), argument.span)
            } else {
                value
            };
            // An owned closure lent to a `share fn` parameter may mutate its
            // environment: that needs a mutable place.
            if parameter.access == Access::Borrow
                && self.closure_wrapper(&self.operand_type(value)?).is_some()
                && self
                    .facts
                    .share_function_arguments
                    .contains(&(argument as *const Expr as usize))
                && !self.callee_is_mutable(argument)
            {
                let place = self.borrow(value, Access::Borrow)?;
                let word = self.field_addr_index(place, 0, Access::Borrow, argument.span)?;
                let word = self.scalar(word)?;
                self.emit(
                    argument.span,
                    InstructionKind::ClosureReadOnly { value: read(word) },
                    None,
                );
            }
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
            let boxed = self.box_depth(base);
            if receiver_parameter.access != Access::Owned
                && (boxed > 0
                    || matches!(base.kind, ExprKind::Index { .. } | ExprKind::Field { .. }))
            {
                // A projected receiver (`t.first.read()`, `xs[0].m()`) is
                // addressed in place, never loaded as a whole aggregate. A
                // boxed receiver is addressed through the box.
                let (root, mut projections) = self.lower_place(base)?;
                for _ in 0..boxed {
                    projections.push(Projection::Deref);
                }
                let mut reference =
                    self.address_chain(root, &projections, receiver_parameter.access, base.span)?;
                reference.mode = access_mode(receiver_parameter.access);
                values.push(reference);
            } else {
                let mut receiver = self.lower_expr(base)?;
                if boxed > 0 {
                    // A by-value method on a box consumes it.
                    let option_ty = self.match_unboxes[&self.id(expr)].clone();
                    let Some(Type::Box(inner)) = self.operand_type(receiver) else {
                        unreachable!("checked boxed receiver")
                    };
                    receiver = self.take_box_value(receiver, option_ty, *inner, base.span)?;
                }
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
