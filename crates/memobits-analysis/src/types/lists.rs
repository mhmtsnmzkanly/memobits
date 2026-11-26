//! Type checking for the supported primitive List surface.
use super::{is_scalar, read_type, Checker, IrAccess, ResolvedArgument, Ty, UNIT};
use memobits_syntax::{Expr, ExprKind};

impl Checker {
    pub(super) fn list_read_receiver(&self, base: &Expr) -> bool {
        match &base.kind {
            ExprKind::Path(path) => path.len() == 1,
            ExprKind::Call { callee, .. } => self.direct_callee(callee),
            // An element of an outer List or array, or a field: a place rooted
            // at a local.
            ExprKind::Index { .. } | ExprKind::Field { .. } => {
                matches!(super::place_root(base), Some(path) if path.len() == 1)
            }
            _ => false,
        }
    }

    pub(super) fn list_get(&mut self, expr: &Expr, base: &Expr, arguments: &[Expr]) -> Ty {
        self.allow_array_value(base);
        let receiver = self.builtin_receiver(base);
        let Ty::List(element) = receiver else {
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
        if !is_scalar(&element) {
            self.error(
                22,
                expr.span,
                "get() copies its element, and only primitive elements are copyable; use `items[i]` in place (borrow, share, in-place match or projection) or `pop()` to take the last element out",
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
            super::registry::by_id(super::registry::TemplateId::Option),
            vec![ResolvedArgument::Type(*element)],
            expr.span,
        )
    }

    pub(super) fn list_mutation(
        &mut self,
        expr: &Expr,
        base: &Expr,
        method: &str,
        arguments: &[Expr],
    ) -> Ty {
        self.allow_array_value(base);
        let receiver = self.expr(base, None);
        let mutable_receiver = matches!(
            receiver,
            Ty::List(_)
                | Ty::Box(_)
                | Ty::Reference {
                    access: IrAccess::Share,
                    ..
                }
        );
        let writable = match &base.kind {
            ExprKind::Path(path) => {
                path.len() == 1
                    && self.lookup(&path[0]).is_some_and(|binding| {
                        mutable_receiver && (binding.mutable || binding.access == IrAccess::Share)
                    })
            }
            // `outer[i].push(x)` writes the element, so the root owner must be
            // a `var` or a `share` parameter.
            ExprKind::Index { .. } | ExprKind::Field { .. } => match super::place_root(base) {
                Some(path) if path.len() == 1 => self.lookup(&path[0]).is_some_and(|binding| {
                    mutable_receiver
                        && (binding.mutable || binding.access == IrAccess::Share)
                        && !matches!(
                            &binding.ty,
                            Ty::Reference {
                                access: IrAccess::Borrow,
                                ..
                            }
                        )
                }),
                _ => false,
            },
            _ => false,
        };
        if writable {
            self.note_write_root(base);
        }
        let (receiver, boxed) = super::peel_boxes(read_type(receiver));
        if boxed
            && !matches!(
                base.kind,
                ExprKind::Path(_) | ExprKind::Field { .. } | ExprKind::Index { .. }
            )
        {
            self.error(
                17,
                base.span,
                "a method through a Box needs the box in a named local, field or element; bind the box to a local first",
            );
            return Ty::Error;
        }
        let Ty::List(element) = receiver else {
            let root = super::root_note(base);
            self.error(17, base.span, format!("{method}() requires a mutable List local, mutable share handle, or share parameter{root}"));
            return Ty::Error;
        };
        if !writable {
            let root = super::root_note(base);
            self.error(17, base.span, format!("{method}() requires a mutable List local, mutable share handle, or share parameter{root}"));
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
                super::registry::by_id(super::registry::TemplateId::Option),
                vec![ResolvedArgument::Type(*element)],
                expr.span,
            );
        }
        if method == "clear" {
            return UNIT;
        }
        let element = *element;
        self.allow_array_value(&arguments[0]);
        let value = read_type(self.expr(&arguments[0], Some(&element)));
        self.reject_extraction(&arguments[0], &value);
        self.ensure(&value, &element, arguments[0].span);
        if value == Ty::Never {
            Ty::Never
        } else {
            UNIT
        }
    }
}

impl Checker {
    /// Elements a List can hold: the types an array can hold, but never a
    /// reference, `(borrow T)?` or a tuple with a List field.
    pub(super) fn check_list_element_support(
        &mut self,
        element: &Ty,
        span: memobits_diagnostics::Span,
    ) {
        if matches!(element, Ty::List(_)) {
            // Nested lists: the inner List owns its block and is released with
            // the outer element cleanup.
            return;
        }
        self.check_element_support(element, span);
    }
}
