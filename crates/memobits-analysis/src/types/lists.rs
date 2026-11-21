//! Type checking for the supported primitive List surface.
use super::{Checker, IrAccess, ResolvedArgument, Ty, UNIT, read_type};
use memobits_syntax::{Expr, ExprKind};

impl Checker {
    pub(super) fn list_read_receiver(&self, base: &Expr) -> bool {
        match &base.kind {
            ExprKind::Path(path) => path.len() == 1,
            ExprKind::Call { callee, .. } => self.direct_callee(callee),
            _ => false,
        }
    }

    pub(super) fn list_get(&mut self, expr: &Expr, base: &Expr, arguments: &[Expr]) -> Ty {
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
            super::registry::by_id(super::registry::TemplateId::Option),
            vec![ResolvedArgument::Type(Ty::Primitive(element))],
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
                | Ty::Reference {
                    access: IrAccess::Share,
                    ..
                }
        );
        let writable = matches!(&base.kind, ExprKind::Path(path) if path.len() == 1
            && self.lookup(&path[0]).is_some_and(|binding| mutable_receiver && (binding.mutable || binding.access == IrAccess::Share)));
        let Ty::List(element) = read_type(receiver) else {
            self.error(17, base.span, format!("{method}() requires a mutable List local, mutable share handle, or share parameter"));
            return Ty::Error;
        };
        if !writable {
            self.error(17, base.span, format!("{method}() requires a mutable List local, mutable share handle, or share parameter"));
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
        if value == Ty::Never { Ty::Never } else { UNIT }
    }
}
