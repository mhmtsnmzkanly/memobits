//! Fixed-array element gates and owned-position propagation.
use super::{Checker, Ty};
use memobits_diagnostics::Span;
use memobits_syntax::{Expr, ExprKind, IntegerLiteral};

impl Checker {
    pub(super) fn array_count(&mut self, count: &IntegerLiteral) -> Option<u32> {
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

    /// Executable arrays hold non-Unit primitive, struct/tuple, enum or nested
    /// array elements. String-owning aggregates remain subject to backend gates.
    pub(super) fn check_element_support(&mut self, element: &Ty, span: Span) {
        if self.lowering
            && matches!(element, Ty::Tuple(..))
            && self.contains_list(element, &mut std::collections::HashSet::new())
        {
            self.error(
                17,
                span,
                "arrays cannot contain tuples with List fields in this slice",
            );
        } else if self.table.is_borrow_option(element) {
            self.error(17, span, "(borrow T)? cannot be stored in an array");
        } else if self.lowering
            && !matches!(
                element,
                Ty::Error
                    | Ty::Never
                    | Ty::String
                    | Ty::Array(..)
                    | Ty::Struct(..)
                    | Ty::Tuple(..)
                    | Ty::Enum(..)
            )
            && !matches!(element, Ty::Primitive(kind) if *kind != "Unit")
        {
            self.error(17, span, "executable arrays support non-Unit primitive, struct/tuple, enum and nested array elements only");
        }
    }

    /// Propagate an owned aggregate position through its expression tails.
    pub(super) fn allow_array_value(&mut self, value: &Expr) {
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

    pub(super) fn array_allowed(&self, expr: &Expr) -> bool {
        self.allowed_arrays
            .contains(&(expr as *const Expr as usize))
    }

    /// Aggregate projections cannot be moved out by an implicit field or index read.
    pub(super) fn reject_extraction(&mut self, expr: &Expr, ty: &Ty) {
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
            let advice = if matches!(expr.kind, ExprKind::Index { .. }) {
                "borrow or share the element, read a primitive inside it, or take an element out of its owner with `replace`, `swap` or `pop` (not available yet)"
            } else {
                "borrow or share the aggregate, or read a primitive inside it"
            };
            self.error(22, expr.span, format!("{what}; only primitive values are copied implicitly and partial moves are deferred, so {advice}"));
        }
    }
}
