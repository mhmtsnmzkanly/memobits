//! Structural control-flow checks over a parsed syntax module.
//!
//! This pass validates loop control placement only. It does not check return
//! completeness, types, ownership, or whether paths resolve.

use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, Span};
use memobits_syntax::{Block, Expr, ExprKind, ItemKind, Module, StatementKind};

/// Find `break` and `continue` statements outside a loop in function bodies.
///
/// TE020 marks an invalid `break`; TE021 marks an invalid `continue`.
/// Diagnostics follow source traversal order and carry the statement's span.
/// The caller should parse the source first and handle syntax diagnostics.
pub fn check_control_flow(module: &Module) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for item in &module.items {
        if let ItemKind::Function { body, .. } = &item.kind {
            check_block(body, false, &mut diagnostics);
        }
    }
    diagnostics
}

fn invalid_control(number: u16, keyword: &str, span: Span) -> Diagnostic {
    let mut diagnostic = Diagnostic::new(
        DiagnosticCode::new(Category::Type, number).expect("static TE code"),
        Severity::Error,
        format!("'{keyword}' is only allowed inside a loop"),
    );
    diagnostic.span = Some(span);
    diagnostic
}

fn check_block(block: &Block, in_loop: bool, diagnostics: &mut Vec<Diagnostic>) {
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::Binding { value, .. } | StatementKind::Destructure { value, .. } => {
                check_expr(value, in_loop, diagnostics)
            }
            StatementKind::Assign { target, value, .. } => {
                check_expr(target, in_loop, diagnostics);
                check_expr(value, in_loop, diagnostics);
            }
            StatementKind::Expression(expr) => check_expr(expr, in_loop, diagnostics),
            StatementKind::Return(Some(expr)) => check_expr(expr, in_loop, diagnostics),
            StatementKind::Return(None) => {}
            StatementKind::Loop(body) => check_block(body, true, diagnostics),
            StatementKind::Break if !in_loop => {
                diagnostics.push(invalid_control(20, "break", statement.span));
            }
            StatementKind::Continue if !in_loop => {
                diagnostics.push(invalid_control(21, "continue", statement.span));
            }
            StatementKind::Break | StatementKind::Continue => {}
        }
    }
    if let Some(tail) = &block.tail {
        check_expr(tail, in_loop, diagnostics);
    }
}

fn check_expr(expr: &Expr, in_loop: bool, diagnostics: &mut Vec<Diagnostic>) {
    match &expr.kind {
        ExprKind::Number(_) | ExprKind::Bool(_) | ExprKind::Path(_) => {}
        ExprKind::Array(elements) => {
            for element in elements {
                check_expr(element, in_loop, diagnostics);
            }
        }
        ExprKind::RepeatArray { value, .. } => check_expr(value, in_loop, diagnostics),
        ExprKind::Index { base, index } => {
            check_expr(base, in_loop, diagnostics);
            check_expr(index, in_loop, diagnostics);
        }
        ExprKind::Unary { operand, .. } => check_expr(operand, in_loop, diagnostics),
        ExprKind::Binary { left, right, .. } => {
            check_expr(left, in_loop, diagnostics);
            check_expr(right, in_loop, diagnostics);
        }
        ExprKind::Call { callee, arguments } => {
            check_expr(callee, in_loop, diagnostics);
            for argument in arguments {
                check_expr(argument, in_loop, diagnostics);
            }
        }
        ExprKind::Field { base, .. } => check_expr(base, in_loop, diagnostics),
        ExprKind::Struct { fields, .. } => {
            for field in fields {
                check_expr(&field.value, in_loop, diagnostics);
            }
        }
        ExprKind::Block(block) => check_block(block, in_loop, diagnostics),
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            check_expr(condition, in_loop, diagnostics);
            check_block(then_branch, in_loop, diagnostics);
            if let Some(else_branch) = else_branch {
                check_expr(else_branch, in_loop, diagnostics);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use memobits_diagnostics::SourceId;

    #[test]
    fn empty_module_has_no_diagnostics() {
        assert!(check_control_flow(&Module { items: vec![] }).is_empty());
    }

    #[test]
    fn skips_non_function_items() {
        let parsed = memobits_syntax::parse(SourceId(0), "type Number = i32; use self::math::add;");
        assert!(parsed.diagnostics.is_empty());
        assert!(check_control_flow(&parsed.module).is_empty());
    }
}

mod constants;
mod types;
pub use types::{
    check_resolved_types, check_typed_module, check_types, ExprId, ExpressionFact, FieldFact,
    FunctionFacts, LocalFact, PathTarget, PathUse, StructFact, TypedModule,
};

mod lower;
pub use lower::{lower_module, lower_resolved};
