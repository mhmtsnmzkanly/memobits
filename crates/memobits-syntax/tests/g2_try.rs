//! `try` grammar: a unary-level operand, `else` binds to the nearest `try`,
//! and every form is built from ordinary `match` arms.
use memobits_diagnostics::SourceId;
use memobits_syntax::{parse, Expr, ExprKind, ItemKind, StatementKind};

fn body_of(source: &str) -> (memobits_syntax::Block, Vec<String>) {
    let parsed = parse(SourceId(0), source);
    let messages = parsed
        .diagnostics
        .iter()
        .map(|d| d.message.clone())
        .collect();
    let body = parsed
        .module
        .items
        .iter()
        .find_map(|item| match &item.kind {
            ItemKind::Function { body, .. } => Some(body.clone()),
            _ => None,
        })
        .expect("a function");
    (body, messages)
}

fn binding_value(source: &str) -> Expr {
    let (body, messages) = body_of(source);
    assert!(messages.is_empty(), "{messages:?}");
    let StatementKind::Binding { value, .. } = &body.statements[0].kind else {
        panic!("expected a binding")
    };
    value.clone()
}

fn arms(expr: &Expr) -> (&Expr, &[memobits_syntax::MatchArm]) {
    match &expr.kind {
        ExprKind::Match { scrutinee, arms } => (scrutinee, arms),
        other => panic!("expected a match, found {other:?}"),
    }
}

#[test]
fn try_operand_is_a_unary_level_expression() {
    let value = binding_value("fn f() { let x := try a.b(c) else e { return; }; }");
    let (scrutinee, arms) = arms(&value);
    assert_eq!(arms.len(), 2);
    let ExprKind::Call {
        callee, arguments, ..
    } = &scrutinee.kind
    else {
        panic!("expected the call as scrutinee")
    };
    assert_eq!(arguments.len(), 1);
    assert!(matches!(callee.kind, ExprKind::Field { .. }));
}

#[test]
fn try_binds_tighter_than_binary_operators() {
    let value = binding_value("fn f() { let x := 1 + try g() else { 0 } * 2; }");
    let ExprKind::Binary {
        operator, right, ..
    } = &value.kind
    else {
        panic!("expected a sum")
    };
    assert_eq!(operator, "+");
    let ExprKind::Binary { operator, left, .. } = &right.kind else {
        panic!("expected a product")
    };
    assert_eq!(operator, "*");
    assert!(matches!(left.kind, ExprKind::Match { .. }));
}

#[test]
fn else_belongs_to_the_nearest_try() {
    let value = binding_value("fn f() { let x := try try a() else { 1 } else { 2 }; }");
    let (inner, outer_arms) = arms(&value);
    // The outer handler is `{ 2 }`; the inner try owns `{ 1 }`.
    assert!(matches!(inner.kind, ExprKind::Match { .. }));
    assert_eq!(outer_arms.len(), 2);
    let ExprKind::Block(handler) = &outer_arms[1].body.kind else {
        panic!("expected the outer handler block")
    };
    assert!(matches!(
        handler.tail.as_deref().map(|tail| &tail.kind),
        Some(ExprKind::Number(n)) if n == "2"
    ));
}

#[test]
fn try_inside_an_if_branch_does_not_capture_the_if_else() {
    let (body, messages) =
        body_of("fn f(c: bool) { if c { try g(); } else { h(); } if c { try g() else { 1 }; } }");
    assert!(messages.is_empty(), "{messages:?}");
    assert!(body.statements.len() == 2 || body.tail.is_some());
    let StatementKind::Expression(first) = &body.statements[0].kind else {
        panic!("expected an if statement")
    };
    let ExprKind::If { else_branch, .. } = &first.kind else {
        panic!("expected an if")
    };
    assert!(else_branch.is_some());
}

#[test]
fn try_condition_with_else_is_not_ambiguous_with_if_else() {
    let (body, messages) = body_of("fn f() { if try g() else { false } { h(); } else { k(); } }");
    assert!(messages.is_empty(), "{messages:?}");
    let expr = match (body.statements.first(), body.tail.as_deref()) {
        (Some(statement), _) => match &statement.kind {
            StatementKind::Expression(expr) => expr,
            other => panic!("expected an if statement, found {other:?}"),
        },
        (None, Some(tail)) => tail,
        _ => panic!("expected an if"),
    };
    let ExprKind::If {
        condition,
        else_branch,
        ..
    } = &expr.kind
    else {
        panic!("expected an if")
    };
    assert!(matches!(condition.kind, ExprKind::Match { .. }));
    assert!(else_branch.is_some());
}

#[test]
fn optional_name_and_statement_forms_parse() {
    let (body, messages) = body_of(
        "fn f() { try g(); try g() else e { return; } try g() else { } x = try g(); x = try g() else { 1 }; }",
    );
    assert!(messages.is_empty(), "{messages:?}");
    assert_eq!(body.statements.len(), 5);
    let StatementKind::Expression(expr) = &body.statements[0].kind else {
        panic!("expected a statement")
    };
    let (_, discard) = arms(expr);
    assert_eq!(discard.len(), 2);
    let StatementKind::Expression(expr) = &body.statements[3].kind else {
        panic!("assignment without else is a statement match")
    };
    let (_, assign) = arms(expr);
    let ExprKind::Block(ok) = &assign[0].body.kind else {
        panic!("expected the assignment arm")
    };
    assert!(matches!(
        ok.statements[0].kind,
        StatementKind::Assign { .. }
    ));
    assert!(matches!(
        body.statements[4].kind,
        StatementKind::Assign { .. }
    ));
}

#[test]
fn try_without_else_is_rejected_in_value_positions() {
    for source in [
        "fn f() { let x := try g(); }",
        "fn f() { return try g(); }",
        "fn f() { h(try g()); }",
        "fn f() -> u32 { try g() }",
        "fn f() { x += try g(); }",
    ] {
        let (_, messages) = body_of(source);
        assert!(
            messages.iter().any(|m| m.contains("`try`")),
            "{source}: {messages:?}"
        );
    }
}

#[test]
fn try_is_a_reserved_word() {
    let (_, messages) = body_of("fn f() { let try := 1; }");
    assert!(!messages.is_empty());
}
