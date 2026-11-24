//! Range loops: `a..b` and `a..=b` exist only in a `loop ... in` header, with
//! full expressions as bounds.
use memobits_diagnostics::SourceId;
use memobits_syntax::{parse, Expr, ExprKind, ItemKind, Statement, StatementKind};

fn parse_body(source: &str) -> (Vec<Statement>, Vec<String>) {
    let parsed = parse(SourceId(0), source);
    let messages = parsed
        .diagnostics
        .iter()
        .map(|d| d.message.clone())
        .collect();
    let statements = parsed
        .module
        .items
        .iter()
        .find_map(|item| match &item.kind {
            ItemKind::Function { body, .. } => Some(body.statements.clone()),
            _ => None,
        })
        .unwrap_or_default();
    (statements, messages)
}

fn range(source: &str) -> (Expr, Expr, bool) {
    let (statements, messages) = parse_body(source);
    assert!(messages.is_empty(), "{messages:?}");
    let StatementKind::RangeLoop {
        start,
        end,
        inclusive,
        ..
    } = &statements[0].kind
    else {
        panic!("expected a range loop, found {:?}", statements[0].kind)
    };
    (start.clone(), end.clone(), *inclusive)
}

fn binary(expr: &Expr) -> (&str, &Expr, &Expr) {
    match &expr.kind {
        ExprKind::Binary {
            operator,
            left,
            right,
        } => (operator.as_str(), left, right),
        other => panic!("expected a binary expression, found {other:?}"),
    }
}

#[test]
fn half_open_and_inclusive_ranges() {
    let (start, end, inclusive) = range("fn f() { loop i in 0..n { } }");
    assert!(matches!(start.kind, ExprKind::Number(_)));
    assert!(matches!(end.kind, ExprKind::Path(_)));
    assert!(!inclusive);
    let (_, _, inclusive) = range("fn f() { loop i in 0..=n { } }");
    assert!(inclusive);
}

#[test]
fn bounds_are_full_expressions_below_the_range() {
    let (start, end, _) = range("fn f() { loop i in a + 1..b * 2 { } }");
    let (operator, left, right) = binary(&start);
    assert_eq!(operator, "+");
    assert!(matches!(left.kind, ExprKind::Path(_)));
    assert!(matches!(right.kind, ExprKind::Number(_)));
    let (operator, _, right) = binary(&end);
    assert_eq!(operator, "*");
    assert!(matches!(right.kind, ExprKind::Number(_)));

    let (start, end, inclusive) = range("fn f() { loop i in x as u8..=len(v) - 1 || z { } }");
    assert!(matches!(start.kind, ExprKind::Cast { .. }));
    assert_eq!(binary(&end).0, "||");
    assert!(inclusive);
    let (start, _, _) = range("fn f() { loop i in -3..3 { } }");
    assert!(matches!(start.kind, ExprKind::Unary { .. }));
    let (start, _, _) = range("fn f() { loop i in (a + 1)..c { } }");
    assert_eq!(binary(&start).0, "+");
}

#[test]
fn non_range_loops_are_unchanged() {
    let (statements, messages) = parse_body("fn f() { loop x in items { } loop { break; } }");
    assert!(messages.is_empty(), "{messages:?}");
    assert!(matches!(statements[0].kind, StatementKind::ForEach { .. }));
    assert!(matches!(statements[1].kind, StatementKind::Loop(_)));
}

#[test]
fn ranges_outside_a_loop_header_are_rejected_clearly() {
    for source in [
        "fn f() { let r := 0..5; }",
        "fn f() { let r := 0..=5; }",
        "fn f() { let r := ..5; }",
        "fn f() { g(0..5); }",
        "fn f() { loop i in g(0..5) { } }",
        "fn f() { loop i in (0..5) { } }",
        "fn f() { loop i in 0..5..9 { } }",
        "fn f() { if 0..5 { } }",
    ] {
        let (_, messages) = parse_body(source);
        assert!(
            messages.iter().any(|m| m.contains("is not a value")),
            "{source}: {messages:?}"
        );
    }
}

#[test]
fn step_syntax_is_not_part_of_ranges() {
    let (_, messages) = parse_body("fn f() { loop i in 0..10 step 2 { } }");
    assert!(!messages.is_empty());
}
