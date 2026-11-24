//! A numeric literal node carries its canonical spelling and, when it differs,
//! the text as written (no side table: diagnostics read it from the node).
use memobits_diagnostics::SourceId;
use memobits_syntax::{parse, ExprKind, ItemKind, StatementKind};

fn first_let_value(source: &str) -> ExprKind {
    let parsed = parse(SourceId(0), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
        panic!("expected a function")
    };
    match &body.statements[0].kind {
        StatementKind::Binding { value, .. } => value.kind.clone(),
        other => panic!("expected a let, found {other:?}"),
    }
}

#[test]
fn radix_and_separated_literals_keep_what_was_written() {
    for (written, canonical) in [
        ("0x1F", "31"),
        ("0b1000_0001", "129"),
        ("0o17", "15"),
        ("1_000", "1000"),
        ("1_0.5_0", "10.50"),
    ] {
        let ExprKind::Number(number) =
            first_let_value(&format!("fn f() {{ let x := {written}; }}"))
        else {
            panic!("expected a number")
        };
        assert_eq!(number.canonical, canonical, "{written}");
        assert_eq!(number.written(), written);
        assert_eq!(number.written.as_deref(), Some(written));
    }
    // A plain literal has nothing extra to remember.
    let ExprKind::Number(plain) = first_let_value("fn f() { let x := 42; }") else {
        panic!("expected a number")
    };
    assert_eq!(plain.canonical, "42");
    assert_eq!(plain.written, None);
    assert_eq!(plain.written(), "42");
}
