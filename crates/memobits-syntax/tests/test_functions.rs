//! `test fn` declarations: shape rules and the contextual `test` word.
use memobits_diagnostics::SourceId;
use memobits_syntax::{parse, ItemKind};

fn messages(text: &str) -> Vec<String> {
    parse(SourceId(0), text)
        .diagnostics
        .into_iter()
        .map(|diagnostic| diagnostic.message)
        .collect()
}

#[test]
fn a_test_function_parses_with_the_test_flag() {
    let parsed = parse(
        SourceId(0),
        "test fn works() { assert(true); }\nfn plain() {}",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let flags: Vec<bool> = parsed
        .module
        .items
        .iter()
        .map(|item| matches!(item.kind, ItemKind::Function { test: true, .. }))
        .collect();
    assert_eq!(flags, [true, false]);
}

#[test]
fn test_is_an_ordinary_name_outside_a_test_declaration() {
    let parsed = parse(
        SourceId(0),
        "fn test() {}\nfn main() { test(); let test := 1; }",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
}

#[test]
fn explicit_unit_result_is_allowed() {
    assert!(messages("test fn t() -> Unit {}").is_empty());
}

#[test]
fn invalid_test_declarations_are_rejected() {
    let cases = [
        ("pub test fn t() {}", "cannot be `pub`"),
        ("test fn t(a: i32) {}", "cannot take parameters"),
        ("test fn t() -> i32 { 1 }", "must not return a value"),
        ("test fn t<T>() {}", "cannot have generic parameters"),
    ];
    for (text, expected) in cases {
        let found = messages(text);
        assert!(
            found.iter().any(|message| message.contains(expected)),
            "{text}: {found:?}"
        );
    }
}
