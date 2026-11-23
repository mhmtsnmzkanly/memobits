use memobits_diagnostics::Severity;
use memobits_diagnostics::SourceId;
use memobits_syntax::parse;

#[test]
fn option_spelling_is_accepted_silently_like_postfix_optional() {
    let option = parse(
        SourceId(0),
        "fn f(a: Option<i32>, b: Option<borrow i32>) {}",
    );
    assert!(option.diagnostics.is_empty(), "{:?}", option.diagnostics);
    assert!(option.warnings.is_empty(), "{:?}", option.warnings);

    let modern = parse(
        SourceId(0),
        "fn f(a: i32?, b: (borrow i32)?, c: borrow i32?) {}",
    );
    assert!(modern.diagnostics.is_empty() && modern.warnings.is_empty());
}

#[test]
fn legacy_bytes_spelling_warns_and_current_spellings_do_not() {
    let legacy = parse(SourceId(0), "fn f(a: Bytes<4>, c: Array<u8, 2>) {}");
    assert!(legacy.diagnostics.is_empty(), "{:?}", legacy.diagnostics);
    let codes: Vec<String> = legacy.warnings.iter().map(|w| w.code.to_string()).collect();
    assert_eq!(codes, ["MW003"]);
    assert!(legacy.warnings[0].message.contains("`Array<u8, N>`"));
    assert!(legacy.warnings.iter().all(|w| w.span.is_some()));

    let modern = parse(
        SourceId(0),
        "fn f(a: string, b: Array<u8, 4>, c: Array<string, 2>) {}",
    );
    assert!(modern.diagnostics.is_empty() && modern.warnings.is_empty());
}
