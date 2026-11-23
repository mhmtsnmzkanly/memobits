use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_syntax::parse;

fn parse_source(source: &str) -> memobits_syntax::Module {
    let parsed = parse(SourceId(91), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    parsed.module
}

#[test]
fn anonymous_record_shapes_are_order_independent_but_exact() {
    let source = r#"
        fn main() -> u32 {
            let first := { right: 2 as u32, left: 40 as u32 };
            let reordered := { left: 1 as u32, right: 3 as u32 };
            let selected := if true { first } else { reordered };
            selected.left + selected.right
        }
    "#;
    let program = lower_module(&parse_source(source), "shapes", &["main".into()])
        .unwrap_or_else(|diagnostics| panic!("{diagnostics:?}"));
    program.validate().unwrap();

    for alternative in [
        "let reordered := { left: true, right: 3 as u32 };",
        "let reordered := { left: 1 as u32, other: 3 as u32 };",
    ] {
        let source = format!(
            "fn main(flag: Bool) -> u32 {{ let first := {{ right: 2 as u32, left: 40 as u32 }}; {alternative} let selected := if flag {{ first }} else {{ reordered }}; selected.left }}"
        );
        let diagnostics = lower_module(&parse_source(&source), "shapes", &["main".into()])
            .expect_err("unequal structural shapes must not unify");
        assert!(
            diagnostics.iter().any(|diagnostic| {
                diagnostic.code.to_string() == "TE013"
                    && diagnostic
                        .message
                        .contains("if branches have incompatible types")
            }),
            "{diagnostics:?}"
        );
    }
}

#[test]
fn anonymous_enum_aliases_keep_declaration_site_identity_and_contextual_unit_variants() {
    let source = r#"
        type First = enum [Ready, Stopped];
        type Second = enum [Ready, Stopped];
        fn first() -> First { Ready }
        fn second() -> Second { Ready }
        fn main() -> u32 {
            let a: First = first();
            let b: Second = second();
            match a {
                Ready => match b { Ready => 42, Stopped => 0 },
                Stopped => 0,
            }
        }
    "#;
    let program = lower_module(&parse_source(source), "anonymous-enums", &["main".into()])
        .unwrap_or_else(|diagnostics| panic!("{diagnostics:?}"));
    program.validate().unwrap();

    let mismatched = r#"
        type First = enum [Ready, Stopped];
        type Second = enum [Ready, Stopped];
        fn second() -> Second { Ready }
        fn take_first(value: First) {}
        fn main() { take_first(second()); }
    "#;
    let diagnostics = lower_module(
        &parse_source(mismatched),
        "anonymous-enums",
        &["main".into()],
    )
    .expect_err("separate inline enum declarations must remain distinct");
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code.to_string() == "TE002"),
        "{diagnostics:?}"
    );

    let unresolved = "type Phase = enum [Ready, Waiting]; fn main() { let value := Ready; }";
    let diagnostics = lower_module(
        &parse_source(unresolved),
        "anonymous-enums",
        &["main".into()],
    )
    .expect_err("a contextual unit variant needs an expected enum type");
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code.to_string() == "TE005"),
        "{diagnostics:?}"
    );
}

#[test]
fn anonymous_enum_payloads_are_typed_and_extracted_by_variant_patterns() {
    let source = r#"
        fn main() -> i32 {
            let result: enum [Number(i32), Pair(i32, Bool), Empty] = Number(40);
            match result {
                Number(value) => value + 2,
                Pair(left, enabled) => left + (if enabled { 1 } else { 0 }),
                Empty => 0,
            }
        }
    "#;
    let program = lower_module(
        &parse_source(source),
        "anonymous-enum-payloads",
        &["main".into()],
    )
    .unwrap_or_else(|diagnostics| panic!("{diagnostics:?}"));
    program.validate().unwrap();

    let mismatched = r#"
        fn main() {
            let result: enum [Number(i32), Empty] = Number(true);
        }
    "#;
    let diagnostics = lower_module(
        &parse_source(mismatched),
        "anonymous-enum-payloads",
        &["main".into()],
    )
    .expect_err("payload types must be checked against the expected anonymous enum");
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.code.to_string() == "TE002"
                && diagnostic.message.contains("expected i32, found Bool")
        }),
        "{diagnostics:?}"
    );
}

#[test]
fn anonymous_record_and_enum_type_syntax_rejects_ambiguous_empty_shapes() {
    for source in ["fn main(value: {}) {}", "fn main() -> enum [] { 0 }"] {
        let parsed = parse(SourceId(92), source);
        assert!(!parsed.diagnostics.is_empty(), "{source}");
        assert!(parsed
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code.to_string() == "SE002"));
    }
}
