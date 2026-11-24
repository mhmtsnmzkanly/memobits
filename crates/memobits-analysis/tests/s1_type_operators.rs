//! `T ?! E` is the same type as `T? ! E` and type names use the new spellings.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_syntax::parse;

fn lower(source: &str) -> String {
    let parsed = parse(SourceId(92), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let program = lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{errors:?}"));
    program.validate().unwrap();
    assert!(memobits_ownership::check_ownership(&program).is_empty());
    // Spans differ between spellings; signatures and type tables must not.
    let signatures: Vec<_> = program.functions.iter().map(|f| &f.signature).collect();
    let types: Vec<_> = program.types.iter().map(|t| (&t.path, &t.kind)).collect();
    format!("{types:?} {signatures:?}")
}

#[test]
fn question_bang_is_the_same_type_as_question_then_bang() {
    let source = |spelling: &str| {
        format!(
            "fn pick(flag: bool) -> {spelling} {{ if flag {{ Ok(Some(1)) }} else {{ Ok(None) }} }}
             fn grid() -> array<array<i32, 2>, 2> {{ [[1, 2], [3, 4]] }}
             fn letter() -> char {{ 'a' }}
             fn wrap(v: i32) -> (i32 ! Error)? {{ Some(Ok(v)) }}
             fn main() -> i32 ! Error {{
                 let x: array<i32 ! Error, 1> = [Ok(5)];
                 match pick(true) {{
                     Ok(Some(n)) => Ok(n as i32),
                     Ok(None) => Ok(0),
                     Err(e) => Err(e),
                 }}
             }}"
        )
    };
    let reference = lower(&source("u32? ! Error"));
    for spelling in ["u32?! Error", "u32 ?! Error", "(u32?) ! Error"] {
        assert_eq!(lower(&source(spelling)), reference, "{spelling}");
    }
    // Type names render with the new spellings.
    assert!(reference.contains("u32 ?! Error"), "{reference}");
    assert!(reference.contains("(i32 ! Error)?"), "{reference}");
}
