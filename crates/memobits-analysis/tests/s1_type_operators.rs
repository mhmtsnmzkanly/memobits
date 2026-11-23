//! New built-in spellings lower to exactly the same program as the old ones.
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
fn new_spellings_lower_like_old_spellings() {
    let new = lower(
        "fn pick(flag: bool) -> u32? ! Error { if flag { Ok(Some(1)) } else { Ok(None) } }
         fn grid() -> array<array<i32, 2>, 2> { [[1, 2], [3, 4]] }
         fn letter() -> char { 'a' }
         fn wrap(v: i32) -> (i32 ! Error)? { Some(Ok(v)) }
         fn main() -> i32 ! Error {
             let x: array<i32 ! Error, 1> = [Ok(5)];
             match pick(true) { Ok(o) => match o { Some(n) => Ok(n as i32), None => Ok(0) }, Err(e) => Err(e) }
         }",
    );
    let old = lower(
        "fn pick(flag: Bool) -> Result<Option<u32>, Error> { if flag { Ok(Some(1)) } else { Ok(None) } }
         fn grid() -> Array<Array<i32, 2>, 2> { [[1, 2], [3, 4]] }
         fn letter() -> Char { 'a' }
         fn wrap(v: i32) -> Option<Result<i32, Error>> { Some(Ok(v)) }
         fn main() -> Result<i32, Error> {
             let x: Array<Result<i32, Error>, 1> = [Ok(5)];
             match pick(true) { Ok(o) => match o { Some(n) => Ok(n as i32), None => Ok(0) }, Err(e) => Err(e) }
         }",
    );
    assert_eq!(new, old);
}
