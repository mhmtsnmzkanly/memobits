//! Compiler-known outcome instances must reuse the ordinary enum pipeline.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_syntax::parse;

#[test]
fn unfinished_error_derivation_cannot_silently_lower_as_plain_struct() {
    let parsed = parse(
        SourceId(91),
        "type Base { pub code: u32 } type Derived: Base { pub line: u32 } fn main() {}",
    );
    assert!(parsed.diagnostics.is_empty());
    let errors = lower_module(&parsed.module, "test", &["main".into()]).unwrap_err();
    assert!(errors
        .iter()
        .any(|error| error.code.to_string() == "TE017" && error.message.contains("derivation")));
}

fn lower(source: &str) -> memobits_ir::Program {
    let parsed = parse(SourceId(91), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let program = lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{errors:?}"));
    program.validate().unwrap();
    program
}

#[test]
fn option_aliases_construct_match_and_cross_calls() {
    let program = lower(
        "type Number = i32;
         type Maybe = Option<Number>;
         fn make(n: i32) -> Option<i32> { Maybe::Some(n) }
         fn read(value: Maybe) -> i32 {
             match value { Maybe::Some(n) => n, Maybe::None => 0 }
         }
         fn main() -> i32 { read(make(7)) + read(Maybe::None) }",
    );
    assert_eq!(program.types.len(), 1);
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn option_aggregate_payload_moves_remain_checked() {
    let program = lower(
        "type Maybe = Option<Array<i32, 2>>;
         fn main() {
             let values := [1, 2];
             let first := Maybe::Some(values);
             let second := Maybe::Some(values);
         }",
    );
    assert!(memobits_ownership::check_ownership(&program)
        .iter()
        .any(|error| error.code.to_string() == "BE001"));
}

#[test]
fn nested_options_keep_all_instantiated_ir_definitions() {
    let program = lower(
        "type Inner = Option<i32>;
         type Outer = Option<Inner>;
         fn main() -> i32 {
             let value := Outer::Some(Inner::Some(9));
             match value {
                 Outer::Some(inner) => match inner { Inner::Some(n) => n, Inner::None => 0 },
                 Outer::None => 0
             }
         }",
    );
    assert_eq!(program.types.len(), 2);
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn contextual_option_prelude_constructors_and_patterns() {
    let program = lower("fn make() -> Option<i32> { Some(7) } fn main() -> i32 { let empty: Option<i32> = None; let value := make(); match value { Some(n) => n, None => 0 } }");
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn option_infers_nested_payloads_without_annotations() {
    let program = lower("fn main() -> i32 { let value := Some(Some(7)); match value { Some(inner) => match inner { Some(n) => n, None => 0 }, None => 0 } }");
    assert_eq!(program.types.len(), 2);
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn bare_none_requires_a_payload_type() {
    let parsed = parse(SourceId(91), "fn main() { let value := None; }");
    assert!(parsed.diagnostics.is_empty());
    let errors = lower_module(&parsed.module, "test", &["main".into()]).unwrap_err();
    assert!(errors
        .iter()
        .any(|error| error.message.contains("Option<T> annotation")));
}

#[test]
fn compiler_error_root_has_public_u32_code_and_can_be_an_option_payload() {
    let program = lower("fn make() -> Error { Error { code: 17 } } fn main() -> u32 { let value := Some(make()); match value { Some(error) => error.code, None => 0 } }");
    assert_eq!(program.types.len(), 2);
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn compiler_known_names_cannot_be_redeclared_as_user_types() {
    for source in [
        "type Option [ Some(i32), None ]",
        "type Error { code: i32 }",
        "type Result [ UserDefined ]",
        "type Attempt = i32;",
    ] {
        let parsed = parse(SourceId(91), source);
        assert!(parsed.diagnostics.is_empty());
        let errors = lower_module(&parsed.module, "test", &["main".into()]).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("reserved for a compiler-known type")),
            "{source}: {errors:?}"
        );
    }
}

fn rejects(source: &str, code: &str, message: &str) {
    let parsed = parse(SourceId(91), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let errors = lower_module(&parsed.module, "test", &["main".into()]).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.code.to_string() == code && error.message.contains(message)),
        "{source}: {errors:?}"
    );
}

#[test]
fn owned_result_and_attempt_intern_aliases_and_match_with_context() {
    let program = lower(
        "type Failure = Error;
         type Number = u32;
         type Read = Result<Number, Failure>;
         type Work = Attempt<Read, Failure>;
         fn make() -> Result<u32, Error> { Ok(7) }
         fn work() -> Work { Done(make()) }
         fn main() -> u32 {
             let error: Read = Read::Err(Error { code: 17 });
             let waiting: Work = Skipped;
             let failed: Work = Failed(Error { code: 23 });
             let value := work();
             match value {
                 Done(read) => match read { Ok(n) => n, Err(e) => e.code },
                 Work::Skipped => 0,
                 Failed(e) => e.code
             }
         }",
    );
    assert_eq!(program.types.len(), 3);
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn outcome_constructor_names_respect_shadowing() {
    lower(
        "type R = Result<i32, Error>;
         fn Ok(n: i32) -> R { R::Ok(n) }
         fn main() -> i32 {
             let value: R = Ok(5);
             let Skipped := 2;
             match value { R::Ok(n) => n + Skipped, Err(_) => 0 }
         }",
    );
    rejects(
        "fn main() -> Result<i32, Error> { let Ok := 5; Ok(1) }",
        "TE011",
        "not callable",
    );
}

#[test]
fn incomplete_or_incompatible_outcome_constructors_report_inference_errors() {
    for (constructor, annotation) in [
        ("Ok(1)", "Result<T, E> annotation"),
        ("Err(Error { code: 2 })", "Result<T, E> annotation"),
        ("Done(1)", "Attempt<T, E> annotation"),
        ("Skipped", "Attempt<T, E> annotation"),
        ("Failed(Error { code: 2 })", "Attempt<T, E> annotation"),
    ] {
        rejects(
            &format!("fn main() {{ let value := {constructor}; }}"),
            "TE002",
            annotation,
        );
    }
    rejects(
        "fn main(value: Result) {}",
        "TE002",
        "requires two type arguments",
    );
    rejects(
        "fn main(value: Attempt) {}",
        "TE002",
        "requires two type arguments",
    );
    rejects(
        "fn main() -> Attempt<i32, Error> { Ok(1) }",
        "TE002",
        "belongs to Result",
    );
    rejects(
        "fn main() -> Result<i32, Error> { Ok(true) }",
        "TE002",
        "expected i32",
    );
    rejects(
        "fn main() -> Result<i32, Error> { Ok(1, 2) }",
        "TE010",
        "expects 1",
    );
    rejects(
        "fn main() -> Attempt<i32, Error> { Skipped() }",
        "TE028",
        "without parentheses",
    );
}

#[test]
fn the_error_bound_checks_identity_and_inferred_payload_evidence() {
    rejects(
        "type Lookalike { pub code: u32 } fn main() { let value: Result<i32, Lookalike> = Ok(7); }",
        "TE002",
        "requires Error for its error type argument, found Lookalike",
    );
    rejects(
        "type Bad = Attempt<i32, u32>; fn main() {}",
        "TE002",
        "requires Error for its error type argument, found u32",
    );
    rejects(
        "fn main() { let value := Err(7); }",
        "TE002",
        "requires Error",
    );
    rejects(
        "fn main() -> Result<i32, Error> { let e := Error { code: 0 }; Err(e.borrow()) }",
        "TE017",
        "reference values cannot escape",
    );
}

#[test]
fn outcome_matches_check_family_instance_and_coverage() {
    rejects(
        "fn main() -> i32 { let v: Attempt<i32, Error> = Done(1); match v { Ok(n) => n, _ => 0 } }",
        "TE030",
        "belongs to Result",
    );
    rejects(
        "type Other = Attempt<u32, Error>; fn main() -> i32 {
             let v: Attempt<i32, Error> = Done(1); match v { Other::Done(_) => 1, _ => 0 }
         }",
        "TE030",
        "belongs to enum 'Attempt<u32, Error>'",
    );
    rejects(
        "fn main() -> i32 { let v: Attempt<i32, Error> = Done(1); match v { Done(n) => n, Failed(_) => 0 } }",
        "TE031",
        "Skipped",
    );
}

#[test]
fn outcome_payload_constructors_consume_owned_aggregates() {
    let program = lower(
        "type R = Result<Array<i32, 2>, Error>;
         type A = Attempt<i32, Error>;
         fn main() {
             let values := [1, 2];
             let error := Error { code: 5 };
             let success: R = Ok(values);
             let failure: A = Failed(error);
             let reused_values: R = R::Ok(values);
             let reused_error: R = Err(error);
         }",
    );
    assert_eq!(
        memobits_ownership::check_ownership(&program)
            .iter()
            .filter(|error| error.code.to_string() == "BE001")
            .count(),
        2
    );
}

#[test]
fn diverging_outcome_payloads_lower_without_constructing_a_variant() {
    lower(
        "fn annotated() -> i32 { let value: Result<i32, Error> = Ok({ return 7; }); 0 }
         fn main() -> i32 { let value := Some({ return annotated(); }); 0 }",
    );
}
