//! Compiler-known outcome instances must reuse the ordinary enum pipeline.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_syntax::parse;

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
         type Maybe = Number?;
         fn make(n: i32) -> i32? { Maybe::Some(n) }
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
        "type Maybe = array<i32, 2>?;
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
        "type Inner = i32?;
         type Outer = Inner?;
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
    let program = lower("fn make() -> i32? { Some(7) } fn main() -> i32 { let empty: i32? = None; let value := make(); match value { Some(n) => n, None => 0 } }");
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn option_infers_nested_payloads_without_annotations() {
    let program = lower("fn main() -> i32 { let value := Some(Some(7)); match value { Some(inner) => match inner { Some(n) => n, None => 0 }, None => 0 } }");
    assert_eq!(program.types.len(), 2);
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn reference_type_arguments_fail_before_lowering() {
    for (source, rejected) in [
        ("type Maybe = (borrow i32)?; fn main() {}", "borrow i32"),
        ("fn main() { let empty: (share i32)? = None; }", "share i32"),
        (
            "fn leak() -> (borrow i32)? { let n := 1; Some(n.borrow()) } fn main() {}",
            "borrow i32",
        ),
        (
            "type Record { value: array<(borrow i32)?, 2> } fn main() {}",
            "borrow i32",
        ),
        (
            "fn take(a: array<borrow i32, 2>) {} fn main() {}",
            "borrow i32",
        ),
        (
            "fn main() { let n := 1; let wrapped := Some(Some(n.borrow())); }",
            "n.borrow()",
        ),
        (
            "type Bad = i32 ! (borrow Error); fn main() {}",
            "borrow Error",
        ),
    ] {
        let parsed = parse(SourceId(91), source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
        let errors = lower_module(&parsed.module, "test", &["main".into()]).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.to_string() == "TE017"
                    && error.message.contains("embedded-loan tracking")
                    && error
                        .span
                        .is_some_and(|span| &source[span.start..span.end] == rejected)
            }),
            "{source}: {errors:?}"
        );
    }
}

#[test]
fn owned_option_still_copies_primitive_from_reference() {
    let program = lower(
        "fn main() -> i32 {
             var n := 1;
             let wrapped: i32? = Some(n.borrow());
             n = 2;
             match wrapped { Some(value) => value, None => n }
         }",
    );
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn bare_none_requires_a_payload_type() {
    let parsed = parse(SourceId(91), "fn main() { let value := None; }");
    assert!(parsed.diagnostics.is_empty());
    let errors = lower_module(&parsed.module, "test", &["main".into()]).unwrap_err();
    assert!(errors
        .iter()
        .any(|error| error.message.contains("'T?' annotation")));
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
        "type Utf8Error { code: i32 }",
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
         type Read = Number ! Failure;
         type Work = Read ?! Failure;
         fn make() -> u32 ! Error { Ok(7) }
         fn work() -> Work { Ok(Some(make())) }
         fn main() -> u32 {
             let error: Read = Read::Err(Error { code: 17 });
             let waiting: Work = Ok(None);
             let failed: Work = Err(Error { code: 23 });
             let value := work();
             match value {
                 Ok(Some(read)) => match read { Ok(n) => n, Err(e) => e.code },
                 Ok(None) => 0,
                 Err(e) => e.code
             }
         }",
    );
    // Failure, Read, Read? and Work.
    assert_eq!(program.types.len(), 4);
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn outcome_constructor_names_respect_shadowing() {
    lower(
        "type R = i32 ! Error;
         fn Ok(n: i32) -> R { R::Ok(n) }
         fn main() -> i32 {
             let value: R = Ok(5);
             let Offset := 2;
             match value { R::Ok(n) => n + Offset, Err(_) => 0 }
         }",
    );
    rejects(
        "fn main() -> i32 ! Error { let Ok := 5; Ok(1) }",
        "TE011",
        "not callable",
    );
}

#[test]
fn incomplete_or_incompatible_outcome_constructors_report_inference_errors() {
    for (constructor, annotation) in [
        ("Ok(1)", "'T ! E' annotation"),
        ("Err(Error { code: 2 })", "'T ! E' annotation"),
        ("None", "'T?' annotation"),
    ] {
        rejects(
            &format!("fn main() {{ let value := {constructor}; }}"),
            "TE002",
            annotation,
        );
    }
    rejects(
        "fn main() -> i32 ?! Error { Ok(1) }",
        "TE002",
        "expected i32?",
    );
    rejects(
        "fn main() -> i32 ! Error { Ok(true) }",
        "TE002",
        "expected i32",
    );
    rejects(
        "fn main() -> i32 ! Error { Ok(1, 2) }",
        "TE010",
        "expects 1",
    );
    rejects(
        "fn main() -> i32 ?! Error { None() }",
        "TE028",
        "without parentheses",
    );
}

#[test]
fn the_error_bound_checks_identity_and_inferred_payload_evidence() {
    rejects(
        "type Lookalike { pub code: u32 } fn main() { let value: i32 ! Lookalike = Ok(7); }",
        "TE002",
        "requires Error or a type derived from it for its error type argument, found Lookalike",
    );
    rejects(
        "type Bad = i32 ?! u32; fn main() {}",
        "TE002",
        "requires Error or a type derived from it for its error type argument, found u32",
    );
    rejects(
        "fn main() { let value := Err(7); }",
        "TE002",
        "requires Error",
    );
    rejects(
        "fn main() -> i32 ! Error { let e := Error { code: 0 }; Err(e.borrow()) }",
        "TE017",
        "reference values cannot escape",
    );
}

#[test]
fn outcome_matches_check_family_instance_and_coverage() {
    rejects(
        "fn main() -> i32 { let v: i32 ?! Error = Ok(Some(1)); match v { Some(n) => n, _ => 0 } }",
        "TE030",
        "belongs to",
    );
    rejects(
        "type Other = u32 ?! Error; fn main() -> i32 {
             let v: i32 ?! Error = Ok(Some(1)); match v { Other::Ok(_) => 1, _ => 0 }
         }",
        "TE030",
        "belongs to enum 'u32 ?! Error'",
    );
    rejects(
        "fn main() -> i32 { let v: i32 ?! Error = Ok(Some(1)); match v { Ok(Some(n)) => n, Err(_) => 0 } }",
        "TE031",
        "Ok(None)",
    );
}

#[test]
fn outcome_payload_constructors_consume_owned_aggregates() {
    let program = lower(
        "type R = array<i32, 2> ! Error;
         type A = i32 ?! Error;
         fn main() {
             let values := [1, 2];
             let error := Error { code: 5 };
             let success: R = Ok(values);
             let failure: A = Err(error);
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
        "fn annotated() -> i32 { let value: i32 ! Error = Ok({ return 7; }); 0 }
         fn main() -> i32 { let value := Some({ return annotated(); }); 0 }",
    );
}

#[test]
fn error_derivation_flattens_fields_in_ancestor_first_order() {
    let program = lower(
        "type Handled = u32 ! ParseError;
         type ParseError: BaseAlias { pub line: u32 }
         type BaseAlias = BaseError;
         type BaseError: Root { pub stage: u32, pub column: u32 }
         type Root = Error;
         fn main() -> u32 {
             let failed: Handled = Err(ParseError { column: 11, line: 23, stage: 7, code: 5 });
             match failed {
                 Err(e) => { let ParseError { stage, code, line, column } := e; code + stage + column + line },
                 Ok(n) => n
             }
         }",
    );
    let derived = program
        .types
        .iter()
        .find(|ty| ty.path.name == "ParseError")
        .unwrap();
    let memobits_ir::TypeDefKind::Struct { fields } = &derived.kind else {
        panic!("expected a struct")
    };
    assert_eq!(
        fields
            .iter()
            .map(|field| field.name.as_str())
            .collect::<Vec<_>>(),
        ["code", "stage", "column", "line"]
    );
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn error_derivation_rejects_non_error_bases() {
    for (declarations, base) in [
        ("type Lookalike { pub code: u32 }", "Lookalike"),
        ("type Something [ Yes ]", "Something"),
        ("", "u32"),
        ("", "array<u32, 2>"),
        (
            "type Wrapped = i32 ! Valid; type Valid: Error {}",
            "Wrapped",
        ),
    ] {
        let source = format!("type Derived: {base} {{}} {declarations} fn main() {{}}");
        let parsed = parse(SourceId(91), &source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let errors = lower_module(&parsed.module, "test", &["main".into()]).unwrap_err();
        assert_eq!(errors.len(), 1, "{source}: {errors:?}");
        assert_eq!(errors[0].code.to_string(), "TE017");
        assert!(errors[0]
            .message
            .contains("error derivation requires Error"));
    }
    rejects("type Bad: Missing {}", "TE001", "unresolved type 'Missing'");
}

#[test]
fn error_derivation_diagnoses_collisions_and_cycles() {
    for (source, code, message) in [
        (
            "type Leaf: Error { code: u32 }",
            "TE023",
            "redeclares inherited field 'code'",
        ),
        (
            "type Leaf: Mid { pub secret: u32 } type Mid: Base {} type Base: Error { secret: u32 }",
            "TE023",
            "redeclares inherited field 'secret'",
        ),
        (
            "type Leaf: Error {} fn main() { let value := Leaf {}; }",
            "TE023",
            "missing field(s) in 'Leaf' literal: code",
        ),
        ("type A: A {}", "TE026", "error derivation cycle"),
        (
            "type A: B {} type B: C {} type C = A;",
            "TE026",
            "error derivation cycle",
        ),
        (
            "type Base: Error { next: i32 ! Leaf } type Leaf: Base {}",
            "TE026",
            "'Leaf' would have infinite size",
        ),
    ] {
        rejects(source, code, message);
    }
}

#[test]
fn derived_errors_are_moved_into_outcomes_and_require_context() {
    let program = lower(
        "type ParseError: Error {}
         fn main() {
             let error := ParseError { code: 7 };
             let failed: i32 ?! ParseError = Err(error);
             let reused: i32 ! ParseError = Err(error);
         }",
    );
    assert!(memobits_ownership::check_ownership(&program)
        .iter()
        .any(|error| error.code.to_string() == "BE001"));
    rejects(
        "type ParseError: Error {} fn main() { let failed := Err(ParseError { code: 7 }); }",
        "TE002",
        "'T ! E' annotation",
    );
}

#[test]
fn error_derivation_preserves_nominal_type_checks() {
    for (use_error, message) in [
        ("owned(e)", "expected Error, found ParseError"),
        (
            "let failed: i32 ! Error = Err(e);",
            "expected Error, found ParseError",
        ),
    ] {
        rejects(
            &format!(
                "type ParseError: Error {{}}
                 fn owned(e: Error) {{}}
                 fn main() {{ var e := ParseError {{ code: 7 }}; {use_error} }}"
            ),
            "TE002",
            message,
        );
    }
}

#[test]
fn error_reference_calls_require_ancestry_and_compatible_access() {
    let types = "type Base: Error {}
                 type Leaf: Base {}
                 type Sibling: Base {}
                 type Lookalike { code: u32 }
                 fn read(e: borrow Error) {}
                 fn leaf(e: borrow Leaf) {}
                 fn write(e: share Error) {}";
    for (body, code, message) in [
        (
            "let e := Lookalike { code: 7 }; read(e.borrow());",
            "TE002",
            "found borrow Lookalike",
        ),
        (
            "let e := Sibling { code: 7 }; leaf(e.borrow());",
            "TE002",
            "found borrow Sibling",
        ),
        (
            "let e := Error { code: 7 }; leaf(e.borrow());",
            "TE002",
            "found borrow Error",
        ),
        (
            "let e := Leaf { code: 7 }; write(e.borrow());",
            "TE017",
            "does not match the share",
        ),
    ] {
        rejects(&format!("{types} fn main() {{ {body} }}"), code, message);
    }
}

#[test]
fn error_ancestor_call_reborrows_keep_the_original_loan() {
    let declarations = "type Base: Error {} type Leaf: Base {}
                        fn read(e: borrow Error) -> u32 { e.code }
                        fn write(e: share Base) { e.code = 12; }
                        fn both(a: share Error, b: borrow Leaf) {}";
    let valid = lower(&format!(
        "{declarations} fn main() -> u32 {{
            var e := Leaf {{ code: 7 }};
            var r := e.share();
            let before := read(r);
            write(r);
            let after := read(r.borrow());
            e.code = 20;
            before + after + e.code
        }}"
    ));
    assert!(memobits_ownership::check_ownership(&valid).is_empty());

    for (body, message) in [
        (
            "var r := e.share(); both(r, e.borrow());",
            "another argument",
        ),
        (
            "let r := e.borrow(); write(e.share()); read(r);",
            "while it is borrowed",
        ),
        (
            "let r := e.share(); write(r);",
            "immutable reference handle",
        ),
    ] {
        let program = lower(&format!(
            "{declarations} fn main() {{ var e := Leaf {{ code: 7 }}; {body} }}"
        ));
        let errors = memobits_ownership::check_ownership(&program);
        assert!(
            errors.iter().any(|error| error.message.contains(message)),
            "{body}: {errors:?}"
        );
    }
}

#[test]
fn local_borrow_option_keeps_the_owner_loan_through_moves_and_extraction() {
    for body in [
        "owner.x = 2; match moved { Some(r) => r.x, None => 0 }",
        "let taken := owner; match moved { Some(r) => r.x, None => 0 }",
        "match moved { Some(r) => { owner.x = 2; r.x }, None => 0 }",
        "match moved { Some(r) => { let taken := owner; r.x }, None => 0 }",
        "match moved { Some(r) => { let exclusive := owner.share(); exclusive.x + r.x }, None => 0 }",
    ] {
        let source = format!(
            "type P {{ x: i32 }} fn main() -> i32 {{
                var owner := P {{ x: 1 }};
                let value: (borrow P)? = Some(owner.borrow());
                let moved := value;
                {body}
            }}"
        );
        let errors = memobits_ownership::check_ownership(&lower(&source));
        assert!(errors.iter().any(|error| error.code.to_string() == "BE005"), "{source}: {errors:?}");
    }
}

#[test]
fn local_borrow_option_extraction_is_read_only_and_allows_later_owner_moves() {
    let source = "type P { x: i32 }
        fn main() -> i32 {
            var owner := P { x: 7 };
            let wrapped: (borrow P)? = Some(owner.borrow());
            match wrapped { Some(r) => { let x := r.x; let moved := owner; x + moved.x }, None => 0 }
        }";
    assert!(memobits_ownership::check_ownership(&lower(source)).is_empty());

    let write_through_borrow = source.replace("let x := r.x;", "r.x = 9; let x := r.x;");
    let parsed = parse(SourceId(91), &write_through_borrow);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let errors = lower_module(&parsed.module, "test", &["main".into()]).unwrap_err();
    assert!(
        errors.iter().any(|error| error.code.to_string() == "TE004"
            && error
                .message
                .contains("cannot assign through borrow binding")),
        "{errors:?}"
    );
}

#[test]
fn local_borrow_option_unsupported_transports_are_gated() {
    for body in [
        "var value: (borrow i32)? = Some(owner.borrow());",
        "let value: (borrow i32)? = Some(owner.share());",
        "let value: (borrow i32)? = Some(owner);",
        "let value: (borrow i32)? = { let inner := 2; let local: (borrow i32)? = Some(inner.borrow()); local };",
        "let value: (borrow i32)? = if true { None } else { None };",
        "let value: (borrow i32)? = None; let next := Some(value);",
        "let value: (borrow i32)? = None; let next := [value];",
        "let value: (borrow i32)? = None; let r := value.borrow();",
        "let value: (borrow i32)? = Some(owner.borrow()); let r := match value { Some(r) => r, None => owner.borrow() };",
        "let value: (borrow i32)? = None; let next := match true_option() { Some(_) => value, None => value };",
    ] {
        let source = format!(
            "fn true_option() -> i32? {{ Some(1) }}
             fn main() {{ var owner := 1; {body} }}"
        );
        let parsed = parse(SourceId(91), &source);
        assert!(parsed.diagnostics.is_empty(), "{source}: {:?}", parsed.diagnostics);
        let errors = lower_module(&parsed.module, "test", &["main".into()]).unwrap_err();
        assert!(errors.iter().any(|error| error.code.to_string() == "TE017"), "{source}: {errors:?}");
    }
}

#[test]
fn ir_rejects_escaping_or_nonconsuming_borrow_option_transport() {
    use memobits_ir::{InstructionKind, UseMode};

    let program = lower(
        "fn main() -> i32 {
            let owner := 9;
            let wrapped: (borrow i32)? = Some(owner.borrow());
            match wrapped { Some(r) => r.copy(), None => 0 }
        }",
    );
    let mut escaping = program.clone();
    let function = &mut escaping.functions[0];
    *function.signature.result = function.locals[1].ty.clone();
    assert!(escaping
        .validate()
        .unwrap_err()
        .iter()
        .any(|error| error.message.contains("not supported in signatures")));

    let mut copying = program;
    let base = copying.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
        .find_map(|instruction| match &mut instruction.kind {
            InstructionKind::VariantExtract { base, .. } => Some(base),
            _ => None,
        })
        .unwrap();
    base.mode = UseMode::Read;
    assert!(copying
        .validate()
        .unwrap_err()
        .iter()
        .any(|error| error.message.contains("must consume the wrapper")));
}

#[test]
fn ir_rejects_a_second_borrow_option_initializer_without_an_intervening_move() {
    use memobits_ir::InstructionKind;

    let mut program = lower(
        "fn main() {
            let first: (borrow i32)? = None;
            let second: (borrow i32)? = None;
        }",
    );
    let mut targets = program.functions[0].blocks[0]
        .instructions
        .iter_mut()
        .filter_map(|instruction| match &mut instruction.kind {
            InstructionKind::Assign {
                target,
                initialize: true,
                ..
            } => Some(target),
            _ => None,
        });
    let first = *targets.next().unwrap();
    *targets.next().unwrap() = first;
    let errors = program.validate().unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("more than one initialization site")),
        "{errors:?}"
    );
}

#[test]
fn borrow_option_reborrow_freezes_its_parent_share_until_last_use() {
    let source = "type P { x: i32 }
        fn update(parent: share P) -> i32 {
            let wrapped: (borrow P)? = Some(parent.borrow());
            let old := match wrapped {
                Some(r) => { let old := r.x; parent.x = 8; old },
                None => 0
            };
            old + parent.x
        }
        fn main() -> i32 { var owner := P { x: 7 }; update(owner.share()) }";
    assert!(memobits_ownership::check_ownership(&lower(source)).is_empty());
    for before_last_use in [
        source.replace(
            "let old := match wrapped",
            "parent.x = 8; let old := match wrapped",
        ),
        source.replace(
            "let old := r.x; parent.x = 8;",
            "parent.x = 8; let old := r.x;",
        ),
    ] {
        let errors = memobits_ownership::check_ownership(&lower(&before_last_use));
        assert!(
            errors.iter().any(|error| error.code.to_string() == "BE005"),
            "{errors:?}"
        );
    }
}

#[test]
fn borrow_option_loan_is_live_only_on_branches_that_use_it() {
    let source = "fn branch(flag: bool) -> i32 {
        var owner := 7;
        let wrapped: (borrow i32)? = Some(owner.borrow());
        if flag { match wrapped { Some(r) => r.copy(), None => 0 } }
        else { owner = 9; owner }
    }
    fn main() -> i32 { branch(true) + branch(false) }";
    assert!(memobits_ownership::check_ownership(&lower(source)).is_empty());

    let before_split = source.replace("if flag", "owner = 8; if flag");
    let errors = memobits_ownership::check_ownership(&lower(&before_split));
    assert!(
        errors.iter().any(|error| error.code.to_string() == "BE005"),
        "{errors:?}"
    );
}
