use memobits_analysis::check_types;
use memobits_diagnostics::{Diagnostic, SourceId};
use memobits_syntax::parse;

fn check(source: &str) -> Vec<Diagnostic> {
    let parsed = parse(SourceId(9), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    check_types(&parsed.module)
}
fn codes(source: &str) -> Vec<String> {
    check(source).iter().map(|d| d.code.to_string()).collect()
}

#[test]
fn string_literals_are_owned_in_type_analysis() {
    let source = r#"
        type Text = String;
        fn inspect(s: borrow Text) {}
        fn take(s: String) -> String { s }
        fn f() {
            let text: Text = "é";
            inspect(text.borrow());
            let moved := take(text);
            inspect(moved.borrow());
            let empty := "";
            inspect(empty.borrow());
        }
    "#;
    let diagnostics = check(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    for (source, expected) in [
        (r#"fn f() { let s: String = 1; }"#, "TE002"),
        (
            r#"fn take(s: String) {} fn f(s: borrow String) { take(s); }"#,
            "TE002",
        ),
        (r#"fn f() { let s := "é"; s.copy(); }"#, "TE017"),
    ] {
        assert!(
            codes(source).iter().any(|code| code == expected),
            "{source}"
        );
    }
}

#[test]
fn string_literals_lower_to_owned_ir_with_utf8_payloads() {
    use memobits_ir::{Constant, InstructionKind, Type};

    let parsed = parse(
        SourceId(9),
        r#"fn f() -> String { let empty := ""; "é😀" }"#,
    );
    let program =
        memobits_analysis::lower_module(&parsed.module, "test", &["main".into()]).unwrap();
    let function = &program.functions[0];
    assert_eq!(*function.signature.result, Type::String);

    let literals: Vec<_> = function
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| {
            let InstructionKind::Constant(Constant::String(text)) = &instruction.kind else {
                return None;
            };
            assert_eq!(
                function.values[instruction.output.unwrap().0 as usize],
                Type::String
            );
            Some(text.as_bytes())
        })
        .collect();
    assert_eq!(literals, [b"".as_slice(), "é😀".as_bytes()]);
}

#[test]
fn accepts_defaults_annotations_and_local_calls() {
    for source in [
        "fn main() { let a := 1; let b := 1.5; let c: i64 = 9; let d: f32 = 2.5; a + 2; b + 3.0; c + 3; d + 4.0; }",
        "fn double(x: i64) -> i64 { x + 2 } fn main() -> i64 { double(4) }",
        "fn main() { var x: i32 = 1; x += 2; x = 3; }",
        "fn choice(x: Bool) -> i32 { if x { 1 } else { 2 } }",
        "fn absolute(x: Bool) -> i32 { if x { return 1; } else { return 2; } }",
        "fn main() { if true { let x := 1; } }",
        "fn main() { let x := 1; let x := x + 1; x; }",
        "fn main() { let x: i8 = -128; let y := -2147483648; let z: i64 = -9223372036854775808; }",
    ] {
        assert!(codes(source).is_empty(), "{source}: {:?}", check(source));
    }
}

#[test]
fn checks_bindings_operators_conditions_and_branches() {
    assert!(codes("fn main() { let x: Bool = 1; }").contains(&"TE002".into()));
    assert!(codes("fn main() { true + 1; }").contains(&"TE007".into()));
    assert!(codes("fn main() { if 1 { 2; } }").contains(&"TE002".into()));
    assert!(codes("fn main() { if true { 1 } else { false }; }").contains(&"TE013".into()));
    assert!(codes("fn main() { 1 && true; }").contains(&"TE002".into()));
    assert!(codes("fn main() { 1.0 % 2.0; }").contains(&"TE007".into()));
    assert!(codes("fn main() { let x: i8 = -129; }").contains(&"TE008".into()));
    assert!(codes("fn main() { let x: u64 = 18446744073709551616; }").contains(&"TE008".into()));
}

#[test]
fn checks_calls_assignments_and_returns() {
    assert!(codes("fn f(x: i32) {} fn main() { f(); }").contains(&"TE010".into()));
    assert!(codes("fn f(x: Bool) {} fn main() { f(1); }").contains(&"TE002".into()));
    assert!(codes("fn main() { let x := 1; x = 2; }").contains(&"TE004".into()));
    assert!(codes("fn main() { var x := 1; x = false; }").contains(&"TE002".into()));
    assert!(codes("fn main() -> Bool { return 1; }").contains(&"TE002".into()));
    assert!(codes("fn main() -> i32 { if true { return 1; } }").contains(&"TE002".into()));
    assert!(codes("fn main() -> i32 { loop { return 1; } }").is_empty());
}

#[test]
fn unsupported_features_are_reported_with_spans() {
    for source in [
        "use other::name;",
        "fn main(x: User) {}",
        "fn main() { other::value; }",
        "fn main() { 1.field; }",
    ] {
        let diagnostics = check(source);
        assert!(!diagnostics.is_empty(), "{source}");
        assert!(diagnostics.iter().all(|d| d.span.is_some()), "{source}");
    }
}

#[test]
fn primitive_references_support_reads_and_target_writes() {
    for source in [
        "fn f(x: borrow i64) -> i64 { -x + 1 }",
        "fn f(x: borrow i32) -> Bool { 1 < x && x == 2 }",
        "fn f(x: share i32) { x = 1; x += 2; }",
        "fn f(x: borrow Bool) -> i32 { if x { 1 } else { 2 } }",
        "fn f(var x: i32) { var r := x.share(); r = 2; r += 1; }",
        "fn inspect(x: borrow i32) {} fn f(var x: i32) { let r := x.share(); inspect(r.borrow()); }",
    ] { assert!(codes(source).is_empty(), "{source}: {:?}", codes(source)); }
}

#[test]
fn primitive_reads_through_references_copy_into_owned_positions() {
    for source in [
        "fn get(r: borrow i32) -> i32 { r }",
        "fn get(r: share i32) -> i32 { return r; }",
        "fn consume(x: i32) {} fn f(x: borrow i32) { consume(x); }",
        "fn f(x: borrow i32) { let y: i32 = x; }",
        "fn f(x: borrow Bool) -> Bool { x }",
    ] {
        assert!(codes(source).is_empty(), "{source}: {:?}", codes(source));
    }
}

#[test]
fn primitive_reference_escapes_and_invalid_writes_are_rejected() {
    for source in [
        "fn f(var x: i32) { var r := x.share(); r = x.share(); }",
        "fn f() { let r := 1.borrow(); }",
        "fn f() { let r := { let x := 1; x.borrow() }; }",
        "fn f(var x: i32) { let r := if true { x.borrow() } else { x.borrow() }; }",
        "fn f(var x: i32) { let r := x.borrow().borrow(); }",
    ] {
        assert!(
            codes(source).contains(&"TE017".into()),
            "{source}: {:?}",
            codes(source)
        );
    }
    for source in [
        "fn f(x: borrow i32) { x = 1; }",
        "fn f(var x: i32) { let r := x.share(); r = 1; }",
    ] {
        assert!(codes(source).contains(&"TE004".into()), "{source}");
    }
}

#[test]
fn fixed_bytes_use_array_length_and_element_rules() {
    assert!(codes("fn f() { let b: Bytes<0> = []; let a: Array<u8, 0> = b; }").is_empty());
    for (source, expected) in [
        ("fn f(b: Bytes<4_294_967_296>) {}", "TE008"),
        ("fn f(b: Bytes<2>) { let a: Array<u8, 3> = b; }", "TE002"),
        ("fn f(b: Bytes<2>) { let a: Array<i8, 2> = b; }", "TE002"),
    ] {
        let diagnostics = codes(source);
        assert!(
            diagnostics.iter().any(|code| code == expected),
            "{source}: {diagnostics:?}"
        );
    }
    for ty in ["Bytes<-1>", "Bytes<n>", "Bytes<1.0>", "Bytes<u8, 1>"] {
        let parsed = parse(SourceId(9), &format!("fn f(b: {ty}) {{}}"));
        assert!(!parsed.diagnostics.is_empty(), "{ty}");
    }
}

#[test]
fn fixed_arrays_infer_homogeneous_elements_and_contextual_literals() {
    for source in [
        "fn f() { let a := [1, 2]; let b: Array<i32, 2> = a; }",
        "fn f() { let a := [1.0, 2.0]; let b: Array<f64, 2> = a; }",
        "fn f() { let a: Array<i8, 3> = [-128, 0, 127]; }",
        "fn f() { let a: Array<Array<u8, 2>, 2> = [[1, 2], [3, 4]]; }",
        "fn f() { let a: Array<i32, 0> = []; let b: Array<Array<i8, 0>, 1> = [[]]; }",
        "fn make() -> i32 { 1 } fn f() { let a := [make(); 3]; let b: Array<i8, 0> = [127; 0]; }",
        "fn f(a: Array<i32, 2>) -> Array<i32, 2> { [1, 2] }",
        "fn f() { let a := [1; 4294967295]; }",
    ] {
        assert!(check(source).is_empty(), "{source}: {:?}", check(source));
    }
}

#[test]
fn fixed_arrays_reject_incompatible_elements_lengths_and_ranges() {
    for source in [
        "fn f() { let a := [1, false]; }",
        "fn f() { let a: Array<i32, 3> = [1, 2]; }",
        "fn f() { let a: Array<i32, 3> = [1; 2]; }",
        "fn f() { let a := []; }",
        "fn f() { let a: Array<i8, 1> = [128]; }",
        "fn f() { let a: Array<i8, 0> = [128; 0]; }",
        "fn f() { let a := [1; 4294967296]; }",
        "fn f(a: Array<i32, 99999999999999999999999999999999999999999999999999999>) {}",
        "fn f() { let a: Array<Array<i32, 2>, 1> = [[1]]; }",
    ] {
        assert!(!check(source).is_empty(), "{source}");
        assert!(check(source).iter().all(|d| d.span.is_some()));
    }
}

#[test]
fn fixed_arrays_keep_ownership_and_executable_ir_gated() {
    for source in [
        "fn f(x: i32) { let a := [x.borrow()]; }",
        "fn f(x: i32) { let a := [x.borrow(); 0]; }",
        "fn f() { [1] + [2]; }",
        "fn f() { [1] == [2]; }",
    ] {
        assert!(!check(source).is_empty(), "{source}");
    }
    // Array parameters and array references type-check and execute.
    for source in [
        "fn f() { let a := [1]; a.borrow(); }",
        "fn f(a: borrow Array<i32, 1>) {}",
        "fn f(a: Array<i32, 2>) {}",
        "fn take(a: Array<i32, 1>) {} fn f() { take([1]); }",
        "fn f() { let a := [[1], [2]]; }",
        "fn f() -> Array<i32, 2> { [1, 2] }",
    ] {
        assert!(check(source).is_empty(), "{source}");
        let parsed = parse(SourceId(9), source);
        assert!(memobits_analysis::check_typed_module(&parsed.module).is_ok());
    }
    for source in ["fn f() { [1, 2]; }", "fn f() { let a := [1, 2]; a; }"] {
        let parsed = parse(SourceId(9), source);
        let diagnostics = memobits_analysis::check_typed_module(&parsed.module).unwrap_err();
        assert!(diagnostics.iter().any(|d| d.code.to_string() == "TE017"));
    }
}

#[test]
fn zero_repetition_does_not_execute_element_control_flow() {
    let source = "fn f() -> i32 { let a: Array<Array<i32, 1>, 0> = [[{ return 1; }]; 0]; }";
    assert!(
        codes(source).contains(&"TE002".into()),
        "{source}: {:?}",
        check(source)
    );
}

#[test]
fn divergent_repeat_uses_contextual_element_type_and_matches_list_flow() {
    for source in [
        "fn f() { let a: Array<i32, 1> = [{ return; }; 1]; }",
        "fn f() -> i32 { let a: Array<i32, 1> = [{ return 1; }; 1]; }",
        "fn f() -> i32 { let a: Array<i32, 1> = [{ return 1; }]; }",
    ] {
        assert!(check(source).is_empty(), "{source}: {:?}", check(source));
    }
}

#[test]
fn array_index_checks_integer_type_and_constant_bounds() {
    assert!(check("fn f() { let x: i32 = [10, 20][1]; }").is_empty());
    assert!(codes("fn f() { let x: i32 = [10, 20][-1]; }").contains(&"TE008".into()));
    assert!(codes("fn f() { let x: i32 = [10, 20][true]; }").contains(&"TE007".into()));
    assert!(codes("fn f() { let x: i32 = [10, 20][2]; }").contains(&"TE008".into()));
    // Indexing a literal is type-correct but executable indexing needs a named local array.
    let parsed = parse(SourceId(9), "fn f() { let x: i32 = [10, 20][1]; }");
    assert!(memobits_analysis::check_typed_module(&parsed.module)
        .unwrap_err()
        .iter()
        .any(|d| d.code.to_string() == "TE017"));
}
