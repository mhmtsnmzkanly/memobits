use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_ir::{Constant, InstructionKind, Primitive, Program, Type};
use memobits_syntax::parse;

fn lower(source: &str) -> Program {
    let parsed = parse(SourceId(13), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let program = lower_module(&parsed.module, "test", &["main".into()]).unwrap();
    program.validate().unwrap();
    program
}
fn move_codes(source: &str) -> Vec<String> {
    memobits_ownership::check_moves(&lower(source))
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

fn lowering_codes(source: &str) -> Vec<String> {
    let parsed = parse(SourceId(13), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_err()
        .iter()
        .map(|diagnostic| diagnostic.code.to_string())
        .collect()
}

#[test]
fn lowers_numeric_facts_shadowing_and_signed_minimum() {
    let program = lower("fn f(x: i8) -> i8 { let x: i8 = -128; x + 1 }");
    let function = &program.functions[0];
    assert_eq!(function.locals.len(), 2);
    assert_eq!(function.locals[0].ty, Type::Primitive(Primitive::I8));
    assert_eq!(function.locals[1].ty, Type::Primitive(Primitive::I8));
    assert!(function.blocks.iter().flat_map(|b| &b.instructions).any(
        |i| matches!(&i.kind, InstructionKind::Constant(Constant::Integer(v)) if v == "-128")
    ));
    assert!(memobits_ownership::check_moves(&program).is_empty());
}

#[test]
fn lowers_calls_and_detects_repeated_owned_move() {
    assert!(
        move_codes("fn id(x: i32) -> i32 { x } fn main() -> i32 { let x := 1; id(x) }").is_empty()
    );
    assert!(move_codes(
        "fn g(a: Array<i32, 1>, b: Array<i32, 1>) {} fn main() { let x := [1]; g(x, x); }"
    )
    .contains(&"BE001".into()));
    assert!(
        move_codes("fn main() { let x := [1]; let y := x; x[0] + 1; }").contains(&"BE001".into())
    );
    // Primitives are copied implicitly.
    assert!(move_codes("fn g(a: i32, b: i32) {} fn main() { let x := 1; g(x, x); }").is_empty());
    assert!(move_codes("fn main() -> i32 { let x := 1; let y := x; x + y }").is_empty());
}

#[test]
fn captures_operands_before_later_side_effects() {
    let program =
        lower("fn g(a: i32, b: i32) {} fn main() { var x := 1; g(x, { x = 2; 0 }); x + 1; }");
    assert!(memobits_ownership::check_moves(&program).is_empty());
    let main = &program.functions[1];
    let instructions = &main.blocks[0].instructions;
    let first_capture = instructions
        .iter()
        .position(|i| {
            matches!(
                i.kind,
                InstructionKind::Capture(_) | InstructionKind::Copy { .. }
            )
        })
        .unwrap();
    let reassignment = instructions
        .iter()
        .position(|i| {
            matches!(
                i.kind,
                InstructionKind::Assign {
                    initialize: false,
                    ..
                }
            )
        })
        .unwrap();
    assert!(first_capture < reassignment);

    let invalid = lower(
        "fn g(a: Array<i32, 1>, b: i32) {} fn main() { let x := [1]; g(x, { let y := x; 0 }); }",
    );
    assert!(memobits_ownership::check_moves(&invalid)
        .iter()
        .any(|diagnostic| diagnostic.code.to_string() == "BE001"));
}

#[test]
fn captures_binary_and_compound_assignment_left_values_first() {
    for source in [
        "fn main() { var x := 1; x + { x = 2; 0 }; }",
        "fn main() { var x := 1; x += { x = 2; 0 }; }",
    ] {
        let program = lower(source);
        let main = &program.functions[0];
        let instructions = &main.blocks[0].instructions;
        let capture = instructions
            .iter()
            .position(|i| matches!(i.kind, InstructionKind::Capture(_)))
            .unwrap();
        let reassignment = instructions
            .iter()
            .position(|i| {
                matches!(
                    i.kind,
                    InstructionKind::Assign {
                        initialize: false,
                        ..
                    }
                )
            })
            .unwrap();
        assert!(capture < reassignment, "{source}");
    }
}

#[test]
fn rejects_proven_integer_overflow_and_division_errors() {
    for source in [
        "fn main() -> i32 { 2147483647 + 1 }",
        "fn main() { let x: i8 = 127 + 1; }",
        "fn main() { let x: u8 = 255 + 1; }",
        "fn main() { let x: u64 = 18446744073709551615 + 1; }",
        "fn main() { let x: u64 = 18446744073709551615 * 18446744073709551615; }",
        "fn main() -> i32 { -2147483648 / -1 }",
    ] {
        assert!(lowering_codes(source).contains(&"LE001".into()), "{source}");
    }
    assert!(lowering_codes("fn main() -> i32 { 1 / 0 }").contains(&"LE002".into()));
}

#[test]
fn accepts_integer_boundaries_dynamic_values_and_ieee_float_results() {
    for source in [
        "fn main() -> i32 { 2147483646 + 1 }",
        "fn main() { let x: i8 = -128; }",
        "fn main() { let x: u8 = 255; }",
        "fn main() { let x: u64 = 18446744073709551615; }",
        "fn next() -> i32 { 1 } fn main() -> i32 { next() + 1 }",
        "fn main() -> f64 { 1e308 * 1e308 }",
    ] {
        let parsed = parse(SourceId(13), source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = lower_module(&parsed.module, "test", &["main".into()]);
        assert!(result.is_ok(), "{source}: {result:?}");
    }
}

#[test]
fn branch_join_and_reinitialization_have_expected_availability() {
    assert!(
        move_codes("fn main() { var x := [1]; if true { let y := x; } else {} x[0] + 1; }")
            .contains(&"BE001".into())
    );
    assert!(move_codes(
        "fn main() { var x := [1]; loop { let y := x; x = [2]; break; } x[0] + 1; }"
    )
    .is_empty());
    assert!(
        move_codes("fn main() { var x := [1]; loop { let y := x; break; } x[0] + 1; }")
            .contains(&"BE001".into())
    );
}

#[test]
fn lowers_if_values_short_circuit_and_nested_loops() {
    for source in [
        "fn f(x: Bool) -> i32 { if x { 1 } else { 2 } }",
        "fn f(x: Bool) -> Bool { x && true || false }",
        "fn f() { loop { if true { break; } else { continue; } } }",
        "fn f() -> i32 { loop { loop { break; } return 1; } }",
        "fn f() -> i32 { 1 + { return 2; }; }",
    ] {
        let program = lower(source);
        assert!(
            memobits_ownership::check_moves(&program).is_empty(),
            "{source}"
        );
    }
}

#[test]
fn mixed_return_paths_and_divergence_validate() {
    for source in [
        "fn f(x: Bool) -> i32 { if x { return 1; } else { 2 } }",
        "fn f() -> i32 { loop {} }",
        "fn f() -> Bool { true || { return false; true } }",
        "fn f() { let x := { return; }; }",
    ] {
        let program = lower(source);
        assert!(
            memobits_ownership::check_moves(&program).is_empty(),
            "{source}"
        );
    }
}

#[test]
fn invalid_inputs_do_not_return_ir() {
    let parsed = parse(SourceId(13), "fn f() -> i32 { break; 1 }");
    assert!(parsed.diagnostics.is_empty());
    assert!(lower_module(&parsed.module, "test", &["main".into()]).is_err());
    let parsed = parse(SourceId(13), "fn f() {}");
    assert!(parsed.diagnostics.is_empty());
    assert!(lower_module(&parsed.module, "", &["main".into()]).is_err());
}

#[test]
fn rejects_known_zero_divisor_with_dynamic_numerator() {
    for source in [
        "fn f(x: i32) -> i32 { x / 0 }",
        "fn f(x: u64) -> u64 { x % (2 - 2) }",
    ] {
        assert!(lowering_codes(source).contains(&"LE002".to_owned()));
    }
    lower("fn f(x: f64) -> f64 { x / 0.0 }");
    lower("fn f(x: i32, y: i32) -> i32 { x / y }");
}

#[test]
fn array_syntax_cannot_produce_executable_ir() {
    for source in [
        "fn main() { []; }",
        "fn main() { [1, 2]; }",
        "fn main() { [1; 2]; }",
        "fn main() { [1][0]; }",
    ] {
        assert!(lowering_codes(source).contains(&"TE017".into()), "{source}");
    }
}
