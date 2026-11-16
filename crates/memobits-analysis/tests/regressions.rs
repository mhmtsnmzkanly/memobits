use memobits_analysis::check_types;
use memobits_diagnostics::SourceId;
use memobits_syntax::parse;

fn check(source: &str) -> Vec<memobits_diagnostics::Diagnostic> {
    let parsed = parse(SourceId(11), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    check_types(&parsed.module)
}

#[test]
fn return_inside_binding_initializer_completes_function() {
    let source = "fn f() -> i32 { let x := { return 1; }; }";
    let diagnostics = check(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
}

#[test]
fn numeric_literal_on_left_uses_right_operand_type() {
    let source = "fn f(x: i64) { let y := 1 + x; }";
    let diagnostics = check(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
}

#[test]
fn boolean_operators_check_both_operands() {
    let good = check("fn f(x: Bool) -> Bool { true && x || false }");
    assert!(good.is_empty(), "{good:?}");
    let bad = check("fn f() -> Bool { true && 1 }");
    assert!(bad.iter().any(|d| d.code.to_string() == "TE002"), "{bad:?}");
}

#[test]
fn diverging_loops_satisfy_nonunit_return_completeness() {
    for source in [
        "fn f() -> i32 { loop {} }",
        "fn f() -> i32 { loop { return 1; } }",
        "fn f() -> i32 { loop { loop { break; } } }",
        "fn f() -> i32 { loop { if true { continue; } else { return 1; } } }",
    ] {
        let diagnostics = check(source);
        assert!(diagnostics.is_empty(), "{source}: {diagnostics:?}");
    }
}

#[test]
fn reachable_break_requires_a_result_after_loop() {
    for source in [
        "fn f() -> i32 { loop { break; } }",
        "fn f() -> i32 { loop { if true { break; } else { return 1; } } }",
        "fn f() -> i32 { loop { let x := { break; 1 }; } }",
    ] {
        let diagnostics = check(source);
        assert!(
            diagnostics.iter().any(|d| d.code.to_string() == "TE002"),
            "{source}: {diagnostics:?}"
        );
    }
    assert!(check("fn f() -> i32 { loop { break; } 2 }").is_empty());
}

#[test]
fn nested_expression_divergence_follows_evaluation_order() {
    for source in [
        "fn f() -> i32 { 1 + { return 2; }; }",
        "fn g(x: i32) {} fn f() -> i32 { g({ return 2; }); }",
        "fn f() -> i32 { if { return 2; true } { 1 } else { 3 } }",
    ] {
        let diagnostics = check(source);
        assert!(diagnostics.is_empty(), "{source}: {diagnostics:?}");
    }
}

#[test]
fn short_circuit_rhs_does_not_prove_return() {
    for source in [
        "fn f() -> i32 { true || { return 1; false }; }",
        "fn f() -> i32 { false && { return 1; true }; }",
    ] {
        let diagnostics = check(source);
        assert!(
            diagnostics.iter().any(|d| d.code.to_string() == "TE002"),
            "{source}: {diagnostics:?}"
        );
    }
}
