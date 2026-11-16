use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_ir::{InstructionKind, UseMode};
use memobits_syntax::parse;

fn lower(source: &str) -> memobits_ir::Program {
    let parsed = parse(SourceId(32), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    lower_module(&parsed.module, "test", &["main".into()]).unwrap()
}
fn accepted(source: &str) {
    let errors = memobits_ownership::check_ownership(&lower(source));
    assert!(errors.is_empty(), "{source}: {errors:?}");
}
fn rejected(source: &str) {
    let errors = memobits_ownership::check_ownership(&lower(source));
    assert!(!errors.is_empty(), "{source}");
}

#[test]
fn primitive_reads_and_writes_use_explicit_reference_instructions() {
    let program = lower("fn f(x: borrow i32, y: share i32) -> i32 { y += -x; y + 1 }");
    let instructions: Vec<_> = program.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .collect();
    assert!(instructions.iter().any(|i| matches!(i.kind, InstructionKind::Load { reference } if reference.mode == UseMode::Borrow)));
    assert!(instructions
        .iter()
        .any(|i| matches!(i.kind, InstructionKind::Store { .. })));
    assert!(memobits_ownership::check_ownership(&program).is_empty());
    accepted("fn f(x: borrow Bool) -> i32 { if x && !x { 1 } else { 2 } }");
}

#[test]
fn owner_access_resumes_after_the_last_reference_use() {
    accepted("fn f() { var x := 1; let r := x.borrow(); r + 1; x = 2; }");
    rejected("fn f() { var x := 1; let r := x.borrow(); x = 2; r + 1; }");
    accepted("fn f() { var x := 1; let a := x.borrow(); let b := x.borrow(); a + b; x = 2; }");
    rejected("fn f() { var x := 1; let a := x.borrow(); let b := x.share(); a + b; }");
}

#[test]
fn moving_reference_bindings_preserves_move_checks_and_loans() {
    accepted("fn f() { var x := 1; let a := x.borrow(); let b := a; b + 1; x = 2; }");
    rejected("fn f() { let x := 1; let a := x.borrow(); let b := a; a + b; }");
    rejected("fn f() { var x := 1; let a := x.borrow(); let b := a; x = 2; b + 1; }");
}

#[test]
fn branch_uses_keep_references_live_only_as_needed() {
    accepted("fn f(flag: Bool) { var x := 1; let r := x.borrow(); if flag { r + 1; } else { r + 2; }; x = 2; }");
    rejected(
        "fn f(flag: Bool) { var x := 1; let r := x.borrow(); if flag { x = 2; } else {}; r + 1; }",
    );
}

#[test]
fn call_arguments_keep_reborrow_loans_live_across_later_arguments() {
    accepted("fn g(a: borrow i32, b: borrow i32) {} fn f() { let x := 1; let r := x.borrow(); g(r, r); }");
    accepted("fn g(a: share i32) { a += 1; } fn f() { var x := 1; var r := x.share(); g(r); r += 1; x = 2; }");
    rejected("fn g(a: borrow i32, b: i32) {} fn f() { var x := 1; let r := x.borrow(); g(r, { x = 2; 0 }); }");
    rejected(
        "fn g(a: share i32, b: share i32) {} fn f() { var x := 1; let r := x.share(); g(r, r); }",
    );
}

#[test]
fn reference_loops_and_mutation_capabilities_are_checked() {
    accepted("fn f(flag: Bool) { var x := 1; loop { let r := x.borrow(); r + 1; x = 2; if flag { break; } } }");
    rejected("fn f(flag: Bool) { var x := 1; let r := x.borrow(); loop { x = 2; if flag { break; } } r + 1; }");
    let p =
        lower("fn g(x: share i32) { x += 1; } fn f() { var x := 1; let r := x.share(); g(r); }");
    let ds = memobits_ownership::check_ownership(&p);
    assert!(ds.iter().any(|d| d.code.to_string() == "BE004"), "{ds:?}");
    accepted("fn g(x: share i32) { x += 1; } fn f() { var x := 1; var r := x.share(); g(r); }");
}

#[test]
fn short_circuit_reference_reads_produce_owned_boolean_results() {
    accepted("fn f(x: borrow Bool) -> Bool { true && x }");
    accepted("fn f(x: borrow Bool) -> Bool { false || x }");
    accepted("fn f(x: share Bool) -> Bool { true && x }");
    accepted("fn f(x: borrow Bool) -> Bool { let result := false || x; result }");
}
