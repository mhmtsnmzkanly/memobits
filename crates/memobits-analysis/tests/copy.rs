//! Explicit primitive copy `expr.copy()`: type facts, diagnostics, lowering and
//! ownership behaviour.
use memobits_analysis::{check_typed_module, lower_module};
use memobits_diagnostics::SourceId;
use memobits_ir::{InstructionKind, Primitive, Type, UseMode};
use memobits_syntax::parse;

fn pipeline(source: &str) -> Result<memobits_ir::Program, Vec<String>> {
    let parsed = parse(SourceId(31), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let program = lower_module(&parsed.module, "test", &["main".into()]).map_err(|errors| {
        errors
            .iter()
            .map(|d| format!("{} {}", d.code, d.message))
            .collect::<Vec<_>>()
    })?;
    program.validate().unwrap();
    let mut errors = memobits_ownership::check_moves(&program);
    errors.extend(memobits_ownership::check_loans(&program));
    if errors.is_empty() {
        Ok(program)
    } else {
        Err(errors
            .iter()
            .map(|d| format!("{} {}", d.code, d.message))
            .collect())
    }
}

fn accepted(source: &str) -> memobits_ir::Program {
    pipeline(source).unwrap_or_else(|errors| panic!("{source}: {errors:?}"))
}

fn rejected(source: &str, code: &str) -> Vec<String> {
    let errors = pipeline(source).expect_err(source);
    assert!(
        errors.iter().any(|message| message.starts_with(code)),
        "{source}: {errors:?}"
    );
    errors
}

#[test]
fn copy_has_the_primitive_type_of_its_receiver() {
    for source in [
        "fn f(x: u8) -> u8 { x.copy() }",
        "fn f(r: borrow u8) -> u8 { r.copy() }",
        "fn f(r: share u8) -> u8 { r.copy() }",
    ] {
        let facts = check_typed_module(&parse(SourceId(32), source).module).unwrap();
        let copy = facts.functions[0]
            .expressions
            .iter()
            .find(|fact| &source[fact.span.start..fact.span.end] == "x.copy()")
            .or_else(|| {
                facts.functions[0]
                    .expressions
                    .iter()
                    .find(|fact| &source[fact.span.start..fact.span.end] == "r.copy()")
            })
            .unwrap();
        assert_eq!(copy.ty, Some(Type::Primitive(Primitive::U8)), "{source}");
    }
}

#[test]
fn copy_lowers_to_a_read_only_copy_instruction() {
    let program = accepted("fn f(x: i32) -> i32 { let y := x.copy(); x + y }");
    let copies: Vec<_> = program.functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match &instruction.kind {
            InstructionKind::Copy { source } => Some(source.mode),
            _ => None,
        })
        .collect();
    assert_eq!(copies, [UseMode::Read]);
}

#[test]
fn copy_reads_locals_parameters_and_elements_without_consuming() {
    accepted("fn main() -> i32 { let x := 1; let y := x.copy(); let z := x.copy(); x + y + z }");
    accepted("fn f(v: i64) -> i64 { let a := v.copy(); let b := v.copy(); a + b + v }");
    accepted("fn main() -> i32 { let a := [1, 2]; let x := a[1].copy(); a[0] + x }");
    accepted("fn f(i: i32, j: i32) -> i32 { let m := [[1, 2], [3, 4]]; let x := m[i][j].copy(); m[0][0] + x }");
    accepted(
        "fn main() -> i32 { let b := [true, false]; let t := b[0].copy(); if t { 1 } else { 0 } }",
    );
    accepted("fn main() -> f64 { let a := [1.5, 2.5]; a[0].copy() }");
}

#[test]
fn copy_reads_through_references() {
    accepted("fn f(r: borrow i32) -> i32 { let v := r.copy(); v + r }");
    accepted("fn f(r: share i32) -> i32 { r.copy() }");
    accepted("fn f(r: borrow Bool) -> Bool { r.copy() }");
    accepted("fn f(p: borrow Array<i32, 3>, i: i32) -> i32 { p[i].copy() }");
    accepted(
        "fn f(p: share Array<i32, 3>, i: i32) -> i32 { let v := p[i].copy(); p[0] = v.copy(); v }",
    );
    accepted("fn f(p: borrow Array<Array<u8, 2>, 2>) -> u8 { p[1][0].copy() }");
    accepted("fn main() -> i32 { var x := 1; let r := x.borrow(); let y := r.copy(); y + r }");
}

#[test]
fn copy_is_usable_in_every_owned_position() {
    accepted("fn main() { let x := 1; let y := x.copy(); var z := 0; z = x.copy(); }");
    accepted("fn take(v: i32) {} fn main() { let x := 1; take(x.copy()); take(x.copy()); }");
    accepted("fn main() -> i32 { let x := 1; return x.copy(); }");
    accepted("fn mk(v: i32) -> Array<i32, 3> { [v.copy(), v.copy() + 1, v + 2] }");
    accepted("fn main() { let x := 7; let a := [x.copy(); 3]; let b := [x.copy(); 1]; let c := [x.copy(); 0]; let d := [x.copy(); 100]; }");
    accepted("fn main() -> i32 { let x := 1; if true { x.copy() } else { 2 } }");
    accepted("fn main() -> i32 { let x := 1; let y := { x.copy() }; y }");
    accepted("fn main() { var a := [1, 2]; a[0] = a[1].copy(); }");
    accepted("fn main() { var a := [1, 2]; let t := a[0].copy(); a[0] = a[1].copy(); a[1] = t; }");
}

#[test]
fn copy_is_a_read_with_respect_to_loans() {
    accepted("fn main() -> i32 { var x := 1; let r := x.borrow(); let y := x.copy(); y + r }");
    accepted(
        "fn main() -> i32 { var a := [1, 2]; let r := a.borrow(); let y := a[0].copy(); y + r[1] }",
    );
    // Rejected exactly like a direct read.
    rejected(
        "fn main() -> i32 { var x := 1; let r := x.share(); let y := x.copy(); r + y }",
        "BE005",
    );
    rejected(
        "fn main() -> i32 { var x := 1; let r := x.share(); let y := x + 0; r + y }",
        "BE005",
    );
    rejected(
        "fn main() -> i32 { var a := [1, 2]; let r := a.share(); let y := a[0].copy(); r[0] + y }",
        "BE005",
    );
}

#[test]
fn copy_of_a_moved_local_is_rejected() {
    rejected(
        "fn main() -> i32 { let x := 1; let y := x; let z := x.copy(); y + z }",
        "BE001",
    );
    rejected(
        "fn take(v: i32) {} fn main() { let x := 1; take(x); let y := x.copy(); }",
        "BE001",
    );
    // The original is still moved by an ordinary use.
    rejected(
        "fn main() -> i32 { let x := 1; let y := x.copy(); let z := x; y + z + x }",
        "BE001",
    );
}

#[test]
fn copy_of_aggregates_and_bad_forms_are_rejected() {
    for source in [
        "fn main() { let a := [1, 2]; let b := a.copy(); }",
        "fn main() { let m := [[1, 2], [3, 4]]; let r := m[0].copy(); }",
        "fn f(p: borrow Array<i32, 2>) { let b := p.copy(); }",
        "fn f(p: share Array<i32, 2>) { let b := p.copy(); }",
        "fn f(p: borrow Array<Array<i32, 2>, 2>) { let b := p[0].copy(); }",
    ] {
        let errors = rejected(source, "TE017");
        assert!(
            errors
                .iter()
                .any(|m| m.contains("copy is currently available only for primitive values")),
            "{source}: {errors:?}"
        );
    }
    rejected("fn main() { let x := 1; let y := x.copy(2); }", "TE010");
    rejected(
        "fn main() { let x := 1; let y := x.copy(); let z: Bool = y; }",
        "TE002",
    );
}

#[test]
fn extraction_diagnostic_recommends_copy_and_arithmetic_still_works() {
    let errors = rejected("fn main() { let a := [1, 2]; let x := a[1]; }", "TE022");
    assert!(errors.iter().any(|m| m.contains("`.copy()`")), "{errors:?}");
    accepted("fn main() -> i32 { let a := [1, 2]; let x := a[1] + 0; x }");
}
