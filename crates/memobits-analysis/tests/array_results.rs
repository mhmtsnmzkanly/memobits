//! Array results, `if`/block array values and nested arrays: typing, lowering,
//! ownership and the forms that stay gated.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_ir::{Access, InstructionKind, Program, Source, TerminatorKind, Type};
use memobits_syntax::parse;

fn try_lower(source: &str) -> Result<Program, Vec<String>> {
    let parsed = parse(SourceId(41), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    lower_module(&parsed.module, "test", &["main".into()]).map_err(|errors| {
        errors
            .iter()
            .map(|diagnostic| diagnostic.code.to_string())
            .collect()
    })
}
fn lower(source: &str) -> Program {
    let program = try_lower(source).unwrap_or_else(|codes| panic!("{source}: {codes:?}"));
    program.validate().unwrap();
    program
}
fn codes(source: &str) -> Vec<String> {
    try_lower(source).expect_err(source)
}
fn ownership(source: &str) -> Vec<String> {
    memobits_ownership::check_ownership(&lower(source))
        .iter()
        .map(|diagnostic| diagnostic.code.to_string())
        .collect()
}
fn array(len: u32) -> Type {
    Type::Array {
        element: Box::new(Type::Primitive(memobits_ir::Primitive::I32)),
        len,
    }
}

#[test]
fn array_results_lower_to_array_typed_calls_and_returns() {
    let program = lower(
        "fn make() -> Array<i32, 2> { [1, 2] } \
         fn main() -> i32 { let a := make(); a[0] + 0 }",
    );
    assert_eq!(*program.functions[0].signature.result, array(2));
    let main = &program.functions[1];
    let call_output = main
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .find_map(|instruction| match &instruction.kind {
            InstructionKind::Call { .. } => instruction.output,
            _ => None,
        })
        .unwrap();
    assert_eq!(main.values[call_output.0 as usize], array(2));
    assert!(matches!(
        program.functions[0].blocks[0].terminator.kind,
        TerminatorKind::Return(Some(_))
    ));
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn array_valued_if_uses_an_array_typed_join_parameter() {
    let program =
        lower("fn f(c: Bool) -> i32 { let a := if c { [1, 2] } else { [3, 4] }; a[1] + 0 }");
    let function = &program.functions[0];
    let joins = function
        .blocks
        .iter()
        .flat_map(|block| &block.parameters)
        .collect::<Vec<_>>();
    assert_eq!(joins.len(), 1);
    assert_eq!(function.values[joins[0].0 as usize], array(2));
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn results_if_blocks_and_returns_accept_every_owned_source() {
    for source in [
        "fn f() -> Array<i32, 2> { [1; 2] }",
        "fn f(a: Array<i32, 2>) -> Array<i32, 2> { a }",
        "fn f() -> Array<i32, 2> { let a := [1, 2]; a }",
        "fn f() -> Array<i32, 2> { let a := [1, 2]; return a; }",
        "fn g() -> Array<i32, 2> { [1, 2] } fn f() -> Array<i32, 2> { g() }",
        "fn f(c: Bool) -> Array<i32, 2> { if c { return [1, 2]; } let r := [3, 4]; r }",
        "fn f(c: Bool) -> Array<i32, 2> { { [5, 6] } }",
        "fn f(c: Bool) -> Array<i32, 2> { if c { [1, 2] } else { if c { [3, 4] } else { [5, 6] } } }",
        "fn g(a: Array<i32, 2>) {} fn f() { g(if true { [1, 2] } else { [3, 4] }); }",
        "fn f() -> Array<Array<i32, 2>, 2> { [[1, 2], [3, 4]] }",
        "fn f() { var a := [0, 0]; a = if true { [1, 2] } else { [3, 4] }; }",
    ] {
        lower(source);
    }
}

#[test]
fn nested_arrays_lower_to_chained_element_addresses() {
    let program = lower(
        "fn main() -> i32 { var m := [[0; 2]; 3]; m[1][0] = 5; m[2][1] += 1; m[1][0] + m[2][1] }",
    );
    let shares = program.functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter(|instruction| {
            matches!(
                instruction.kind,
                InstructionKind::ElementAddr {
                    access: Access::Share,
                    ..
                }
            )
        })
        .count();
    // Two writes, each with a row address and an element address.
    assert!(shares >= 4);
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn nested_index_and_row_assignment_evaluate_indices_then_right_hand_side() {
    let program = lower(
        "fn f() -> i32 { 0 } fn g() -> i32 { 1 } fn h() -> i32 { 2 } \
         fn main() { var m := [[0; 2]; 2]; m[f()][g()] = h(); }",
    );
    let main = &program.functions[3];
    let mut calls = Vec::new();
    let mut first_share = None;
    let mut last_call = 0;
    for (position, instruction) in main
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .enumerate()
    {
        match &instruction.kind {
            InstructionKind::Call { callee, .. } => {
                if let Source::Function(id) = callee.source {
                    calls.push(id.0);
                    last_call = position;
                }
            }
            InstructionKind::ElementAddr {
                access: Access::Share,
                ..
            } => {
                first_share.get_or_insert(position);
            }
            _ => {}
        }
    }
    assert_eq!(calls, [0, 1, 2]);
    // Every call precedes the first checked address of the write.
    assert!(first_share.unwrap() > last_call);
}

#[test]
fn nested_array_parameters_rows_and_row_references_lower() {
    lower(
        "fn t(m: borrow Array<Array<i32, 2>, 2>) -> i32 { m[0][0] + m[1][1] } \
         fn f(m: share Array<Array<i32, 2>, 2>) { m[0][1] = 1; m[1] = [2, 3]; } \
         fn r(a: borrow Array<i32, 2>) -> i32 { a[0] + 0 } \
         fn w(a: share Array<i32, 2>) { a[0] = 9; } \
         fn main() -> i32 { var m := [[1, 2], [3, 4]]; w(m[1].share()); \
           let b := m[0].borrow(); r(b) + r(m[1].borrow()) + t(m.borrow()) }",
    );
}

#[test]
fn row_extraction_into_owned_positions_is_rejected_with_te022() {
    for source in [
        "fn main() { let m := [[1, 2], [3, 4]]; let r := m[0]; }",
        "fn f(a: Array<i32, 2>) {} fn main() { let m := [[1, 2], [3, 4]]; f(m[0]); }",
        "fn main() { var m := [[1, 2], [3, 4]]; m[0] = m[1]; }",
        "fn main() { var a := [1, 2]; let m := [[1, 2], [3, 4]]; a = m[1]; }",
        "fn f(m: borrow Array<Array<i32, 2>, 2>) -> Array<i32, 2> { m[0] }",
        "fn f(m: borrow Array<Array<i32, 2>, 2>) -> Array<i32, 2> { return m[0]; }",
        "fn main() { let m := [[1, 2], [3, 4]]; let n := [m[0], m[1]]; }",
        "fn main() { let m := [[1, 2], [3, 4]]; m[0]; }",
    ] {
        assert!(codes(source).contains(&"TE022".into()), "{source}");
    }
    // Primitive elements are copied implicitly.
    lower("fn main() { let m := [1, 2]; let x := m[0]; }");
}

#[test]
fn constant_indices_are_checked_on_every_level() {
    for source in [
        "fn main() { let m := [[1, 2], [3, 4]]; m[0][2] + 0; }",
        "fn main() { let m := [[1, 2], [3, 4]]; m[2][0] + 0; }",
        "fn main() { var m := [[1, 2], [3, 4]]; m[0][-1] = 1; }",
        "fn main() { var m := [[1, 2], [3, 4]]; m[5] = [1, 2]; }",
        "fn f(m: borrow Array<Array<i32, 2>, 2>) -> i32 { m[1][2] + 0 }",
    ] {
        assert!(codes(source).contains(&"TE008".into()), "{source}");
    }
}

#[test]
fn nested_type_errors() {
    assert!(codes("fn main() { let m := [[1, 2], [3]]; }").contains(&"TE002".into()));
    assert!(
        codes("fn main() { let m: Array<Array<i32, 2>, 2> = [[1, 2], [3, 4], [5, 6]]; }")
            .contains(&"TE002".into())
    );
    assert!(codes("fn main() { var m := [[1, 2]]; m[0] = [1, 2, 3]; }").contains(&"TE002".into()));
    assert!(codes("fn main() { var m := [[1, 2]]; m[0] += 1; }").contains(&"TE007".into()));
    assert!(codes("fn main() { let m := [[1, 2]]; m[0][0] = 1; }").contains(&"TE004".into()));
    assert!(codes("fn main() { let m := [[1, 2]]; m[0] = [3, 4]; }").contains(&"TE004".into()));
    assert!(codes("fn f() -> Array<i32, 2> { [1, 2, 3] }").contains(&"TE002".into()));
    assert!(codes("fn f() -> Array<i32, 2> { 1 }").contains(&"TE002".into()));
    assert!(
        codes("fn main() { let a := if true { [1, 2] } else { [3] }; }").contains(&"TE013".into())
    );
}

#[test]
fn forms_that_stay_gated_report_te017() {
    for source in [
        // indexing a temporary
        "fn make() -> Array<i32, 2> { [1, 2] } fn main() { let x := make()[0] + 1; }",
        "fn main() { let x := [[1, 2], [3, 4]][0][1] + 1; }",
        // references to primitive elements and to temporaries
        "fn main() { var m := [[1, 2], [3, 4]]; let r := m[0][1].share(); }",
        "fn main() { var m := [[1, 2], [3, 4]]; let r := m[0][1].borrow(); }",
        "fn g(a: borrow Array<i32, 2>) {} fn main() { g([1, 2].borrow()); }",
        // sharing rows needs a mutable owner and cannot come from a borrow
        "fn g(a: share Array<i32, 2>) {} fn main() { let m := [[1, 2]]; g(m[0].share()); }",
        "fn g(a: share Array<i32, 2>) {} fn f(m: borrow Array<Array<i32, 2>, 1>) { g(m[0].share()); }",
        // whole arrays outside owned positions
        "fn main() { let m := [[1, 2]]; m; }",
        "fn main() { if true { [1, 2]; } }",
        // reference elements
        "fn main() { var x := 1; let a := [x.borrow()]; }",
        "fn f(a: borrow Array<i32, 2>) -> i32 { a }",
        "fn f(a: borrow Array<i32, 2>) -> Array<i32, 2> { a }",
        "fn f(a: borrow Array<i32, 2>) { let b := if true { a } else { a }; }",
        // array results are never references
        "fn f(a: share Array<i32, 2>) -> Array<i32, 2> { return a; }",
    ] {
        assert!(codes(source).contains(&"TE017".into()), "{source}");
    }
}

#[test]
fn results_and_values_follow_move_rules() {
    assert!(ownership(
        "fn make() -> Array<i32, 2> { [1, 2] } fn main() { let a := make(); let b := a; }"
    )
    .is_empty());
    for source in [
        "fn make() -> Array<i32, 2> { [1, 2] } fn main() { let a := make(); let b := a; a[0] + 0; }",
        "fn make() -> Array<i32, 2> { let a := [1, 2]; let b := a; a }",
        "fn make() -> Array<i32, 2> { let a := [1, 2]; let b := a; return a; }",
        "fn id(a: Array<i32, 2>) -> Array<i32, 2> { a } fn main() { let a := [1, 2]; let b := id(a); a[0] + 0; }",
        "fn main() { let x := [1, 2]; let y := [3, 4]; let z := if true { x } else { y }; x[0] + 0; }",
        "fn main() { let x := [1, 2]; let y := [3, 4]; let z := if true { x } else { y }; y[0] + 0; }",
        "fn main() { let x := [1, 2]; let n := [x; 3]; }",
        "fn main() { let x := [1, 2]; let n := [x, x]; }",
        "fn main() { let x := [1, 2]; let n := { x }; x[0] + 0; }",
        "fn main() { let r := [1, 2]; let m := [[1, 2], r]; r[0] + 0; }",
    ] {
        assert!(ownership(source).contains(&"BE001".into()), "{source}");
    }
    // A moved `var` array can be reassigned from a result and used again.
    assert!(ownership(
        "fn id(a: Array<i32, 2>) -> Array<i32, 2> { a } \
         fn main() -> i32 { var a := [1, 2]; a = id(a); a[0] + 0 }"
    )
    .is_empty());
}

#[test]
fn writes_conflict_with_live_borrows_of_the_whole_nested_array() {
    for source in [
        "fn main() -> i32 { var m := [[1, 2], [3, 4]]; let r := m.borrow(); m[1][0] = 9; r[0][0] + 0 }",
        "fn main() -> i32 { var m := [[1, 2], [3, 4]]; let r := m[0].borrow(); m[0][0] += 1; r[1] + 0 }",
        "fn main() -> i32 { var m := [[1, 2], [3, 4]]; let r := m[0].borrow(); m[0] = [1, 1]; r[0] + 0 }",
        "fn two(a: share Array<i32, 2>, b: share Array<i32, 2>) {} \
         fn main() { var m := [[1, 2], [3, 4]]; two(m[0].share(), m[0].share()); }",
        "fn mixed(a: share Array<i32, 2>, b: borrow Array<i32, 2>) {} \
         fn main() { var m := [[1, 2], [3, 4]]; mixed(m[0].share(), m[0].borrow()); }",
    ] {
        assert!(ownership(source).contains(&"BE005".into()), "{source}");
    }
    // Provably different constant rows are disjoint (A4 field-disjoint loans).
    for source in [
        "fn main() -> i32 { var m := [[1, 2], [3, 4]]; let r := m[0].borrow(); m[1][0] = 9; r[0] + 0 }",
        "fn main() -> i32 { var m := [[1, 2], [3, 4]]; let r := m[0].borrow(); m[1] = [1, 1]; r[0] + 0 }",
        "fn two(a: share Array<i32, 2>, b: share Array<i32, 2>) {} \
         fn main() { var m := [[1, 2], [3, 4]]; two(m[0].share(), m[1].share()); }",
        "fn mixed(a: share Array<i32, 2>, b: borrow Array<i32, 2>) {} \
         fn main() { var m := [[1, 2], [3, 4]]; mixed(m[0].share(), m[1].borrow()); }",
    ] {
        assert!(ownership(source).is_empty(), "{source}: {:?}", ownership(source));
    }
    // Once the borrow is dead the write is fine, and borrows can overlap.
    assert!(ownership(
        "fn rd(a: borrow Array<i32, 2>, b: borrow Array<i32, 2>) -> i32 { a[0] + b[0] } \
         fn main() -> i32 { var m := [[1, 2], [3, 4]]; let r := m[0].borrow(); let x := r[0] + 0; \
           m[1][0] = x; rd(m[0].borrow(), m[1].borrow()) }"
    )
    .is_empty());
}
