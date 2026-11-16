//! Executable lowering of `let` arrays with primitive elements read by index.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_ir::{Access, ArrayInit, InstructionKind, Primitive, Program, Type};
use memobits_syntax::parse;

fn lower(source: &str) -> Program {
    let parsed = parse(SourceId(21), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let program = lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"));
    program.validate().unwrap();
    program
}

fn codes(source: &str) -> Vec<String> {
    let parsed = parse(SourceId(21), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    lower_module(&parsed.module, "test", &["main".into()])
        .expect_err(source)
        .iter()
        .map(|diagnostic| diagnostic.code.to_string())
        .collect()
}

#[test]
fn literal_and_read_index_lower_to_array_new_and_element_addr_load() {
    let program = lower("fn main() -> i32 { let a := [1, 2, 3]; a[0] + a[2] }");
    let function = &program.functions[0];
    assert_eq!(
        function.locals[0].ty,
        Type::Array {
            element: Box::new(Type::Primitive(Primitive::I32)),
            len: 3
        }
    );
    let kinds = function
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .map(|instruction| &instruction.kind)
        .collect::<Vec<_>>();
    assert!(kinds.iter().any(
        |kind| matches!(kind, InstructionKind::ArrayNew { init: ArrayInit::Elements(e) } if e.len() == 3)
    ));
    let addresses = kinds
        .iter()
        .filter(|kind| {
            matches!(
                kind,
                InstructionKind::ElementAddr {
                    access: Access::Borrow,
                    ..
                }
            )
        })
        .count();
    assert_eq!(addresses, 2);
    assert!(memobits_ownership::check_moves(&program).is_empty());
    assert!(memobits_ownership::check_loans(&program).is_empty());
}

#[test]
fn annotated_empty_arrays_and_dynamic_indices_lower() {
    lower("fn main() { let a: Array<i32, 0> = []; }");
    lower("fn f(n: i64) -> i32 { let a := [4, 5]; a[n] + 0 }");
    lower("fn f(n: u8) -> Bool { let a := [true, false]; if a[n] { true } else { false } }");
    lower("fn f(n: i32) -> Bool { let a := [true, false]; a[n] && a[0] }");
    lower("fn f() -> i32 { let a := [1, 2]; let b := [3, 4]; a[b[0] - 3] + 0 }");
}

#[test]
fn extracting_an_element_into_an_owned_position_is_rejected() {
    for source in [
        "fn main() { let a := [1, 2]; let x := a[1]; }",
        "fn main() { let a := [1, 2]; var x := 0; x = a[1]; }",
        "fn main() -> i32 { let a := [1, 2]; return a[1]; }",
        "fn main() -> i32 { let a := [1, 2]; a[1] }",
        "fn take(x: i32) {} fn main() { let a := [1, 2]; take(a[1]); }",
        "fn main() { let a := [1, 2]; let b := [a[0], 1]; }",
        "fn main() -> i32 { let a := [1, 2]; if true { a[0] } else { 1 } }",
    ] {
        assert!(codes(source).contains(&"TE022".into()), "{source}");
    }
    lower("fn main() { let a := [1, 2]; var x := 0; x += a[1]; }");
}

#[test]
fn unsupported_array_forms_stay_gated() {
    for source in [
        // whole arrays as values outside a binding initializer or `=`
        "fn main() { let a := [1, 2]; a; }",
        "fn main() { let a := [1, 2]; let b := [a; 2]; }",
        "fn main() { let a := [1, 2]; let b := if true { a } else { a }; }",
        "fn main() { let a := [1, 2]; let b := { a }; }",
        "fn main() { let a := [1, 2]; let b := a; a = b + 1; }",
        // arrays in calls and results
        "fn take(a: Array<i32, 2>) {} fn main() { let a := [1, 2]; take(a); }",
        "fn take(a: borrow Array<i32, 2>) {}",
        "fn take(a: share Array<i32, 2>) {}",
        "fn make() -> Array<i32, 2> { [1, 2] }",
        // nested arrays and non-primitive elements
        "fn main() { let a := [[1], [2]]; }",
        "fn main() { let a: Array<Array<i32, 1>, 1> = [[1]]; }",
        "fn main() { let a := [[1]; 2]; }",
        "fn main() { var x := 1; let a := [x.borrow()]; }",
        // literals and repetition outside a binding initializer or `=`
        "fn main() { [1, 2]; }",
        "fn main() { [1; 2]; }",
        "fn main() { let x := [1, 2][0] + 1; }",
        "fn main() { let a := if true { [1] } else { [2] }; }",
        "fn main() { let a := { [1] }; }",
        "fn main() { let a := { [1; 2] }; }",
        // element references are not expressible yet
        "fn main() { var a := [1, 2]; let r := a[0].share(); }",
        // indexing a non-local
        "fn main() { var a := [[1], [2]]; a[0][0] = 1; }",
    ] {
        assert!(codes(source).contains(&"TE017".into()), "{source}");
    }
}

#[test]
fn element_assignment_requires_a_mutable_array() {
    for source in [
        "fn main() { let a := [1]; a[0] = 2; }",
        "fn main() { let a := [1]; a[0] += 2; }",
        "fn main() { let a := [1; 4]; a[0] *= 2; }",
    ] {
        assert!(codes(source).contains(&"TE004".into()), "{source}");
    }
    assert!(codes("fn main() { var a := [1, 2]; a[2] = 2; }").contains(&"TE008".into()));
    assert!(codes("fn main() { var a := [1, 2]; a[-1] += 2; }").contains(&"TE008".into()));
    assert!(codes("fn main() { var a := [1, 2]; a[0] = true; }").contains(&"TE002".into()));
    assert!(codes("fn main() { var a := [true]; a[0] += true; }").contains(&"TE007".into()));
    assert!(codes("fn main() { var a := [1, 2]; let b := a; b = a; }").contains(&"TE004".into()));
    assert!(codes("fn main() { [1, 2][0] = 3; }").contains(&"TE017".into()));
}

#[test]
fn mutable_arrays_assignment_and_whole_array_moves_lower() {
    lower("fn main() { var a := [1, 2]; a[0] = 3; a[1] += a[0] * 2; a[0] -= 1; a[0] /= 1; a[0] %= 5; }");
    lower("fn main() -> i32 { var a := [1, 2, 3]; var i := 1; a[i] = a[0] + 1; a[i - 1] += a[2]; a[0] + 0 }");
    lower("fn main() { var a := [1, 2]; let b := a; var c := [5, 6]; c = b; c = [7, 8]; c = [0; 2]; }");
    lower("fn main() { var a := [1.5, 2.5]; a[0] += 1.0; let b: Array<u8, 2> = [1; 2]; }");
    // The extraction rule also covers the right-hand side of an element write.
    assert!(codes("fn main() { var a := [1, 2]; a[0] = a[1]; }").contains(&"TE022".into()));
}

#[test]
fn element_assignment_orders_index_before_right_hand_side_and_addresses_late() {
    let program = lower(
        "fn i() -> i32 { 0 } fn v() -> i32 { 1 } fn main() { var a := [0, 0]; a[i()] = v(); }",
    );
    let main = &program.functions[2];
    let kinds = main
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .map(|instruction| &instruction.kind)
        .collect::<Vec<_>>();
    let call = |name: &str| {
        let id = program
            .functions
            .iter()
            .position(|f| f.path.name == name)
            .unwrap();
        kinds
            .iter()
            .position(|kind| {
                matches!(kind, InstructionKind::Call { callee, .. }
                    if matches!(callee.source, memobits_ir::Source::Function(f) if f.0 as usize == id))
            })
            .unwrap()
    };
    let address = kinds
        .iter()
        .position(|kind| {
            matches!(
                kind,
                InstructionKind::ElementAddr {
                    access: Access::Share,
                    ..
                }
            )
        })
        .unwrap();
    assert!(call("i") < call("v") && call("v") < address);
    assert!(matches!(kinds[address + 1], InstructionKind::Store { .. }));
}

#[test]
fn repetition_lowers_to_a_loop_whose_size_is_independent_of_the_count() {
    let small = lower("fn main() { let a := [7; 2]; }");
    let huge = lower("fn main() { let a := [7; 4000000000]; }");
    let shape = |program: &Program| -> (usize, usize) {
        let function = &program.functions[0];
        (
            function.blocks.len(),
            function.blocks.iter().map(|b| b.instructions.len()).sum(),
        )
    };
    assert_eq!(shape(&small), shape(&huge));
    assert!(shape(&huge).0 > 1, "repetition is a loop");
    let kinds = huge.functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .map(|instruction| &instruction.kind)
        .collect::<Vec<_>>();
    assert!(kinds.iter().any(|kind| matches!(
        kind,
        InstructionKind::ArrayNew {
            init: ArrayInit::Zeroed
        }
    )));
    assert!(!kinds.iter().any(|kind| matches!(
        kind,
        InstructionKind::ArrayNew {
            init: ArrayInit::Elements(_)
        }
    )));
    assert!(memobits_ownership::check_moves(&huge).is_empty());
    assert!(memobits_ownership::check_loans(&huge).is_empty());
}

#[test]
fn repetition_of_zero_and_one_needs_no_loop() {
    let zero = lower("fn f() -> i32 { 1 } fn main() { let a: Array<i32, 0> = [f(); 0]; }");
    assert_eq!(zero.functions[1].blocks.len(), 1);
    assert!(!zero.functions[1]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .any(|instruction| matches!(instruction.kind, InstructionKind::Call { .. })));
    let one = lower("fn f() -> i32 { 1 } fn main() { let a := [f(); 1]; }");
    assert_eq!(one.functions[1].blocks.len(), 1);
}

#[test]
fn repeating_an_owned_binding_is_a_repeated_move() {
    let repeated = lower("fn main() { let x := 5; let a := [x; 3]; }");
    let codes = memobits_ownership::check_moves(&repeated)
        .iter()
        .map(|d| d.code.to_string())
        .collect::<Vec<_>>();
    assert!(codes.contains(&"BE001".into()), "{codes:?}");
    // Zero and one repetitions evaluate the element at most once.
    for source in [
        "fn main() { let x := 5; let a := [x; 1]; }",
        "fn main() { let x := 5; let a: Array<i32, 0> = [x; 0]; }",
        "fn main() { let x := 5; let a := [x + 0; 3]; }",
    ] {
        let program = lower(source);
        assert!(
            memobits_ownership::check_moves(&program).is_empty(),
            "{source}"
        );
    }
}

#[test]
fn use_after_whole_array_move_is_an_ownership_error() {
    for source in [
        "fn main() -> i32 { let a := [1, 2]; let b := a; a[0] + b[0] }",
        "fn main() { var a := [1, 2]; var b := [3, 4]; b = a; b = a; }",
        "fn main() { var a := [1, 2]; let b := a; a[0] = 1; }",
    ] {
        let program = lower(source);
        let codes = memobits_ownership::check_moves(&program)
            .iter()
            .map(|d| d.code.to_string())
            .collect::<Vec<_>>();
        assert!(codes.contains(&"BE001".into()), "{source}: {codes:?}");
    }
    // Reinitializing the moved-from variable makes it usable again.
    let program =
        lower("fn main() -> i32 { var a := [1, 2]; let b := a; a = [3, 4]; a[0] + b[0] }");
    assert!(memobits_ownership::check_moves(&program).is_empty());
}

#[test]
fn element_writes_pass_loan_checks() {
    let program =
        lower("fn main() -> i32 { var a := [1, 2]; a[0] = a[1] + 1; a[1] += a[0]; a[0] + a[1] }");
    assert!(memobits_ownership::check_moves(&program).is_empty());
    assert!(memobits_ownership::check_loans(&program).is_empty());
}

#[test]
fn constant_out_of_bounds_index_keeps_the_type_error() {
    assert!(codes("fn main() -> i32 { let a := [1, 2, 3]; a[3] + 0 }").contains(&"TE008".into()));
    assert!(codes("fn main() -> i32 { let a := [1, 2, 3]; a[-1] + 0 }").contains(&"TE008".into()));
}
