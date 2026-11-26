//! Wasm execution of array-valued results, `if`/block array values and nested
//! arrays: struct-return storage, joins, rows, bounds traps and evaluation order.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_ir::Program;
use memobits_syntax::parse;
use std::collections::BTreeMap;
use wasmi::{Engine, Linker, Module, Store};

fn lower(source: &str) -> Program {
    let parsed = parse(SourceId(0), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"))
}

fn instantiate(bytes: &[u8]) -> (Store<()>, wasmi::Instance) {
    wasmparser::validate(bytes).unwrap();
    let engine = Engine::default();
    let module = Module::new(&engine, bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Linker::new(&engine)
        .instantiate_and_start(&mut store, &module)
        .unwrap();
    (store, instance)
}

/// Run the last function as `main`.
fn try_run(source: &str) -> Result<i32, wasmi::Error> {
    let program = lower(source);
    let main = program.functions.len() as u32 - 1;
    let exports = BTreeMap::from([("main".to_string(), memobits_ir::FunctionId(main))]);
    let wasm = memobits_wasm::compile(&program, &exports).unwrap();
    let (mut store, instance) = instantiate(&wasm);
    instance
        .get_typed_func::<(), i32>(&store, "main")
        .unwrap()
        .call(&mut store, ())
}

fn run(source: &str) -> i32 {
    try_run(source).unwrap_or_else(|error| panic!("{source}: {error}"))
}

fn traps(source: &str) {
    assert!(try_run(source).is_err(), "{source} should trap");
}

const SUM3: &str = "fn sum3(a: borrow array<i32, 3>) -> i32 { \
    var i := 0; var t := 0; loop { if i >= 3 { break; } t += a[i]; i += 1; } t } ";

#[test]
fn array_results_come_from_literals_and_tails() {
    assert_eq!(
        run("fn make() -> array<i32, 3> { [1, 2, 3] } \
             fn main() -> i32 { let a := make(); a[0] * 100 + a[1] * 10 + a[2] }"),
        123
    );
    assert_eq!(
        run("fn make() -> array<i32, 3> { return [4, 5, 6]; } \
             fn main() -> i32 { let a := make(); a[2] + 0 }"),
        6
    );
}

#[test]
fn array_results_move_owned_parameters_and_locals() {
    assert_eq!(
        run("fn pass(a: array<i32, 2>) -> array<i32, 2> { a } \
             fn main() -> i32 { let b := pass([7, 8]); b[0] + b[1] }"),
        15
    );
    assert_eq!(
        run(
            "fn make() -> array<i32, 2> { var a := [1, 2]; a[0] = 9; return a; } \
             fn main() -> i32 { let b := make(); b[0] * 10 + b[1] }"
        ),
        92
    );
    // A var parameter mutated in the callee and returned.
    assert_eq!(
        run(
            "fn bump(var a: array<i32, 2>) -> array<i32, 2> { a[1] += 5; a } \
             fn main() -> i32 { let x := [1, 1]; let y := bump(x); y[1] + 0 }"
        ),
        6
    );
}

#[test]
fn array_results_feed_assignment_arguments_and_borrows() {
    assert_eq!(
        run("fn make() -> array<i32, 3> { [1, 2, 3] } \
             fn main() -> i32 { var a := [0, 0, 0]; a = make(); a[1] + a[2] }"),
        5
    );
    assert_eq!(
        run(&format!(
            "{SUM3} fn make() -> array<i32, 3> {{ [4, 5, 6] }} \
             fn sum_owned(a: array<i32, 3>) -> i32 {{ a[0] + a[1] + a[2] }} \
             fn main() -> i32 {{ sum_owned(make()) * 100 + sum_owned(make()) }}"
        )),
        1515
    );
    assert_eq!(
        run(&format!(
            "{SUM3} fn make() -> array<i32, 3> {{ [3; 3] }} \
             fn main() -> i32 {{ let a := make(); sum3(a.borrow()) }}"
        )),
        9
    );
    // A call result consumed by another call result.
    assert_eq!(
        run("fn make() -> array<i32, 2> { [1, 2] } \
             fn twice(a: array<i32, 2>) -> array<i32, 2> { [a[0] * 2, a[1] * 2] } \
             fn main() -> i32 { let a := twice(twice(make())); a[0] + a[1] }"),
        12
    );
}

#[test]
fn recursion_returning_arrays_keeps_frames_separate() {
    assert_eq!(
        run("fn build(n: i32) -> array<i32, 2> { \
                if n <= 0 { return [0, 1]; } \
                let inner := build(n - 1); \
                [inner[1] + 0, inner[0] + inner[1]] } \
             fn main() -> i32 { let a := build(10); a[0] * 1000 + a[1] }"),
        55089
    );
}

#[test]
fn array_valued_if_and_blocks_choose_dynamically() {
    let program =
        "fn pick(c: bool) -> i32 { let a := if c { [1, 2] } else { [3, 4] }; a[0] * 10 + a[1] } ";
    assert_eq!(
        run(&format!("{program} fn main() -> i32 {{ pick(true) }}")),
        12
    );
    assert_eq!(
        run(&format!("{program} fn main() -> i32 {{ pick(false) }}")),
        34
    );
    assert_eq!(
        run("fn main() -> i32 { let a := { let x := 5; [x + 0, x + 1] }; a[0] + a[1] }"),
        11
    );
    assert_eq!(
        run("fn pick(n: i32) -> array<i32, 2> { if n == 0 { [1, 1] } else { if n == 1 { [2, 2] } else { [3, 3] } } } \
             fn main() -> i32 { let a := pick(2); let b := pick(1); let c := pick(0); a[0] * 100 + b[0] * 10 + c[0] }"),
        321
    );
    // Moving named arrays through the branches.
    assert_eq!(
        run("fn main() -> i32 { let x := [1, 2]; let y := [5, 6]; \
             let z := if true { x } else { y }; z[0] + z[1] }"),
        3
    );
}

#[test]
fn nested_arrays_read_write_and_trap() {
    assert_eq!(
        run("fn main() -> i32 { let m := [[1, 2], [3, 4], [5, 6]]; m[0][0] + m[1][1] * 10 + m[2][0] * 100 }"),
        541
    );
    assert_eq!(
        run(
            "fn main() -> i32 { var m := [[0; 2]; 3]; m[1][1] = 7; m[2][0] += 3; m[2][0] *= 2; \
             m[1][1] + m[2][0] + m[0][0] }"
        ),
        13
    );
    for source in [
        "fn main(i: i32) -> i32 { let m := [[1, 2], [3, 4]]; m[i][0] + 0 }",
        "fn main(j: i32) -> i32 { let m := [[1, 2], [3, 4]]; m[0][j] + 0 }",
    ] {
        let program = lower(source);
        let exports = BTreeMap::from([("main".to_string(), memobits_ir::FunctionId(0))]);
        let wasm = memobits_wasm::compile(&program, &exports).unwrap();
        let (mut store, instance) = instantiate(&wasm);
        let main = instance.get_typed_func::<i32, i32>(&store, "main").unwrap();
        assert_eq!(
            main.call(&mut store, 1).unwrap(),
            if source.contains("m[i]") { 3 } else { 2 }
        );
        assert!(main.call(&mut store, 2).is_err());
        assert!(main.call(&mut store, -1).is_err());
    }
}

#[test]
fn matrix_fill_trace_and_sum() {
    assert_eq!(
        run("fn main() -> i32 { var m := [[0; 3]; 3]; \
             var i := 0; \
             loop { if i >= 3 { break; } \
               var j := 0; \
               loop { if j >= 3 { break; } m[i][j] = i * 3 + j; j += 1; } \
               i += 1; } \
             var trace := 0; var total := 0; var k := 0; \
             loop { if k >= 3 { break; } trace += m[k][k]; \
               var l := 0; loop { if l >= 3 { break; } total += m[k][l]; l += 1; } \
               k += 1; } \
             trace * 100 + total }"),
        12 * 100 + 36
    );
}

#[test]
fn nested_repetition_evaluates_each_element_separately() {
    // The element expression is an array literal whose own element calls next().
    assert_eq!(
        run("fn next(c: share i32) -> i32 { c += 1; c + 0 } \
             fn main() -> i32 { var c := 0; var m := [[next(c.share()), next(c.share())]; 3]; \
             m[0][0] * 100000 + m[0][1] * 10000 + m[1][0] * 1000 + m[1][1] * 100 + m[2][0] * 10 + m[2][1] }"),
        123456
    );
    assert_eq!(
        run("fn next(c: share i32) -> i32 { c += 1; c + 0 } \
             fn main() -> i32 { var c := 0; let m := [[next(c.share()); 2]; 0]; c }"),
        0
    );
}

#[test]
fn rows_are_replaced_and_passed_by_reference() {
    assert_eq!(
        run("fn main() -> i32 { var m := [[1, 2], [3, 4]]; m[1] = [10, 20]; m[1][0] + m[1][1] + m[0][0] }"),
        31
    );
    // Self-referential row assignment builds the new row first.
    assert_eq!(
        run("fn main() -> i32 { var m := [[1, 2], [3, 4]]; m[0] = [m[0][1] + 0, m[0][0] + 0]; m[0][0] * 10 + m[0][1] }"),
        21
    );
    assert_eq!(
        run("fn sum2(a: borrow array<i32, 2>) -> i32 { a[0] + a[1] } \
             fn main() -> i32 { let m := [[1, 2], [3, 4]]; sum2(m[0].borrow()) * 10 + sum2(m[1].borrow()) }"),
        37
    );
    assert_eq!(
        run("fn zero(a: share array<i32, 2>) { a[0] = 0; a[1] = 0; } \
             fn main() -> i32 { var m := [[1, 2], [3, 4]]; zero(m[1].share()); m[0][0] + m[0][1] + m[1][0] + m[1][1] }"),
        3
    );
}

#[test]
fn nested_arrays_cross_calls_as_parameters_and_results() {
    assert_eq!(
        run(
            "fn trace(m: borrow array<array<i32, 2>, 2>) -> i32 { m[0][0] + m[1][1] } \
             fn fill(m: share array<array<i32, 2>, 2>, v: i32) { m[0][1] = v + 0; m[1][0] = v; } \
             fn eye() -> array<array<i32, 2>, 2> { [[1, 0], [0, 1]] } \
             fn take(m: array<array<i32, 2>, 2>) -> i32 { m[0][0] + m[1][1] + m[0][1] } \
             fn main() -> i32 { var m := eye(); fill(m.share(), 5); \
               trace(m.borrow()) * 100 + m[0][1] * 10 + take(m) }"
        ),
        2 * 100 + 50 + 7
    );
}

#[test]
fn evaluation_order_of_nested_assignment() {
    // f, g, then h: each effect appends a digit.
    assert_eq!(
        run(
            "fn digit(log: share i32, d: i32) -> i32 { log = log * 10 + d; 0 } \
             fn main() -> i32 { var log := 0; var m := [[0; 2]; 2]; \
             m[digit(log.share(), 1)][digit(log.share(), 2)] = digit(log.share(), 3); log }"
        ),
        123
    );
}

#[test]
fn constant_nested_index_errors_and_trap_after_rhs() {
    // The write trap fires after the right-hand side's effects (D2).
    traps("fn main() -> i32 { var m := [[0; 2]; 2]; var i := 2; m[i][0] = 1; 0 }");
}

fn compile_errors(source: &str, entry: &str) -> Vec<String> {
    let program = lower(source);
    let id = program
        .functions
        .iter()
        .position(|function| function.path.name == entry)
        .unwrap() as u32;
    let exports = BTreeMap::from([(entry.to_string(), memobits_ir::FunctionId(id))]);
    memobits_wasm::compile(&program, &exports)
        .unwrap_err()
        .into_iter()
        .map(|d| format!("{} {}", d.code, d.message))
        .collect()
}

#[test]
fn arrays_stay_out_of_exported_signatures_and_frames_are_capped() {
    for (source, entry, expected) in [
        ("fn main() -> array<i32, 2> { [1, 2] }", "main", "cannot return arrays"),
        (
            "fn main() -> array<array<i32, 2>, 2> { [[1, 2], [3, 4]] }",
            "main",
            "cannot return arrays",
        ),
        (
            "fn main(m: borrow array<array<i32, 2>, 2>) -> i32 { 0 }",
            "main",
            "cannot take arrays or array references",
        ),
        (
            "fn main(m: array<array<i32, 2>, 2>) -> i32 { 0 }",
            "main",
            "cannot take arrays or array references",
        ),
        // A caller-allocated result cell counts against the frame.
        (
            "fn big() -> array<i64, 140000> { [0; 140000] } fn main() -> i32 { let a := big(); 0 }",
            "main",
            "configured stack size",
        ),
        (
            "fn main() -> i32 { let m: array<array<i32, 4000>, 4000> = [[0; 4000]; 4000]; 0 }",
            "main",
            "configured stack size",
        ),
        (
            "fn main() -> i32 { let m: array<array<i64, 4000000000>, 4000000000> = [[0; 4000000000]; 4000000000]; 0 }",
            "main",
            "configured stack size",
        ),
    ] {
        let errors = compile_errors(source, entry);
        assert!(
            errors.iter().any(|message| message.contains(expected)),
            "{source}: {errors:?}"
        );
    }
}

#[test]
fn the_manifest_export_style_also_rejects_array_results() {
    // An internal array-returning function is fine; exporting it is not.
    let source =
        "fn make() -> array<i32, 2> { [1, 2] } fn main() -> i32 { let a := make(); a[0] + 0 }";
    let program = lower(source);
    let exports = BTreeMap::from([
        ("main".to_string(), memobits_ir::FunctionId(1)),
        ("make".to_string(), memobits_ir::FunctionId(0)),
    ]);
    let errors = memobits_wasm::compile(&program, &exports).unwrap_err();
    assert!(errors
        .iter()
        .any(|d| d.message.contains("cannot return arrays")));
}

#[test]
fn array_results_work_for_every_element_type_and_nesting() {
    assert_eq!(
        run("fn make() -> array<u8, 3> { [200, 3, 4] } \
             fn main() -> i32 { let a := make(); if a[0] == 200 { 1 } else { 0 } }"),
        1
    );
    assert_eq!(
        run("fn make() -> array<f64, 2> { [1.5, 2.5] } \
             fn main() -> i32 { let a := make(); if a[0] + a[1] == 4.0 { 7 } else { 0 } }"),
        7
    );
    assert_eq!(
        run("fn make() -> array<i64, 2> { [1, 2] } \
             fn main() -> i32 { let a := make(); if a[1] == 2 { 9 } else { 0 } }"),
        9
    );
    assert_eq!(
        run("fn make() -> array<array<u8, 2>, 2> { [[1, 2], [3, 4]] } \
             fn flat(m: borrow array<array<u8, 2>, 2>) -> i32 { \
               if m[1][1] == 4 { 1 } else { 0 } } \
             fn main() -> i32 { let m := make(); flat(m.borrow()) }"),
        1
    );
    // Rows of three levels.
    assert_eq!(
        run(
            "fn main() -> i32 { var c := [[[0; 2]; 2]; 2]; c[1][0][1] = 5; c[0][1][0] += 2; \
             c[1][0][1] + c[0][1][0] }"
        ),
        7
    );
}
