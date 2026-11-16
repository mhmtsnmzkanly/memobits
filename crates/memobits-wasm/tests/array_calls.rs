//! Wasm execution of arrays across internal calls: owned, `borrow` and `share`
//! array parameters, element access through references and recursion.
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

/// Run the last function as `main`; `Err` means the guest trapped.
fn try_run<T: wasmi::WasmResults>(source: &str) -> Result<T, wasmi::Error> {
    let program = lower(source);
    let main = program.functions.len() as u32 - 1;
    let exports = BTreeMap::from([("main".to_string(), memobits_ir::FunctionId(main))]);
    let wasm = memobits_wasm::compile(&program, &exports).unwrap();
    let (mut store, instance) = instantiate(&wasm);
    instance
        .get_typed_func::<(), T>(&store, "main")
        .unwrap()
        .call(&mut store, ())
}

fn run(source: &str) -> i32 {
    try_run::<i32>(source).unwrap_or_else(|error| panic!("{source}: {error}"))
}

const SUM: &str = "fn sum(a: borrow Array<i32, 3>) -> i32 { \
    var i := 0; var total := 0; \
    loop { if i >= 3 { break; } total += a[i]; i += 1; } total } ";
const FILL: &str = "fn fill(a: share Array<i32, 4>, v: i32) { \
    var i := 0; loop { if i >= 4 { break; } a[i] = v + i; i += 1; } } ";

#[test]
fn borrowed_arrays_are_summed_in_a_loop_and_reused() {
    assert_eq!(
        run(&format!(
            "{SUM} fn main() -> i32 {{ let a := [1, 2, 3]; sum(a.borrow()) * 10 + sum(a.borrow()) }}"
        )),
        66
    );
    // Passing a borrow on to another function reads the same storage.
    assert_eq!(
        run(&format!(
            "{SUM} fn twice(a: borrow Array<i32, 3>) -> i32 {{ sum(a) + sum(a) }} \
             fn main() -> i32 {{ let a := [4, 5, 6]; twice(a.borrow()) }}"
        )),
        30
    );
    // A local reference binding.
    assert_eq!(
        run("fn main() -> i32 { let a := [4, 5, 6]; let r := a.borrow(); r[0] + r[2] }"),
        10
    );
}

#[test]
fn share_parameters_mutate_the_callers_array() {
    assert_eq!(
        run(&format!(
            "{FILL} fn main() -> i32 {{ var a := [0; 4]; fill(a.share(), 10); a[0] + a[3] }}"
        )),
        23
    );
    // Compound writes, a dynamic index and a whole-array store through a share.
    assert_eq!(
        run(
            "fn f(a: share Array<i32, 3>, i: i32) { a[i + 0] += 5; a[0] *= 2; } \
             fn main() -> i32 { var a := [1, 2, 3]; f(a.share(), 2); a[0] * 100 + a[2] }"
        ),
        208
    );
    assert_eq!(
        run("fn put(a: share Array<i32, 2>) { a = [7, 8]; } \
             fn main() -> i32 { var a := [1, 2]; put(a.share()); a[0] * 10 + a[1] }"),
        78
    );
    // Forwarding a share parameter to another share parameter.
    assert_eq!(
        run(&format!(
            "{FILL} fn outer(a: share Array<i32, 4>) {{ fill(a, 1); a[0] = 100; }} \
             fn main() -> i32 {{ var a := [0; 4]; outer(a.share()); a[0] + a[3] }}"
        )),
        104
    );
    // A local share binding.
    assert_eq!(
        run("fn main() -> i32 { var a := [1, 2]; var r := a.share(); r[0] = 5; r[1] += 1; a[0] + a[1] }"),
        8
    );
}

#[test]
fn owned_array_parameters_are_copied_into_the_callee() {
    assert_eq!(
        run("fn f(a: Array<i32, 3>) -> i32 { a[0] + a[2] } \
             fn main() -> i32 { let a := [1, 2, 3]; f(a) }"),
        4
    );
    // A literal and a repetition are accepted directly as owned arguments.
    assert_eq!(
        run("fn f(a: Array<i32, 3>) -> i32 { a[0] + a[2] } \
             fn main() -> i32 { f([5, 6, 7]) + f([1; 3]) }"),
        14
    );
    // A `var` parameter mutates the callee's own copy.
    assert_eq!(
        run(
            "fn f(var a: Array<i32, 2>) -> i32 { a[0] = 40; a[1] += 2; a[0] + a[1] } \
             fn main() -> i32 { var a := [1, 2]; f(a) }"
        ),
        44
    );
    // A moved array can be rebuilt and passed again.
    assert_eq!(
        run("fn f(a: Array<i32, 2>) -> i32 { a[0] + a[1] } \
             fn main() -> i32 { var a := [1, 2]; let x := f(a); a = [10, 20]; x + f(a) }"),
        33
    );
    // Passing an owned parameter on, and a borrow of an owned parameter.
    assert_eq!(
        run(&format!(
            "{SUM} fn g(a: Array<i32, 3>) -> i32 {{ sum(a.borrow()) }} \
             fn f(a: Array<i32, 3>) -> i32 {{ g(a) + 1 }} \
             fn main() -> i32 {{ f([1, 2, 3]) }}"
        )),
        7
    );
    // Zero-length arrays cross calls.
    assert_eq!(
        run("fn f(a: Array<i32, 0>, b: borrow Array<i32, 0>) -> i32 { 3 } \
             fn main() -> i32 { let a: Array<i32, 0> = []; let b: Array<i32, 0> = []; f(a, b.borrow()) }"),
        3
    );
}

#[test]
fn every_element_type_crosses_calls() {
    for (ty, elements, check) in [
        ("i8", "[-1, -128, 127]", "a[1] == -128"),
        ("u8", "[1, 255, 3]", "a[1] == 255"),
        ("i16", "[-1, -32768, 5]", "a[1] == -32768"),
        ("u16", "[1, 65535, 3]", "a[1] == 65535"),
        ("i32", "[-1, -2147483648, 3]", "a[1] == -2147483648"),
        ("u32", "[1, 4294967295, 3]", "a[1] == 4294967295"),
        (
            "i64",
            "[-1, -9223372036854775808, 3]",
            "a[1] == -9223372036854775808",
        ),
        (
            "u64",
            "[1, 18446744073709551615, 3]",
            "a[1] == 18446744073709551615",
        ),
        ("f32", "[1.5, 2.5, 3.5]", "a[1] == 2.5"),
        ("f64", "[1.5, 2.5, 3.5]", "a[1] == 2.5"),
        ("Bool", "[true, false, true]", "!(a[1]) && a[0]"),
    ] {
        let source = format!(
            "fn by_borrow(a: borrow Array<{ty}, 3>) -> Bool {{ {check} }} \
             fn by_value(a: Array<{ty}, 3>) -> Bool {{ {check} }} \
             fn main() -> i32 {{ let a: Array<{ty}, 3> = {elements}; \
                 let x := by_borrow(a.borrow()); let y := by_value(a); \
                 if x && y {{ 1 }} else {{ 0 }} }}"
        );
        assert_eq!(run(&source), 1, "{ty}");
    }
    // Writes through a share keep the element width.
    assert_eq!(
        run("fn f(a: share Array<u8, 2>) { a[0] = 200; a[1] = 7; } \
             fn main() -> i32 { var a: Array<u8, 2> = [1; 2]; f(a.share()); if a[0] == 200 && a[1] == 7 { 1 } else { 0 } }"),
        1
    );
}

#[test]
fn out_of_range_dynamic_indices_trap_inside_callees() {
    let read = |n: &str| {
        try_run::<i32>(&format!(
            "fn get(a: borrow Array<i32, 3>, n: i32) -> i32 {{ a[n] + 0 }} \
             fn main() -> i32 {{ let a := [1, 2, 3]; let n := {n}; get(a.borrow(), n + 0) }}"
        ))
    };
    assert_eq!(read("2").unwrap(), 3);
    assert!(read("3").is_err());
    assert!(read("-1").is_err());
    let write = |n: &str| {
        try_run::<i32>(&format!(
            "fn put(a: share Array<i32, 3>, n: i32) {{ a[n] = 9; }} \
             fn main() -> i32 {{ var a := [1, 2, 3]; let n := {n}; put(a.share(), n + 0); a[2] + 0 }}"
        ))
    };
    assert_eq!(write("2").unwrap(), 9);
    assert!(write("3").is_err());
    // The same for an owned parameter and for 64-bit indices.
    assert!(try_run::<i32>(
        "fn get(a: Array<i32, 3>, n: i64) -> i32 { a[n] + 0 } \
         fn main() -> i32 { let n: i64 = 4294967296; get([1, 2, 3], n + 0) }"
    )
    .is_err());
}

#[test]
fn recursion_keeps_each_activation_frame_separate() {
    // Every level owns a local array and borrows the root array.
    assert_eq!(
        run("fn rec(a: borrow Array<i32, 3>, n: i32) -> i32 { \
                 let m := n + 0; var local := [m + 0, m * 2, m * 3]; \
                 if m + 0 == 0 { a[0] + 0 } else { let r := rec(a, m - 1); r + local[2] } } \
             fn main() -> i32 { let a := [100, 2, 3]; rec(a.borrow(), 3) }"),
        118
    );
    // Owned array parameters are copied per activation.
    assert_eq!(
        run("fn rec(var a: Array<i32, 2>, n: i32) -> i32 { \
                 let m := n + 0; a[0] = m + 0; \
                 if m + 0 == 0 { 0 } else { let r := rec([m + 0, m + 0], m - 1); r + a[0] } } \
             fn main() -> i32 { rec([9, 9], 4) }"),
        10
    );
    // A share parameter is mutated by every activation.
    assert_eq!(
        run(
            "fn rec(a: share Array<i32, 2>, n: i32) { a[0] += 1; if n > 0 { rec(a, n - 1); } } \
             fn main() -> i32 { var a := [0, 0]; rec(a.share(), 4); a[0] + 0 }"
        ),
        5
    );
}

#[test]
fn array_arguments_report_backend_gates_with_clear_messages() {
    let rejected = |source: &str, expected: &str| {
        let program = lower(source);
        let main = program.functions.len() as u32 - 1;
        let exports = BTreeMap::from([("main".to_string(), memobits_ir::FunctionId(main))]);
        let errors = memobits_wasm::compile(&program, &exports).unwrap_err();
        assert!(
            errors.iter().any(|d| d.message.contains(expected)),
            "{source}: {errors:?}"
        );
    };
    for source in [
        "fn main(a: Array<i32, 2>) -> i32 { 0 }",
        "fn main(a: borrow Array<i32, 2>) -> i32 { 0 }",
        "fn main(a: share Array<i32, 2>) -> i32 { 0 }",
    ] {
        rejected(source, "cannot take arrays or array references");
    }
    // A callee frame holding a too-large array parameter is a frame diagnostic.
    rejected(
        "fn f(a: Array<i64, 5000>) {} fn main() -> i32 { 0 }",
        "32 KiB",
    );
}
