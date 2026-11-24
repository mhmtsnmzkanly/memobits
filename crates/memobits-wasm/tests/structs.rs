//! Wasm execution of user-defined structs: frame-cell layout, in-place
//! construction, field reads and the configured stack limit.
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

fn instantiate(source: &str) -> (Store<()>, wasmi::Instance) {
    let program = lower(source);
    let main = program.functions.len() as u32 - 1;
    let exports = BTreeMap::from([("main".to_string(), memobits_ir::FunctionId(main))]);
    let wasm = memobits_wasm::compile(&program, &exports).unwrap();
    wasmparser::validate(&wasm).unwrap();
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm[..]).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Linker::new(&engine)
        .instantiate_and_start(&mut store, &module)
        .unwrap();
    (store, instance)
}

fn run_as<R: wasmi::WasmResults>(source: &str) -> Result<R, wasmi::Error> {
    let (mut store, instance) = instantiate(source);
    instance
        .get_typed_func::<(), R>(&store, "main")
        .unwrap()
        .call(&mut store, ())
}

fn run(source: &str) -> i32 {
    run_as::<i32>(source).unwrap_or_else(|error| panic!("{source}: {error}"))
}

#[test]
fn two_field_struct_multiplies_its_fields() {
    assert_eq!(
        run("type P { x: i32, y: i32 } \
             fn main() -> i32 { let p := P { x: 3, y: 4 }; p.x * p.y }"),
        12
    );
}

const MIXED: &str = "type M { a: u8, b: i64, c: bool, d: f32, e: i16 } ";

#[test]
fn mixed_width_fields_read_back_exactly() {
    let build = "let m := M { e: -7, a: 200, d: 1.5, c: true, b: 5000000000 };";
    assert_eq!(
        run_as::<i32>(&format!("{MIXED} fn main() -> u8 {{ {build} m.a.copy() }}")).unwrap(),
        200
    );
    assert_eq!(
        run_as::<i64>(&format!(
            "{MIXED} fn main() -> i64 {{ {build} m.b.copy() }}"
        ))
        .unwrap(),
        5_000_000_000
    );
    assert_eq!(
        run_as::<i32>(&format!(
            "{MIXED} fn main() -> bool {{ {build} m.c.copy() }}"
        ))
        .unwrap(),
        1
    );
    assert_eq!(
        run_as::<f32>(&format!(
            "{MIXED} fn main() -> f32 {{ {build} m.d.copy() }}"
        ))
        .unwrap(),
        1.5
    );
    assert_eq!(
        run_as::<i32>(&format!(
            "{MIXED} fn main() -> i16 {{ {build} m.e.copy() }}"
        ))
        .unwrap(),
        -7
    );
    // Neighbouring fields do not disturb each other when all are used together.
    assert_eq!(
        run_as::<i64>(&format!(
            "{MIXED} fn main() -> i64 {{ {build} if m.c {{ m.b + 1 }} else {{ 0 }} }}"
        ))
        .unwrap(),
        5_000_000_001
    );
}

#[test]
fn extreme_values_survive_layout_padding() {
    let program = "type W { a: u8, b: u64, c: i8, d: f64, e: u16, f: i32, g: bool } ";
    let build = "let w := W { g: false, f: -2147483648, e: 65535, d: -0.25, c: -128, b: 18446744073709551615, a: 255 };";
    for (field, ty, expected) in [
        ("a", "u8", 255i64),
        ("c", "i8", -128),
        ("e", "u16", 65535),
        ("f", "i32", -2147483648),
        ("g", "bool", 0),
    ] {
        let source = format!("{program} fn main() -> {ty} {{ {build} w.{field}.copy() }}");
        assert_eq!(
            i64::from(run_as::<i32>(&source).unwrap()),
            expected,
            "{field}"
        );
    }
    let source = format!("{program} fn main() -> u64 {{ {build} w.b.copy() }}");
    assert_eq!(run_as::<i64>(&source).unwrap() as u64, u64::MAX);
    let source = format!("{program} fn main() -> f64 {{ {build} w.d.copy() }}");
    assert_eq!(run_as::<f64>(&source).unwrap(), -0.25);
}

#[test]
fn field_initialisers_run_in_source_order() {
    // `next` bumps a shared counter; the observed values show source order
    // (c, a, b), not declaration order (a, b, c).
    assert_eq!(
        run("type P { a: i32, b: i32, c: i32 } \
             fn next(c: share i32) -> i32 { c += 1; c.copy() } \
             fn main() -> i32 { \
                 var n := 0; \
                 let p := P { c: next(n.share()), a: next(n.share()), b: next(n.share()) }; \
                 p.a * 100 + p.b * 10 + p.c }"),
        231
    );
}

#[test]
fn structs_work_in_branches_loops_and_with_arrays() {
    assert_eq!(
        run("type P { x: i32, y: i32 } \
             fn main() -> i32 { \
                 var total := 0; var i := 0; \
                 loop { \
                     if i >= 4 { break; } \
                     let p := P { x: i.copy(), y: i * i }; \
                     total += p.x + p.y; \
                     i += 1; \
                 } \
                 total }"),
        // sum of i + i*i for i in 0..4 = 6 + 14
        20
    );
    assert_eq!(
        run("type P { x: i32, flag: bool } \
             fn main() -> i32 { \
                 let p := P { x: 7, flag: true }; let q := P { x: 9, flag: false }; \
                 let a := [10, 20, 30]; \
                 if q.flag { 0 } else if p.flag && p.x > 5 { a[1] + q.x } else { 1 } }"),
        29
    );
    assert_eq!(
        run("type P { x: i32 } type Q { x: i32, y: i32 } \
             fn main() -> i32 { let p := P { x: 1 }; let q := Q { y: 20, x: 300 }; p.x + q.x + q.y }"),
        321
    );
}

#[test]
fn structs_pass_through_helper_calls_by_field_copies() {
    assert_eq!(
        run("type P { x: i32, y: i32 } \
             fn add(a: i32, b: i32) -> i32 { a + b } \
             fn main() -> i32 { let p := P { x: 5, y: 6 }; add(p.x.copy(), p.y.copy()) }"),
        11
    );
}

#[test]
fn field_arithmetic_is_checked_and_indices_trap_out_of_range() {
    assert!(run_as::<i32>(
        "type P { x: i32 } fn main() -> i32 { let p := P { x: 2147483647 }; p.x + 1 }"
    )
    .is_err());
    assert!(run_as::<i32>(
        "type P { i: i32 } fn main() -> i32 { let p := P { i: 5 }; let a := [1, 2]; a[p.i] + 0 }"
    )
    .is_err());
}

#[test]
fn zero_field_structs_are_valid_values() {
    assert_eq!(
        run("type U {} fn main() -> i32 { let u := U {}; let v := U {}; 7 }"),
        7
    );
}

#[test]
fn a_struct_larger_than_the_frame_cap_is_a_backend_diagnostic() {
    let fields = |count: usize| {
        (0..count)
            .map(|i| format!("f{i}: i64"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let inits = |count: usize| {
        (0..count)
            .map(|i| format!("f{i}: {i}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let source = |count: usize| {
        format!(
            "type Big {{ {} }} fn main() -> i32 {{ let b := Big {{ {} }}; 1 }}",
            fields(count),
            inits(count)
        )
    };
    // 1000 * 8 bytes = 8 KB fits.
    assert_eq!(run(&source(1000)), 1);
    // 4200 * 8 bytes = 33.6 KB exceeds a 32 KiB configured stack.
    let program = lower(&source(4200));
    let exports = BTreeMap::from([("main".to_string(), memobits_ir::FunctionId(0))]);
    let options = memobits_wasm::CompileOptions {
        stack_size: 32 * 1024,
    };
    let errors = memobits_wasm::compile_with(&program, &exports, &options).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|d| d.message.contains("struct frame layout of")
                && d.message.contains("configured stack size")),
        "{errors:?}"
    );
}
