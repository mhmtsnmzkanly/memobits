//! Wasm execution of whole-value destructuring (package A4).
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_syntax::parse;
use std::collections::BTreeMap;
use wasmi::{Engine, Linker, Module, Store};

fn run_as<R: wasmi::WasmResults>(source: &str) -> R {
    let parsed = parse(SourceId(0), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let program = lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"));
    assert!(
        memobits_ownership::check_ownership(&program).is_empty(),
        "{source}"
    );
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
    instance
        .get_typed_func::<(), R>(&store, "main")
        .unwrap()
        .call(&mut store, ())
        .unwrap_or_else(|error| panic!("{source}: {error}"))
}

const TYPES: &str = "type M { a: u8, b: i64, c: bool, d: f32, e: i16 } \
    type P { x: i32, y: i32 } \
    type Line { a: P, b: P, n: i32 } \
    type Grid { cells: array<i32, 3>, k: i32 } \
    type Outer { g: Grid, tag: u8 } ";

#[test]
fn mixed_width_fields_destructure_exactly() {
    let build = "let M { e, a, d, c, b } := M { e: -7, a: 200, d: 1.5, c: true, b: 5000000000 };";
    assert_eq!(
        run_as::<i32>(&format!("{TYPES} fn main() -> i16 {{ {build} e.copy() }}")),
        -7
    );
    assert_eq!(
        run_as::<i32>(&format!("{TYPES} fn main() -> u8 {{ {build} a.copy() }}")),
        200
    );
    assert_eq!(
        run_as::<i64>(&format!("{TYPES} fn main() -> i64 {{ {build} b.copy() }}")),
        5_000_000_000
    );
    assert_eq!(
        run_as::<i32>(&format!(
            "{TYPES} fn main() -> i32 {{ {build} if c {{ 1 }} else {{ 0 }} }}"
        )),
        1
    );
    assert_eq!(
        run_as::<f32>(&format!("{TYPES} fn main() -> f32 {{ {build} d.copy() }}")),
        1.5
    );
}

#[test]
fn aggregate_fields_move_out_with_their_contents() {
    assert_eq!(
        run_as::<i32>(&format!(
            "{TYPES} fn main() -> i32 {{ \
               let l := Line {{ a: P {{ x: 1, y: 2 }}, b: P {{ x: 3, y: 4 }}, n: 5 }}; \
               let Line {{ b: first, a: second, n }} := l; \
               first.x * 1000 + first.y * 100 + second.x * 10 + second.y + n * 10000 }}"
        )),
        53_412
    );
    // A nested array field and a doubly nested destructuring in two steps.
    assert_eq!(
        run_as::<i32>(&format!(
            "{TYPES} fn main() -> i32 {{ \
               let Outer {{ g, tag }} := Outer {{ g: Grid {{ cells: [7, 8, 9], k: 2 }}, tag: 4 }}; \
               let Grid {{ cells, k }} := g; \
               cells[0] + cells[1] * 10 + cells[2] * 100 + k * 1000 + if tag == 4 {{ 40000 }} else {{ 0 }} }}"
        )),
        42_987
    );
}

#[test]
fn var_destructuring_mutates_only_the_bindings() {
    assert_eq!(
        run_as::<i32>(&format!(
            "{TYPES} fn main() -> i32 {{ \
               let p := P {{ x: 1, y: 2 }}; \
               var P {{ x, y }} := P {{ x: p.x.copy(), y: p.y.copy() }}; \
               x += 10; y = y * 5; \
               var Line {{ a, b, n }} := Line {{ a: P {{ x: 1, y: 1 }}, b: P {{ x: 2, y: 2 }}, n: 0 }}; \
               a.x = 40; b = P {{ x: 5, y: 6 }}; \
               x + y + a.x + b.x + b.y + p.x }}"
        )),
        11 + 10 + 40 + 5 + 6 + 1
    );
}

#[test]
fn destructuring_works_on_results_parameters_and_in_loops() {
    assert_eq!(
        run_as::<i32>(&format!(
            "{TYPES} \
             fn mk(n: i32) -> Line {{ Line {{ a: P {{ x: n, y: 1 }}, b: P {{ x: n * 2, y: 2 }}, n: n * 3 }} }} \
             fn sum(l: Line) -> i32 {{ let Line {{ a, b, n }} := l; a.x + b.x + n }} \
             fn main() -> i32 {{ \
               var total := 0; var i := 1; \
               loop {{ \
                 let Line {{ a, b, n }} := mk(i); \
                 total += a.x + b.y + n; \
                 i += 1; \
                 if i > 3 {{ break; }} \
               }} \
               total * 1000 + sum(mk(2)) }}"
        )),
        // i=1: 1+2+3=6, i=2: 2+2+6=10, i=3: 3+2+9=14 -> 30; sum(mk(2)) = 2+4+6
        30_012
    );
}
