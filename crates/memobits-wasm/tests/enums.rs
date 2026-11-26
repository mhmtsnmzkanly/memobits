//! Wasm execution of enum values (package B1): construction into frame cells,
//! moves, parameters, results, joins, fields, arrays, nesting, and the limits
//! around frames and exports. Enums are not inspectable yet (no `match`), so the
//! programs return primitives computed next to the enum traffic; the tag and
//! payload bytes are checked by the layout tests in the crate itself.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_ir::{FunctionId, Program};
use memobits_syntax::parse;
use memobits_wasm::{compile, compile_with, CompileOptions};
use std::collections::BTreeMap;
use wasmi::{Engine, Linker, Module, Store};

fn lower(source: &str) -> Program {
    let parsed = parse(SourceId(0), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"))
}

fn exports_of(program: &Program, names: &[&str]) -> BTreeMap<String, FunctionId> {
    names
        .iter()
        .map(|name| {
            let index = program
                .functions
                .iter()
                .position(|f| f.path.name == *name)
                .unwrap();
            (name.to_string(), FunctionId(index as u32))
        })
        .collect()
}

fn run(source: &str) -> i32 {
    let program = lower(source);
    let exports = exports_of(&program, &["main"]);
    let wasm = compile(&program, &exports).unwrap_or_else(|e| panic!("{source}: {e:?}"));
    wasmparser::validate(&wasm).unwrap();
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm[..]).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Linker::new(&engine)
        .instantiate_and_start(&mut store, &module)
        .unwrap();
    instance
        .get_typed_func::<(), i32>(&store, "main")
        .unwrap()
        .call(&mut store, ())
        .unwrap_or_else(|e| panic!("{source}: {e}"))
}

const DECLS: &str = "type P { x: i32, y: i64 } \
    type Shape [ Empty, Circle(f64), Rect(i32, i32), Poly(P, array<u8, 3>) ] \
    type H { n: i32, s: Shape, m: u8 } \
    fn make(n: i32) -> Shape { if n > 0 { Shape::Rect(n, 2) } else { Shape::Empty } } \
    fn eat(s: Shape) -> i32 { 3 } \
    fn peek(s: borrow Shape) -> i32 { 4 } \
    fn poke(s: share Shape) { s = Shape::Circle(1.5); } \
    fn pass(s: Shape) -> Shape { s } ";

fn program(body: &str) -> String {
    format!("{DECLS} fn main() -> i32 {{ {body} }}")
}

#[test]
fn building_and_moving_enums_compiles_and_runs() {
    assert_eq!(
        run(&program(
            "let a := Shape::Empty; let b := Shape::Circle(2.5); let c := Shape::Rect(3, 4); \
             let d := Shape::Poly(P { x: 1, y: 2 }, [1, 2, 3]); let e := a; let f := d; 42"
        )),
        42
    );
}

#[test]
fn enums_cross_calls_by_move_borrow_and_share() {
    assert_eq!(
        run(&program(
            "var s := Shape::Rect(5, 6); \
             let a := peek(s.borrow()); poke(s.share()); let b := peek(s.borrow()); \
             let c := eat(s); let t := pass(make(2)); let d := eat(t); \
             a + b + c + d"
        )),
        4 + 4 + 3 + 3
    );
}

#[test]
fn results_joins_and_loops_with_enums() {
    assert_eq!(
        run(&program(
            "var total := 0; var i := 0; \
             loop { if i == 5 { break; } let s := make(i); total += eat(s); i += 1; } \
             let j := if total > 100 { Shape::Empty } else { Shape::Circle(0.5) }; \
             total + eat(j)"
        )),
        15 + 3
    );
}

#[test]
fn whole_assignment_replaces_the_value() {
    assert_eq!(
        run(&program(
            "var s := Shape::Empty; s = Shape::Circle(1.0); s = make(3); s = pass(s); eat(s)"
        )),
        3
    );
}

#[test]
fn enum_fields_arrays_and_repetition_run() {
    assert_eq!(
        run(&program(
            "let h := H { n: 7, s: Shape::Rect(1, 2), m: 9 }; \
             let a := [Shape::Empty, make(2), Shape::Circle(1.0)]; \
             let r := [Shape::Rect(1, 2); 4]; \
             var g: array<Shape, 2> = [Shape::Empty; 2]; g[1] = Shape::Circle(2.0); \
             let k := peek(g[0].borrow()); \
             h.n + k"
        )),
        7 + 4
    );
}

#[test]
fn enum_payloads_nest_through_enums_structs_and_arrays() {
    assert_eq!(
        run(
            "type In [ Leaf, Num(i64) ] type Mid { a: array<In, 2>, k: u8 } \
             type Out [ Wrap(In), Many(Mid), Pair(In, In) ] \
             fn count(o: borrow Out) -> i32 { 5 } \
             fn main() -> i32 { \
                 let a := Out::Wrap(In::Num(9)); \
                 let m := Mid { a: [In::Leaf, In::Num(1)], k: 3 }; \
                 let b := Out::Many(m); \
                 let c := Out::Pair(In::Leaf, In::Num(2)); \
                 count(a.borrow()) + count(b.borrow()) + count(c.borrow()) }"
        ),
        15
    );
}

#[test]
fn many_variant_enums_run() {
    let variants = (0..300)
        .map(|i| format!("V{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    assert_eq!(
        run(&format!(
            "type Big [ {variants} ] fn main() -> i32 {{ let a := Big::V0; let b := Big::V299; 1 }}"
        )),
        1
    );
}

#[test]
fn an_enum_frame_over_the_configured_stack_is_a_diagnostic() {
    let source = "type Big [ A(array<i64, 5000>), B ] \
                  fn main() -> i32 { let b := Big::B; 1 }";
    let program = lower(source);
    let exports = exports_of(&program, &["main"]);
    let options = CompileOptions {
        stack_size: 32 * 1024,
    };
    let errors = compile_with(&program, &exports, &options).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|d| d.message.contains("enum frame layout of")
                && d.message.contains("configured stack size")),
        "{errors:?}"
    );
    // Within the default stack the same program runs.
    assert_eq!(run(source), 1);
}

#[test]
fn enum_layout_overflow_is_reported_not_wrapped() {
    let source =
        "type Huge [ A(array<array<array<i64, 65536>, 65536>, 65536>) ] fn main() -> i32 { 1 }";
    let program = lower(source);
    let errors = compile(&program, &BTreeMap::new()).unwrap_err();
    assert!(
        errors.iter().any(|d| d.message.contains("overflows")),
        "{errors:?}"
    );
}

#[test]
fn exported_signatures_cannot_use_enums() {
    for source in [
        "type E [ A, B(i32) ] pub fn f(e: E) -> i32 { 1 } fn main() -> i32 { 1 }",
        "type E [ A, B(i32) ] pub fn f(e: borrow E) -> i32 { 1 } fn main() -> i32 { 1 }",
        "type E [ A, B(i32) ] pub fn f() -> E { E::A } fn main() -> i32 { 1 }",
    ] {
        let program = lower(source);
        let exports = exports_of(&program, &["f"]);
        let errors = compile(&program, &exports).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("enums") && d.message.contains("ABI")),
            "{source}: {errors:?}"
        );
    }
}
