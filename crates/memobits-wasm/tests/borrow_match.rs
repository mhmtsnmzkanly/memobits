//! Wasm execution of borrowing `match` (package B3): element, field and
//! reference scrutinees, payload addresses (`VariantAddr`) at their variant
//! offsets, copies of primitive payloads and references to aggregate ones.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_ir::{FunctionId, Program};
use memobits_syntax::parse;
use memobits_wasm::compile;
use std::collections::BTreeMap;
use wasmi::{Engine, Linker, Module, Store};

fn lower(source: &str) -> Program {
    let parsed = parse(SourceId(0), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"))
}

fn run(source: &str) -> i32 {
    let program = lower(source);
    let index = program
        .functions
        .iter()
        .position(|f| f.path.name == "main")
        .unwrap();
    let exports = BTreeMap::from([("main".to_string(), FunctionId(index as u32))]);
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

const DECLS: &str = "type P { x: i32, y: i32 } \
    type Shape [ Empty, Circle(f64), Rect(i32, i32), Poly(P, Array<i32, 3>) ] \
    type Wrap [ Plain, Boxed(Shape), Pair(Shape, i32) ] \
    type H { n: i32, s: Shape } \
    fn px(p: borrow P) -> i32 { p.y } \
    fn weigh(s: borrow Shape) -> i32 { \
        match s { \
            Shape::Empty => 100, \
            Shape::Circle(r) => if r > 2.0 { 200 } else { 201 }, \
            Shape::Rect(w, h) => w * 10 + h, \
            Shape::Poly(p, a) => { p.x + a[2] + px(p) } \
        } } \
    fn bump(s: share Shape) -> i32 { match s { Shape::Rect(w, _) => w, _ => 0 } } ";

fn program(body: &str) -> String {
    format!("{DECLS} fn main() -> i32 {{ {body} }}")
}

#[test]
fn matching_array_elements_counts_variants_and_sums_payloads() {
    assert_eq!(
        run(&program(
            "let a: Array<Shape, 4> = [Shape::Rect(3, 4), Shape::Empty, Shape::Circle(1.5), \
                 Shape::Poly(P { x: 5, y: 6 }, [7, 8, 9])]; \
             var rects := 0; var other := 0; var sum := 0; var i := 0; \
             loop { if i == 4 { break; } \
                 match a[i] { \
                     Shape::Rect(w, h) => { rects += 1; sum += w * h; } \
                     Shape::Poly(p, a2) => { other += 1; sum += p.x + a2[1]; } \
                     _ => { other += 1; } \
                 } \
                 i += 1; } \
             rects * 10000 + other * 1000 + sum"
        )),
        10000 + 3000 + 12 + 13
    );
}

#[test]
fn matching_a_struct_field_and_a_nested_place() {
    assert_eq!(
        run(&program(
            "let h := H { n: 4, s: Shape::Rect(6, 7) }; \
             match h.s { Shape::Rect(w, k) => w * k + h.n, _ => 0 }"
        )),
        46
    );
    assert_eq!(
        run(&program(
            "let hs := [H { n: 1, s: Shape::Empty }, H { n: 2, s: Shape::Rect(2, 3) }]; \
             var i := 1; match hs[i].s { Shape::Rect(w, k) => w + k + hs[i].n, _ => 0 }"
        )),
        7
    );
}

#[test]
fn borrow_and_share_parameters_match_in_place() {
    assert_eq!(
        run(&program(
            "let a := [Shape::Rect(2, 5), Shape::Circle(3.0), Shape::Poly(P { x: 1, y: 20 }, [1, 2, 3])]; \
             let h := H { n: 0, s: Shape::Empty }; \
             weigh(a[0].borrow()) + weigh(a[1].borrow()) + weigh(a[2].borrow()) + weigh(h.s.borrow())"
        )),
        25 + 200 + (1 + 3 + 20) + 100
    );
    assert_eq!(
        run(&program(
            "var s := Shape::Rect(9, 1); bump(s.share()) + weigh(s.borrow()) - 90"
        )),
        10
    );
}

#[test]
fn matching_does_not_consume_the_place_and_leaves_it_intact() {
    assert_eq!(
        run(&program(
            "var h := H { n: 0, s: Shape::Poly(P { x: 11, y: 22 }, [1, 2, 3]) }; \
             let first := match h.s { Shape::Poly(p, _) => p.x, _ => 0 }; \
             let again := match h.s { Shape::Poly(_, a) => a[2], _ => 0 }; \
             h.n = 5; first * 100 + again * 10 + h.n"
        )),
        1100 + 30 + 5
    );
}

#[test]
fn nested_enum_payloads_match_in_a_second_borrowing_match() {
    assert_eq!(
        run(&program(
            "let w := [Wrap::Pair(Shape::Rect(2, 5), 7), Wrap::Boxed(Shape::Circle(1.0))]; \
             match w[0] { \
                 Wrap::Pair(inner, k) => match inner { Shape::Rect(a, b) => a * b + k, _ => 0 }, \
                 _ => 1 }"
        )),
        17
    );
    assert_eq!(
        run(&program(
            "let w := Wrap::Boxed(Shape::Poly(P { x: 3, y: 4 }, [5, 6, 7])); \
             match w.borrow() { Wrap::Boxed(s) => weigh(s), _ => 0 }"
        )),
        3 + 7 + 4
    );
}

#[test]
fn disjoint_writes_and_the_variant_offsets_agree_during_a_live_payload_borrow() {
    assert_eq!(
        run(&program(
            "var h := H { n: 1, s: Shape::Poly(P { x: 11, y: 22 }, [1, 2, 3]) }; \
             match h.s { Shape::Poly(p, a) => { h.n = 50; p.x + a[1] + h.n }, _ => 0 }"
        )),
        11 + 2 + 50
    );
}
