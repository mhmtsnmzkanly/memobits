//! Wasm execution of `match` on owned enums (package B2): tag reads at every
//! tag width, the `Switch` compare chain, payload extraction (primitives,
//! structs, arrays, nested enums), joins, divergent arms and loops.
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

const DECLS: &str = "type P { x: i32, y: i64 } \
    type Shape [ Empty, Circle(f64), Rect(i32, i32), Poly(P, array<u8, 3>) ] \
    type Wrap [ Plain, Boxed(Shape), Pair(Shape, i32) ] \
    fn make(n: i32) -> Shape { \
        if n == 0 { Shape::Empty } else if n == 1 { Shape::Circle(2.5) } \
        else if n == 2 { Shape::Rect(3, 4) } \
        else { Shape::Poly(P { x: 5, y: 6 }, [7, 8, 9]) } } \
    fn score(s: Shape) -> i32 { \
        match s { \
            Shape::Empty => 100, \
            Shape::Circle(r) => if r > 2.0 { 200 } else { 201 }, \
            Shape::Rect(w, h) => w * 10 + h, \
            Shape::Poly(p, a) => { let tail: u8 = a[2]; p.x + p.x * 1000 } \
        } } ";

fn program(body: &str) -> String {
    format!("{DECLS} fn main() -> i32 {{ {body} }}")
}

#[test]
fn every_variant_selects_its_arm_and_binds_its_payload() {
    assert_eq!(run(&program("score(make(0))")), 100);
    assert_eq!(run(&program("score(make(1))")), 200);
    assert_eq!(run(&program("score(make(2))")), 34);
    assert_eq!(run(&program("score(make(3))")), 5005);
}

#[test]
fn payload_fields_keep_their_declared_order_and_values() {
    assert_eq!(
        run(&program(
            "match Shape::Rect(7, 9) { Shape::Rect(a, b) => a * 100 + b, _ => 0 }"
        )),
        709
    );
    // Ignoring the first slot binds the second.
    assert_eq!(
        run(&program(
            "match Shape::Rect(7, 9) { Shape::Rect(_, b) => b, _ => 0 }"
        )),
        9
    );
    assert_eq!(
        run(&program(
            "match Shape::Poly(P { x: 1, y: 2 }, [4, 5, 6]) { \
             Shape::Poly(_, a) => { let z: u8 = a[1]; 55 } _ => 0 }"
        )),
        55
    );
}

#[test]
fn aggregate_payloads_move_into_bindings_and_are_readable() {
    assert_eq!(
        run(&program(
            "match Shape::Poly(P { x: 11, y: 22 }, [1, 2, 3]) { \
             Shape::Poly(p, a) => { let q := p; q.x + q.x } _ => 0 }"
        )),
        22
    );
    assert_eq!(
        run(&program(
            "match Shape::Poly(P { x: 11, y: 22 }, [1, 2, 3]) { \
             Shape::Poly(p, a) => { let b := a; let last: u8 = b[2]; 3 } _ => 0 }"
        )),
        3
    );
}

#[test]
fn nested_enums_match_in_two_steps() {
    assert_eq!(
        run(&program(
            "let w := Wrap::Pair(Shape::Rect(2, 5), 7); \
             match w { \
                Wrap::Pair(inner, k) => match inner { Shape::Rect(a, b) => a * b + k, _ => 0 }, \
                _ => 1 }"
        )),
        17
    );
    assert_eq!(
        run(&program(
            "match Wrap::Boxed(make(1)) { Wrap::Boxed(s) => score(s), _ => 0 }"
        )),
        200
    );
}

#[test]
fn a_default_arm_covers_the_unlisted_variants() {
    let body = "var total := 0; var i := 0; \
        loop { if i == 4 { break; } \
        total += match make(i) { Shape::Rect(w, h) => w + h, _ => 1000 }; i += 1; } total";
    assert_eq!(run(&program(body)), 3 * 1000 + 7);
}

#[test]
fn matches_in_loops_rebuild_the_enum_each_iteration() {
    assert_eq!(
        run(&program(
            "var total := 0; var i := 0; \
             loop { if i == 4 { break; } total += score(make(i)); i += 1; } total"
        )),
        100 + 200 + 34 + 5005
    );
}

#[test]
fn divergent_arms_return_break_and_continue() {
    assert_eq!(
        run(&program(
            "match make(0) { Shape::Empty => return 77, _ => 1 }"
        )),
        77
    );
    assert_eq!(
        run(&program(
            "var n := 0; var i := 0; \
             loop { i += 1; if i > 5 { break; } \
             let k := match make(i - 1) { Shape::Empty => continue, Shape::Circle(_) => { n += 10; 1 } \
                 _ => if i == 5 { break; } else { 2 } }; n += k; } n"
        )),
        // i=1 Empty: continue; i=2 Circle: +10 +1; i=3 Rect: +2; i=4 Poly: +2; i=5 break.
        15
    );
}

#[test]
fn statement_position_match_runs_for_effect() {
    assert_eq!(
        run(&program(
            "var n := 0; match make(2) { Shape::Rect(w, h) => { n = w + h; } _ => {} } n"
        )),
        7
    );
}

#[test]
fn a_match_result_can_be_an_enum() {
    assert_eq!(
        run(&program(
            "let s := match make(2) { Shape::Rect(w, h) => Shape::Circle(1.0), _ => make(0) }; score(s)"
        )),
        201
    );
}

#[test]
fn a_state_machine_steps_in_a_loop() {
    let source = "type State [ Start, Running(i32), Done(i32) ] \
        fn main() -> i32 { \
            var s := State::Start; var fuel := 20; \
            loop { \
                fuel -= 1; \
                if fuel == 0 { return -9; } \
                s = match s { \
                    State::Start => State::Running(1), \
                    State::Running(n) => if n >= 5 { State::Done(n * 10) } else { State::Running(n + 1) }, \
                    State::Done(n) => return n }; } \
            0 }";
    assert_eq!(run(source), 50);
}

#[test]
fn recursion_through_a_function_returning_an_enum() {
    let source = "type State [ Start, Running(i32), Done(i32) ] \
        fn step(s: State) -> State { \
            match s { \
                State::Start => State::Running(1), \
                State::Running(n) => if n >= 5 { State::Done(n * 10) } else { State::Running(n + 1) }, \
                State::Done(n) => State::Done(n) } } \
        fn finish(s: State, fuel: i32) -> i32 { \
            if fuel == 0 { return -1; } \
            match step(s) { State::Done(n) => n, State::Running(n) => finish(State::Running(n), fuel - 1), \
                State::Start => finish(State::Start, fuel - 1) } } \
        fn main() -> i32 { finish(State::Start, 20) }";
    assert_eq!(run(source), 50);
}

#[test]
fn wide_tags_are_read_with_their_own_width() {
    // 300 variants need a u16 tag; matching the last one reads both bytes.
    let variants: Vec<String> = (0..300).map(|i| format!("V{i}(i32)")).collect();
    let source = format!(
        "type Big [ {} ] fn main() -> i32 {{ \
            match Big::V299(41) {{ Big::V0(a) => a, Big::V298(a) => a + 100, \
            Big::V299(a) => a + 1, _ => 0 }} }}",
        variants.join(", ")
    );
    assert_eq!(run(&source), 42);
    let source = format!(
        "type Big [ {} ] fn main() -> i32 {{ \
            match Big::V256(5) {{ Big::V0(a) => a, Big::V256(a) => a + 1, _ => 0 }} }}",
        variants.join(", ")
    );
    assert_eq!(run(&source), 6);
}

#[test]
fn single_variant_and_unit_only_enums_match() {
    assert_eq!(
        run("type One [ Only(i32) ] fn main() -> i32 { match One::Only(9) { One::Only(n) => n } }"),
        9
    );
    assert_eq!(
        run("type Flag [ Off, On ] fn main() -> i32 { match Flag::On { Flag::Off => 0, Flag::On => 1 } }"),
        1
    );
}
