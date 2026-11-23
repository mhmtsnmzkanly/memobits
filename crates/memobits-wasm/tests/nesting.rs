//! Wasm execution of nested aggregates (package A3): layout, chained
//! addresses, bounds checks at every level and the configured stack limit.
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

fn try_run(source: &str) -> Result<i32, wasmi::Error> {
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
    instance
        .get_typed_func::<(), i32>(&store, "main")
        .unwrap()
        .call(&mut store, ())
}

fn run(source: &str) -> i32 {
    try_run(source).unwrap_or_else(|error| panic!("{source}: {error}"))
}

const TYPES: &str = "type P { x: i32, y: i32 } \
    type Line { a: P, b: P } \
    type Poly { n: u8, pts: array<i32, 4>, c: P } ";

#[test]
fn struct_in_struct_reads_writes_and_replacement() {
    assert_eq!(
        run(&format!(
            "{TYPES} fn main() -> i32 {{ \
             var l := Line {{ a: P {{ x: 1, y: 2 }}, b: P {{ x: 3, y: 4 }} }}; \
             l.a.x = 10; l.b.y += 5; \
             l.a = P {{ x: l.a.x + 1, y: 20 }}; \
             let o := P {{ x: 30, y: 40 }}; l.b = o; \
             l.a.x * 1000000 + l.a.y * 10000 + l.b.x * 100 + l.b.y }}"
        )),
        11 * 1_000_000 + 20 * 10_000 + 30 * 100 + 40
    );
}

#[test]
fn array_fields_index_replace_and_compound_write() {
    assert_eq!(
        run(&format!(
            "{TYPES} fn main() -> i32 {{ \
             var p := Poly {{ n: 7, pts: [1, 2, 3, 4], c: P {{ x: 5, y: 6 }} }}; \
             p.pts[2] += 10; \
             let before := p.pts[2]; \
             p.pts = [p.pts[3] + 0, p.pts[2] + 0, p.pts[1] + 0, p.pts[0] + 0]; \
             before * 1000 + p.pts[0] * 100 + p.pts[1] * 10 + p.pts[3] }}"
        )),
        13 * 1000 + 4 * 100 + 13 * 10 + 1
    );
}

#[test]
fn arrays_of_structs_with_array_fields_nest_to_any_depth() {
    assert_eq!(
        run(&format!(
            "{TYPES} fn main() -> i32 {{ \
             var a := [Poly {{ n: 1, pts: [1, 2, 3, 4], c: P {{ x: 5, y: 6 }} }}; 3]; \
             a[1].pts[2] = 99; a[2].c.x += 1; a[0].pts[3] = a[1].pts[2] + 1; \
             a[2] = Poly {{ n: 2, pts: [0, 0, 0, 7], c: P {{ x: 8, y: 9 }} }}; \
             a[1].pts[2] + a[0].pts[3] + a[2].pts[3] + a[2].c.y + a[0].c.x + a[1].pts[0] }}"
        )),
        99 + 100 + 7 + 9 + 5 + 1
    );
}

#[test]
fn nested_aggregates_move_across_calls_and_results() {
    // g.pts[0] = 101; h.pts[0] = 201 and h.c.y = 201; sum = 101 + 201 = 302.
    assert_eq!(
        run(&format!(
            "{TYPES} \
             fn make() -> Poly {{ Poly {{ n: 1, pts: [1, 2, 3, 4], c: P {{ x: 5, y: 6 }} }} }} \
             fn grow(var p: Poly) -> Poly {{ p.pts[0] += 100; p.c.y = p.pts[0] + 0; p }} \
             fn pick(c: bool) -> Line {{ if c {{ Line {{ a: P {{ x: 1, y: 1 }}, b: P {{ x: 2, y: 2 }} }} }} else {{ Line {{ a: P {{ x: 3, y: 3 }}, b: P {{ x: 4, y: 4 }} }} }} }} \
             fn sum(a: borrow array<Poly, 2>) -> i32 {{ a[0].pts[0] + a[1].c.y }} \
             fn main() -> i32 {{ \
                 let g := grow(make()); \
                 let h := grow(grow(make())); \
                 let arr := [g, h]; \
                 let l := pick(false); \
                 sum(arr.borrow()) * 10 + l.b.x }}"
        )),
        302 * 10 + 4
    );
}

#[test]
fn mixed_widths_survive_nesting_inside_arrays() {
    // Q is 24 bytes (u8 @0, i64 @8, f32 @16, Bool @20); R packs a Q, two Qs and
    // an i16 after a u8, so every inner offset depends on the nested alignment.
    let source = "type Q { a: u8, b: i64, f: f32, ok: bool } \
        type R { tag: u8, q: Q, xs: array<Q, 2>, last: i16 } \
        fn bump(r: share R) { r.xs[1].b += 5; r.xs[0].ok = true; r.last = -3; r.q.f = 2.5; } \
        fn mk() -> R { R { tag: 1, q: Q { a: 1, b: 2, f: 0.5, ok: false }, \
            xs: [Q { a: 7, b: 8, f: 1.0, ok: true }, Q { a: 9, b: 10, f: 1.5, ok: false }], last: 11 } } \
        fn score(r: borrow R) -> i32 { \
            var s := 0; \
            if r.tag == 1 { s += 1; } \
            if r.q.a == 1 { s += 2; } \
            if r.q.b == 2 { s += 4; } \
            if r.q.f == 2.5 { s += 8; } \
            if r.q.ok { s += 100000; } \
            if r.xs[0].a == 7 { s += 16; } \
            if r.xs[0].b == 8 { s += 32; } \
            if r.xs[0].ok { s += 64; } \
            if r.xs[1].a == 9 { s += 128; } \
            if r.xs[1].b == 15 { s += 256; } \
            if r.xs[1].ok { s += 200000; } \
            if r.last == -3 { s += 512; } \
            s } \
        fn main() -> i32 { var r := mk(); bump(r.share()); score(r.borrow()) }";
    assert_eq!(run(source), 1023);
}

#[test]
fn bounds_are_checked_at_every_level() {
    let setup = format!(
        "{TYPES} fn main() -> i32 {{ \
         var a := [Poly {{ n: 1, pts: [1, 2, 3, 4], c: P {{ x: 5, y: 6 }} }}; 2]; \
         var i := 0; var j := 0; "
    );
    // In range at both levels.
    assert_eq!(
        run(&format!(
            "{setup} i = 1; j = 3; a[i].pts[j] = 9; a[1].pts[3] }}"
        )),
        9
    );
    // Outer index out of range, inner index out of range, negative, wide.
    for body in [
        "i = 2; a[i].pts[0] = 1; 0",
        "j = 4; a[0].pts[j] = 1; 0",
        "i = 2; a[i].pts[0]",
        "j = 4; a[0].pts[j]",
        "j = 4; a[0].pts[j] += 1; 0",
        "i = 5; a[i].c.x",
    ] {
        assert!(try_run(&format!("{setup} {body} }}")).is_err(), "{body}");
    }
    assert!(try_run(&format!("{setup} let k: i64 = -1; a[0].pts[k] }}")).is_err());
    // The bounds trap fires after the right-hand side's effects.
    assert!(try_run(&format!(
        "{TYPES} fn bad() -> i32 {{ 1 }} fn main() -> i32 {{ \
         var a := [Poly {{ n: 1, pts: [1, 2, 3, 4], c: P {{ x: 5, y: 6 }} }}; 2]; \
         var i := 3; a[i].pts[0] = bad(); 0 }}"
    ))
    .is_err());
}

#[test]
fn zero_length_arrays_of_structs_are_empty() {
    assert_eq!(
        run("type P { x: i32 } type Z { e: array<P, 0>, n: i32 } \
             fn main() -> i32 { let a: array<P, 0> = [P { x: 1 }; 0]; let z := Z { e: a, n: 5 }; z.n }"),
        5
    );
    assert!(try_run(
        "type P { x: i32 } fn main() -> i32 { let a: array<P, 0> = [P { x: 1 }; 0]; var i := 0; a[i].x }"
    )
    .is_err());
}

#[test]
fn repeating_a_struct_literal_evaluates_it_per_element() {
    assert_eq!(
        run("type P { x: i32, y: i32 } \
             fn next(c: share i32) -> i32 { c += 1; c + 0 } \
             fn main() -> i32 { var c := 0; \
                 let a := [P { x: next(c.share()), y: 0 }; 4]; \
                 a[0].x * 1000 + a[1].x * 100 + a[2].x * 10 + a[3].x }"),
        1234
    );
}

#[test]
fn nested_frames_over_the_configured_stack_are_diagnostics() {
    let source = "type P { x: i32 } type Big { a: array<P, 10000> } \
                  fn main() -> i32 { let b := Big { a: [P { x: 1 }; 10000] }; b.a[9999].x }";
    let program = lower(source);
    let exports = BTreeMap::from([("main".to_string(), memobits_ir::FunctionId(0))]);
    let small = memobits_wasm::CompileOptions {
        stack_size: 32 * 1024,
    };
    let errors = memobits_wasm::compile_with(&program, &exports, &small).unwrap_err();
    assert!(
        errors.iter().any(|d| d.message.contains("frame layout of")
            && d.message.contains("configured stack size")),
        "{errors:?}"
    );
    let large = memobits_wasm::CompileOptions {
        stack_size: 256 * 1024,
    };
    assert!(memobits_wasm::compile_with(&program, &exports, &large).is_ok());
    // Overflowing the 32-bit address space is a layout diagnostic, not a wrap.
    let huge = lower(
        "type P { x: i64 } type A { a: array<array<array<P, 65536>, 65536>, 65536> } fn main() {}",
    );
    let errors = memobits_wasm::compile(&huge, &BTreeMap::new()).unwrap_err();
    assert!(
        errors.iter().any(|d| d.message.contains("overflows")),
        "{errors:?}"
    );
}
