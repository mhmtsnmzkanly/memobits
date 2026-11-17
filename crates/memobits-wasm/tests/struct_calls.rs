//! Wasm execution of struct mutation, whole-value moves, parameters and results
//! (package A2): the aggregate machinery shared with arrays.
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

fn compile(source: &str) -> Vec<u8> {
    let program = lower(source);
    let main = program.functions.len() as u32 - 1;
    let exports = BTreeMap::from([("main".to_string(), memobits_ir::FunctionId(main))]);
    let wasm = memobits_wasm::compile(&program, &exports).unwrap_or_else(|e| panic!("{e:?}"));
    wasmparser::validate(&wasm).unwrap();
    wasm
}

fn run_as<R: wasmi::WasmResults>(source: &str) -> Result<R, wasmi::Error> {
    let wasm = compile(source);
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
}

fn run(source: &str) -> i32 {
    run_as::<i32>(source).unwrap_or_else(|error| panic!("{source}: {error}"))
}

const P: &str = "type P { x: i32, y: i32 } ";

#[test]
fn var_struct_field_writes_and_compound_writes() {
    assert_eq!(
        run(&format!(
            "{P} fn main() -> i32 {{ var p := P {{ x: 1, y: 2 }}; p.x = 10; p.y += 5; p.x -= 1; p.y *= 2; p.x + p.y }}"
        )),
        9 + 14
    );
    // All scalar compound operators.
    assert_eq!(
        run("type Q { a: i32 } fn main() -> i32 { var q := Q { a: 100 }; q.a += 5; q.a -= 3; q.a *= 2; q.a /= 4; q.a %= 7; q.a }"),
        ((100 + 5 - 3) * 2 / 4) % 7
    );
}

#[test]
fn field_write_evaluation_order_is_base_then_right_hand_side_then_store() {
    // The right-hand side mutates the struct through a share first; the plain
    // write then overwrites that field, so only the call's other effect shows.
    assert_eq!(
        run("type P { x: i32, y: i32 } \
             fn tick(p: share P) -> i32 { p.y += 1; p.x = 100; 7 } \
             fn main() -> i32 { var p := P { x: 1, y: 10 }; p.x = tick(p.share()); p.x * 100 + p.y }"),
        7 * 100 + 11
    );
    // A compound write reads the old value before the call runs.
    assert_eq!(
        run("type P { x: i32 } \
             fn tick(p: share P) -> i32 { p.x += 50; 1 } \
             fn main() -> i32 { var p := P { x: 5 }; p.x += tick(p.share()); p.x }"),
        6
    );
}

#[test]
fn whole_struct_moves_copy_every_field() {
    assert_eq!(
        run(&format!(
            "{P} fn main() -> i32 {{ let p := P {{ x: 3, y: 4 }}; let q := p; q.x * 10 + q.y }}"
        )),
        34
    );
    assert_eq!(
        run(&format!(
            "{P} fn main() -> i32 {{ var a := P {{ x: 1, y: 2 }}; var b := P {{ x: 3, y: 4 }}; b = a; a = P {{ x: 9, y: 8 }}; a.x * 1000 + a.y * 100 + b.x * 10 + b.y }}"
        )),
        9000 + 800 + 10 + 2
    );
    // Self-referential assignment builds the new value before storing it.
    assert_eq!(
        run(&format!(
            "{P} fn main() -> i32 {{ var a := P {{ x: 1, y: 2 }}; a = P {{ x: a.y, y: a.x }}; a.x * 10 + a.y }}"
        )),
        21
    );
}

#[test]
fn struct_valued_if_and_blocks() {
    let source = |c: &str| {
        format!(
            "{P} fn main() -> i32 {{ let c := {c}; let p := if c {{ P {{ x: 1, y: 2 }} }} else {{ P {{ x: 3, y: 4 }} }}; p.x * 10 + p.y }}"
        )
    };
    assert_eq!(run(&source("true")), 12);
    assert_eq!(run(&source("false")), 34);
    assert_eq!(
        run(&format!(
            "{P} fn main() -> i32 {{ let a := P {{ x: 5, y: 6 }}; let p := if 1 < 2 {{ a }} else {{ P {{ x: 0, y: 0 }} }}; let q := {{ p }}; q.x + q.y }}"
        )),
        11
    );
}

#[test]
fn borrow_and_share_parameters_see_and_change_the_caller() {
    assert_eq!(
        run("type P { x: i32, y: i32 } \
             fn bump(p: share P, n: i32) { p.x += n; p.y = p.y + n; } \
             fn sum(p: borrow P) -> i32 { p.x + p.y } \
             fn forward(p: share P) { bump(p.share(), 1); } \
             fn main() -> i32 { var p := P { x: 1, y: 2 }; bump(p.share(), 10); forward(p.share()); sum(p.borrow()) }"),
        1 + 10 + 1 + 2 + 10 + 1
    );
    // Local reference bindings and reborrows.
    assert_eq!(
        run("type P { x: i32, y: i32 } \
             fn inner(p: borrow P) -> i32 { p.y + 0 } \
             fn outer(p: borrow P) -> i32 { inner(p.borrow()) + p.x } \
             fn main() -> i32 { var p := P { x: 3, y: 4 }; var s := p.share(); s.x = 30; s.y += 1; let r := p.borrow(); outer(r.borrow()) + r.x }"),
        5 + 30 + 30
    );
    // Whole-struct assignment through a share parameter.
    assert_eq!(
        run("type P { x: i32, y: i32 } \
             fn reset(p: share P) { p = P { x: 7, y: 8 }; } \
             fn main() -> i32 { var p := P { x: 1, y: 2 }; reset(p.share()); p.x * 10 + p.y }"),
        78
    );
}

#[test]
fn owned_parameters_copy_in_and_never_touch_the_caller() {
    assert_eq!(
        run("type P { x: i32, y: i32 } \
             fn bump(var p: P) -> i32 { p.x += 100; p.x + p.y } \
             fn main() -> i32 { let p := P { x: 1, y: 2 }; let r := bump(p); r }"),
        103
    );
    // A literal and a call result are valid owned arguments.
    assert_eq!(
        run("type P { x: i32, y: i32 } \
             fn make() -> P { P { x: 4, y: 5 } } \
             fn sum(p: P) -> i32 { p.x + p.y } \
             fn main() -> i32 { sum(P { x: 1, y: 2 }) * 100 + sum(make()) }"),
        309
    );
}

#[test]
fn struct_results_returned_literal_local_and_parameter() {
    assert_eq!(
        run("type P { x: i32, y: i32 } \
             fn lit() -> P { P { x: 1, y: 2 } } \
             fn local(n: i32) -> P { var p := P { x: n, y: n }; p.y += 1; p } \
             fn pass(p: P) -> P { p } \
             fn early(n: i32) -> P { if n > 0 { return P { x: n, y: 0 }; } P { x: 0, y: 9 } } \
             fn main() -> i32 { \
                 let a := lit(); let b := local(5); let c := pass(b); let d := early(3); let e := early(0); \
                 var f := P { x: 0, y: 0 }; f = pass(lit()); \
                 a.x + a.y * 10 + c.x * 100 + c.y * 1000 + d.x * 10000 + e.y * 100000 + f.y * 1000000 }"),
        1 + 20 + 500 + 6000 + 30000 + 900000 + 2000000
    );
}

#[test]
fn constructor_function_consumed_by_a_borrow_taking_function() {
    assert_eq!(
        run("type Account { id: u32, balance: i64, active: Bool } \
             fn open(id: u32) -> Account { Account { id: id, balance: 0, active: true } } \
             fn deposit(a: share Account, amount: i64) { a.balance += amount; } \
             fn describe(a: borrow Account) -> i64 { if a.active { a.balance * 2 } else { 0 } } \
             fn main() -> i32 { \
                 var a := open(7); deposit(a.share(), 20); deposit(a.share(), 1); \
                 let r := describe(a.borrow()); \
                 if r == 42 { 1 } else { 0 } }"),
        1
    );
}

#[test]
fn recursion_accumulates_in_a_struct_through_results() {
    assert_eq!(
        run("type Acc { sum: i32, count: i32 } \
             fn step(a: Acc, n: i32) -> Acc { if n == 0 { a } else { step(Acc { sum: a.sum + n, count: a.count + 1 }, n - 1) } } \
             fn main() -> i32 { let r := step(Acc { sum: 0, count: 0 }, 10); r.sum * 100 + r.count }"),
        5510
    );
    // A share parameter threaded through the recursion.
    assert_eq!(
        run("type Acc { sum: i32 } \
             fn go(a: share Acc, n: i32) { if n > 0 { a.sum += n; go(a.share(), n - 1); } } \
             fn main() -> i32 { var a := Acc { sum: 0 }; go(a.share(), 100); a.sum }"),
        5050
    );
}

#[test]
fn mixed_width_fields_survive_calls_results_and_copies() {
    let decls = "type M { a: u8, b: i64, c: f32, d: Bool, e: i16, f: f64 } \
        fn make() -> M { M { a: 200, b: -5_000_000_000, c: 1.5, d: true, e: -300, f: 2.25 } } \
        fn pass(m: M) -> M { m } \
        fn edit(m: share M) { m.a = 255; m.b -= 1; m.c = 0.5; m.d = false; m.e += 1; m.f *= 2.0; } ";
    assert_eq!(
        run_as::<i64>(&format!(
            "{decls} fn main() -> i64 {{ var m := pass(make()); edit(m.share()); m.b }}"
        ))
        .unwrap(),
        -5_000_000_001
    );
    assert_eq!(
        run(&format!(
            "{decls} fn main() -> i32 {{ var m := pass(make()); let before := m.a; edit(m.share()); if before == 200 {{ if m.a == 255 {{ 1 }} else {{ 0 }} }} else {{ 0 }} }}"
        )),
        1
    );
    assert_eq!(
        run_as::<i32>(&format!(
            "{decls} fn main() -> i32 {{ var m := pass(make()); edit(m.share()); if m.d {{ 0 }} else {{ if m.e == -299 {{ 1000 }} else {{ 1 }} }} }}"
        ))
        .unwrap(),
        1000
    );
    assert_eq!(
        run_as::<f32>(&format!(
            "{decls} fn main() -> f32 {{ var m := pass(make()); edit(m.share()); m.c + 1.0 }}"
        ))
        .unwrap(),
        1.5
    );
    assert_eq!(
        run_as::<f64>(&format!(
            "{decls} fn main() -> f64 {{ let m := make(); let n := pass(m); n.f }}"
        ))
        .unwrap(),
        2.25
    );
    // Narrow stores through a share must not clobber neighbouring fields.
    assert_eq!(
        run("type N { a: u8, b: u8, c: u8, d: u8 } \
             fn set(n: share N) { n.b = 7; n.d = 9; } \
             fn main() -> i32 { var n := N { a: 1, b: 2, c: 3, d: 4 }; set(n.share()); if n.a == 1 && n.b == 7 && n.c == 3 && n.d == 9 { 1 } else { 0 } }"),
        1
    );
}

#[test]
fn zero_field_and_checked_arithmetic_in_field_writes() {
    assert_eq!(
        run("type U {} fn make() -> U { U {} } fn take(u: U) -> i32 { 3 } fn main() -> i32 { take(make()) }"),
        3
    );
    // Overflow in a compound field write traps like any checked arithmetic.
    assert!(run_as::<i32>(
        "type B { b: u8 } fn main() -> i32 { var b := B { b: 250 }; b.b += 10; 0 }"
    )
    .is_err());
}

#[test]
fn exported_struct_signatures_are_rejected_by_the_backend() {
    for source in [
        "type P { x: i32 } fn main(p: P) -> i32 { 0 }",
        "type P { x: i32 } fn main(p: borrow P) -> i32 { 0 }",
        "type P { x: i32 } fn main(p: share P) -> i32 { 0 }",
        "type P { x: i32 } fn main() -> P { P { x: 1 } }",
    ] {
        let program = lower(source);
        let exports = BTreeMap::from([("main".to_string(), memobits_ir::FunctionId(0))]);
        let errors = memobits_wasm::compile(&program, &exports).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("cannot take structs")
                    || d.message.contains("cannot return structs")),
            "{source}: {errors:?}"
        );
    }
}
