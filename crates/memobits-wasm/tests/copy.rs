//! Wasm execution of the explicit primitive copy `expr.copy()`.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_ir::{FunctionId, Program};
use memobits_syntax::parse;
use std::collections::BTreeMap;
use wasmi::{Engine, Linker, Module, Store};

fn lower(source: &str) -> Program {
    let parsed = parse(SourceId(0), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let program = lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"));
    let mut errors = memobits_ownership::check_moves(&program);
    errors.extend(memobits_ownership::check_loans(&program));
    assert!(errors.is_empty(), "{source}: {errors:?}");
    program
}

fn call(source: &str, argument: Option<wasmi::Val>) -> Option<i32> {
    let program = lower(source);
    let main = program.functions.len() as u32 - 1;
    let exports = BTreeMap::from([("main".to_string(), FunctionId(main))]);
    let wasm = memobits_wasm::compile(&program, &exports).unwrap();
    wasmparser::validate(&wasm).unwrap();
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Linker::new(&engine)
        .instantiate_and_start(&mut store, &module)
        .unwrap();
    let func = instance.get_func(&store, "main").unwrap();
    let mut out = [wasmi::Val::I32(0)];
    let arguments: Vec<_> = argument.into_iter().collect();
    func.call(&mut store, &arguments, &mut out).ok()?;
    match out[0] {
        wasmi::Val::I32(value) => Some(value),
        _ => unreachable!(),
    }
}

fn run(source: &str) -> i32 {
    call(source, None).unwrap_or_else(|| panic!("{source} trapped"))
}

const TYPES: [(&str, &str); 11] = [
    ("i8", "-100"),
    ("i16", "-30000"),
    ("i32", "-2000000000"),
    ("i64", "-9000000000000000000"),
    ("u8", "250"),
    ("u16", "65000"),
    ("u32", "4000000000"),
    ("u64", "18446744073709551000"),
    ("f32", "-2.25"),
    ("f64", "1.5e300"),
    ("Bool", "true"),
];

#[test]
fn copy_of_locals_and_parameters_keeps_the_original_for_every_primitive() {
    for (ty, value) in TYPES {
        let local = format!(
            "fn main() -> Bool {{ let x: {ty} = {value}; let y := x.copy(); let z := x.copy(); y == {value} && z == x && x == {value} }}"
        );
        assert_eq!(run(&local), 1, "{ty} local");
        let parameter = format!(
            "fn dup(v: {ty}) -> Bool {{ let a := v.copy(); let b := v.copy(); a == b && v == a }} \
             fn main() -> Bool {{ dup({value}) }}"
        );
        assert_eq!(run(&parameter), 1, "{ty} parameter");
        // A variable stays usable after being copied and then reassigned.
        let var = format!(
            "fn main() -> Bool {{ var x: {ty} = {value}; let y := x.copy(); x = y.copy(); x == y }}"
        );
        assert_eq!(run(&var), 1, "{ty} var");
    }
}

#[test]
fn copy_of_array_elements_at_every_depth_for_every_primitive() {
    for (ty, value) in TYPES {
        let flat = format!(
            "fn main() -> Bool {{ let a: Array<{ty}, 3> = [{value}; 3]; let x := a[2].copy(); x == {value} && a[1] == x }}"
        );
        assert_eq!(run(&flat), 1, "{ty} flat");
        let nested = format!(
            "fn main() -> Bool {{ let m: Array<Array<{ty}, 2>, 3> = [[{value}; 2]; 3]; let x := m[2][1].copy(); x == {value} && m[0][0] == x }}"
        );
        assert_eq!(run(&nested), 1, "{ty} nested");
    }
}

#[test]
fn copy_through_reference_parameters_for_every_primitive() {
    for (ty, value) in TYPES {
        for access in ["borrow", "share"] {
            let scalar = format!(
                "fn rd(r: {access} {ty}) -> {ty} {{ r.copy() }} \
                 fn main() -> Bool {{ var x: {ty} = {value}; let y := rd(x.{access}()); y == {value} && x == y }}"
            );
            assert_eq!(run(&scalar), 1, "{ty} {access} scalar");
            let element = format!(
                "fn at(p: {access} Array<{ty}, 3>, i: u32) -> {ty} {{ p[i].copy() }} \
                 fn main() -> Bool {{ var a: Array<{ty}, 3> = [{value}; 3]; let y := at(a.{access}(), 2); y == {value} && a[0] == y }}"
            );
            assert_eq!(run(&element), 1, "{ty} {access} element");
        }
    }
}

#[test]
fn copy_results_work_in_every_owned_position() {
    assert_eq!(
        run(
            "fn mk(v: i32) -> Array<i32, 3> { [v.copy(), v.copy() + 1, v + 2] } \
             fn main() -> i32 { let a := mk(10); a[0] * 10000 + a[1] * 100 + a[2] }"
        ),
        10 * 10000 + 11 * 100 + 12
    );
    // Swap two elements.
    assert_eq!(
        run("fn swap(a: share Array<i32, 3>, i: u32, j: u32) { let t := a[i].copy(); a[i] = a[j].copy(); a[j] = t; } \
             fn main() -> i32 { var a := [1, 2, 3]; swap(a.share(), 0, 2); a[0] * 100 + a[1] * 10 + a[2] }"),
        321
    );
    assert_eq!(
        run("fn main() -> i32 { var a := [1, 2, 3]; var i := 0; var j := 2; let t := a[i].copy(); a[i] = a[j].copy(); a[j] = t; a[0] * 100 + a[1] * 10 + a[2] }"),
        321
    );
    // Repetition evaluates the element per iteration for any N.
    assert_eq!(
        run("fn main() -> i32 { let x := 7; let a := [x.copy(); 100]; let b := [x.copy(); 1]; let c := [x.copy(); 0]; a[0] + a[99] + b[0] }"),
        21
    );
    assert_eq!(
        run("fn main() -> i32 { let s := [4, 5]; let a := [s[1].copy(); 3]; a[0] + a[2] }"),
        10
    );
    // Binding, assignment, argument, return, blocks and branches.
    assert_eq!(
        run("fn id(v: i32) -> i32 { v } fn main() -> i32 { let x := 3; let y := if true { x.copy() } else { 0 }; let z := { x.copy() }; id(x.copy()) + y + z + x }"),
        12
    );
    assert_eq!(run("fn main() -> i32 { let x := 5; return x.copy(); }"), 5);
}

#[test]
fn bool_element_copy_feeds_conditions() {
    assert_eq!(
        run("fn main() -> i32 { let a := [false, true]; let t := a[1].copy(); let f := a[0].copy(); if t { if f { 1 } else { 2 } } else { 3 } }"),
        2
    );
    assert_eq!(
        run("fn main() -> Bool { let a := [true, false]; let t := a[0].copy(); t && a[1] == false }"),
        1
    );
}

#[test]
fn copy_of_an_element_keeps_the_bounds_check() {
    let source = "fn main(n: u32) -> i32 { let a := [10, 20, 30]; a[n].copy() }";
    for (index, expected) in [(0, 10), (1, 20), (2, 30)] {
        assert_eq!(call(source, Some(wasmi::Val::I32(index))), Some(expected));
    }
    assert_eq!(call(source, Some(wasmi::Val::I32(3))), None);
    assert_eq!(call(source, Some(wasmi::Val::I32(-1))), None);
    let nested = "fn main(n: u32) -> i32 { let m := [[1, 2], [3, 4]]; m[1][n].copy() }";
    assert_eq!(call(nested, Some(wasmi::Val::I32(1))), Some(4));
    assert_eq!(call(nested, Some(wasmi::Val::I32(2))), None);
}
