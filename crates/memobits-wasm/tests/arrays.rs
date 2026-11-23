//! Wasm execution of `let` arrays: literals, indexed reads, dynamic bounds traps,
//! frame layout and the frame-size cap.
use memobits_analysis::lower_module;
use memobits_diagnostics::{SourceId, Span};
use memobits_ir::{
    Access, ArrayInit, BinaryOp, Block, BlockId, CanonicalFunction, Constant, Function, FunctionId,
    Instruction, InstructionKind, LoanId, Local, LocalId, Operand, Primitive, Program, Signature,
    Source, Terminator, TerminatorKind, Type, UseMode, ValueId,
};
use memobits_syntax::parse;
use std::collections::BTreeMap;
use wasmi::{Engine, Linker, Module, Store};

fn lower(source: &str) -> Program {
    let parsed = parse(SourceId(0), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"))
}

fn exports(name: &str, function: u32) -> BTreeMap<String, FunctionId> {
    BTreeMap::from([(name.into(), FunctionId(function))])
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

fn run_main(source: &str) -> i32 {
    run_typed::<i32>(source)
}

fn run_typed<T: wasmi::WasmResults>(source: &str) -> T {
    let program = lower(source);
    let main = program.functions.len() as u32 - 1;
    let wasm = memobits_wasm::compile(&program, &exports("main", main)).unwrap();
    let (mut store, instance) = instantiate(&wasm);
    instance
        .get_typed_func::<(), T>(&store, "main")
        .unwrap()
        .call(&mut store, ())
        .unwrap()
}

#[test]
fn literal_and_indexed_reads_execute() {
    assert_eq!(
        run_main("fn main() -> i32 { let a := [1, 2, 3]; a[0] + a[2] }"),
        4
    );
    assert_eq!(
        run_main("fn main() -> i32 { let a := [1 + 1, 2 * 3]; a[1] - a[0] }"),
        4
    );
    assert_eq!(
        run_main("fn main() -> i32 { let a := [3, 1, 0]; let b := [7, 8]; b[a[1]] + 0 }"),
        8
    );
    assert_eq!(
        run_main("fn main() -> i32 { let a: array<i32, 0> = []; 5 }"),
        5
    );
}

#[test]
fn every_element_type_reads_back_with_sign_and_zero_extension() {
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
        ("f32", "[1.5, -2.25, 3.0]", "a[1] == -2.25"),
        ("f64", "[1.5, -2.25, 3.0]", "a[1] == -2.25"),
        ("Bool", "[false, true, false]", "a[1] == true"),
    ] {
        let source = format!(
            "fn main() -> bool {{ let a: array<{ty}, 3> = {elements}; {check} && a[2] == a[2] }}"
        );
        assert_eq!(run_main(&source), 1, "{ty}");
    }
}

#[test]
fn arrays_coexist_with_owner_cells_and_survive_recursion() {
    assert_eq!(
        run_typed::<i64>(
            "fn main() -> i64 { var x: i64 = 7; let a: array<u8, 3> = [1, 2, 3]; let b: array<i64, 2> = [100, 200]; let r := x.borrow(); if a[2] == 3 { b[1] + b[0] + r } else { 0 } }"
        ),
        307
    );
    assert_eq!(
        run_main(
            "fn f(n: i32) -> i32 { let a := [n + 0, 1]; if n == 0 { 0 } else { a[0] + a[1] + f(n - 1) } } fn main() -> i32 { f(3) }"
        ),
        9
    );
}

fn call_index(source: &str, name: &str, function: u32, argument: wasmi::Val) -> Option<i32> {
    let program = lower(source);
    let wasm = memobits_wasm::compile(&program, &exports(name, function)).unwrap();
    let (mut store, instance) = instantiate(&wasm);
    let func = instance.get_func(&store, name).unwrap();
    let mut out = [wasmi::Val::I32(0)];
    func.call(&mut store, &[argument], &mut out).ok()?;
    match out[0] {
        wasmi::Val::I32(value) => Some(value),
        _ => unreachable!(),
    }
}

#[test]
fn dynamic_indices_trap_outside_bounds_for_every_integer_width() {
    for ty in ["i8", "i16", "i32", "u8", "u16", "u32", "i64", "u64"] {
        let source = format!("fn get(n: {ty}) -> i32 {{ let a := [10, 20, 30]; a[n] + 0 }}");
        let wide = ty.ends_with("64");
        let value = |n: i64| {
            if wide {
                wasmi::Val::I64(n)
            } else {
                wasmi::Val::I32(n as i32)
            }
        };
        for (index, expected) in [(0, 10), (1, 20), (2, 30)] {
            assert_eq!(
                call_index(&source, "get", 0, value(index)),
                Some(expected),
                "{ty} {index}"
            );
        }
        assert_eq!(call_index(&source, "get", 0, value(3)), None, "{ty} 3");
        if !ty.starts_with('u') {
            assert_eq!(call_index(&source, "get", 0, value(-1)), None, "{ty} -1");
        }
    }
    // Extreme and wrapping values must not alias an in-range element.
    let i32_source = "fn get(n: i32) -> i32 { let a := [10, 20, 30]; a[n] + 0 }";
    for n in [i32::MIN, i32::MAX, -1] {
        assert_eq!(
            call_index(i32_source, "get", 0, wasmi::Val::I32(n)),
            None,
            "{n}"
        );
    }
    let u32_source = "fn get(n: u32) -> i32 { let a := [10, 20, 30]; a[n] + 0 }";
    assert_eq!(call_index(u32_source, "get", 0, wasmi::Val::I32(-1)), None);
    let i64_source = "fn get(n: i64) -> i32 { let a := [10, 20, 30]; a[n] + 0 }";
    for n in [1i64 << 32, (1i64 << 32) + 1, i64::MIN, i64::MAX, -1] {
        assert_eq!(
            call_index(i64_source, "get", 0, wasmi::Val::I64(n)),
            None,
            "{n}"
        );
    }
    let u64_source = "fn get(n: u64) -> i32 { let a := [10, 20, 30]; a[n] + 0 }";
    assert_eq!(
        call_index(u64_source, "get", 0, wasmi::Val::I64(1i64 << 32)),
        None
    );
    assert_eq!(call_index(u64_source, "get", 0, wasmi::Val::I64(-1)), None);
}

#[test]
fn zero_length_array_traps_on_any_index() {
    let source = "fn get(n: i32) -> i32 { let a: array<i32, 0> = []; a[n] + 0 }";
    assert_eq!(call_index(source, "get", 0, wasmi::Val::I32(0)), None);
}

#[test]
fn bounds_trap_happens_before_later_effects_and_inside_control_flow() {
    let source = "fn get(n: i32) -> i32 { let a := [1, 2]; if a[n] == 1 { 100 } else { 200 } }";
    assert_eq!(call_index(source, "get", 0, wasmi::Val::I32(0)), Some(100));
    assert_eq!(call_index(source, "get", 0, wasmi::Val::I32(1)), Some(200));
    assert_eq!(call_index(source, "get", 0, wasmi::Val::I32(2)), None);
}

#[test]
fn array_frames_are_capped_with_a_diagnostic() {
    // Repetition keeps these sources tiny. The hidden accumulator and the
    // binding each own a cell, so 65536 * 8 bytes twice is exactly the default
    // 1 MiB stack.
    assert_eq!(
        run_typed::<i64>(
            "fn main() -> i64 { let a: array<i64, 65536> = [0; 65536]; a[65535] + 1 }"
        ),
        1
    );
    // A literal is built directly in the binding's cell, so it occupies one cell.
    let literal = format!("[{}]", vec!["0"; 600].join(", "));
    assert_eq!(
        run_typed::<i64>(&format!(
            "fn main() -> i64 {{ let a: array<i64, 600> = {literal}; a[599] + 1 }}"
        )),
        1
    );
    for source in [
        "fn main() { let a: array<i64, 65537> = [0; 65537]; }",
        "fn main() { let a: array<i32, 300000> = [0; 300000]; }",
        "fn main() { let a: array<u8, 4000000000> = [0; 4000000000]; }",
        "fn main() { let a: array<f64, 4294967295> = [0.0; 4294967295]; }",
    ] {
        let program = lower(source);
        let errors = memobits_wasm::compile(&program, &exports("main", 0)).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("configured stack size")),
            "{source}: {errors:?}"
        );
    }
}

#[test]
fn repetition_evaluates_the_element_per_slot_in_order() {
    let next = "fn next(c: share i32) -> i32 { c += 1; c + 0 } ";
    assert_eq!(
        run_main(&format!(
            "{next}fn main() -> i32 {{ var n := 0; let a := [next(n.share()); 3]; a[0] * 100 + a[1] * 10 + a[2] + n * 1000 }}"
        )),
        3123
    );
    // A zero count never calls the element expression; a count of one calls it once.
    assert_eq!(
        run_main(&format!(
            "{next}fn main() -> i32 {{ var n := 0; let z: array<i32, 0> = [next(n.share()); 0]; let o := [next(n.share()); 1]; n * 10 + o[0] }}"
        )),
        11
    );
    // The loop also runs inside control flow and recursion.
    assert_eq!(
        run_main(&format!(
            "{next}fn f(d: i32) -> i32 {{ var n := d + 0; let a := [next(n.share()); 4]; if d == 0 {{ a[3] + 0 }} else {{ a[0] + f(d - 1) }} }} fn main() -> i32 {{ f(2) }}"
        )),
        3 + 2 + 4
    );
}

#[test]
fn repetition_of_every_element_type_and_large_counts() {
    for (ty, value, check) in [
        ("i8", "-5", "a[63] == -5 && a[0] == -5"),
        ("u8", "200", "a[63] == 200"),
        ("i16", "-300", "a[63] == -300"),
        ("u16", "60000", "a[63] == 60000"),
        ("i32", "-70000", "a[63] == -70000"),
        ("u32", "4000000000", "a[63] == 4000000000"),
        ("i64", "-5000000000", "a[63] == -5000000000"),
        ("u64", "5000000000", "a[63] == 5000000000"),
        ("f32", "1.5", "a[63] == 1.5"),
        ("f64", "-2.25", "a[63] == -2.25"),
        ("Bool", "true", "a[63] == true && a[1] == true"),
    ] {
        let source = format!(
            "fn main() -> bool {{ let a: array<{ty}, 64> = [{value}; 64]; {check} && a[2] == a[2] }}"
        );
        assert_eq!(run_main(&source), 1, "{ty}");
    }
    assert_eq!(
        run_main("fn main() -> i32 { let a := [3; 1000]; a[0] + a[999] + 0 }"),
        6
    );
    assert_eq!(
        run_main("fn main() -> i32 { let a := [0; 4096]; a[4095] + 1 }"),
        1
    );
}

#[test]
fn element_assignment_and_compound_assignment_execute() {
    assert_eq!(
        run_main("fn main() -> i32 { var a := [1, 2, 3]; a[1] = 10; a[0] + a[1] }"),
        11
    );
    assert_eq!(
        run_main(
            "fn main() -> i32 { var a := [1, 2, 3]; a[0] = a[1] + a[2]; a[0] *= 3; a[1] -= 1; a[2] /= 2; a[2] %= 5; a[0] * 100 + a[1] * 10 + a[2] }"
        ),
        1511
    );
    // `a[i] = a[j] + 1` reads before it writes, even with a dynamic index.
    assert_eq!(
        run_main(
            "fn main() -> i32 { var a := [5, 7, 9]; var i := 2; var j := 0; a[i] = a[j] + 1; a[i] + a[j] + a[1] }"
        ),
        6 + 5 + 7
    );
    assert_eq!(
        run_typed::<f64>("fn main() -> f64 { var a := [1.5, 2.5]; a[1] += 0.25; a[1] + 0.0 }"),
        2.75
    );
    assert_eq!(
        run_typed::<i64>(
            "fn main() -> i64 { var a: array<i64, 2> = [1, 2]; a[0] = 5000000000; a[1] += a[0]; a[1] + 0 }"
        ),
        5_000_000_002
    );
    // Narrow element writes do not clobber their neighbours.
    assert_eq!(
        run_main(
            "fn main() -> i32 { var a: array<u8, 4> = [1, 2, 3, 4]; a[1] = 255; a[2] += 7; if a[0] == 1 && a[1] == 255 && a[2] == 10 && a[3] == 4 { 1 } else { 0 } }"
        ),
        1
    );
}

#[test]
fn element_assignment_in_a_loop_fills_an_array() {
    assert_eq!(
        run_main(
            "fn main() -> i32 { var a := [0; 8]; var i := 0; loop { if i >= 8 { break; } a[i] = i * i; i += 1; } var s := 0; var j := 0; loop { if j >= 8 { break; } s += a[j]; j += 1; } s }"
        ),
        140
    );
}

#[test]
fn element_assignment_evaluates_index_before_right_hand_side() {
    let helpers = "fn idx(c: share i32) -> i32 { c += 1; c - 1 } fn rhs(c: share i32) -> i32 { c += 1; c * 10 } ";
    // Index first: idx() == 0 and rhs() == 20, so element 0 receives 20.
    assert_eq!(
        run_main(&format!(
            "{helpers}fn main() -> i32 {{ var n := 0; var a := [0, 0]; a[idx(n.share())] = rhs(n.share()); a[0] * 100 + a[1] }}"
        )),
        2000
    );
    assert_eq!(
        run_main(&format!(
            "{helpers}fn main() -> i32 {{ var n := 0; var a := [1, 1]; a[idx(n.share())] += rhs(n.share()); a[0] * 100 + a[1] }}"
        )),
        2101
    );
}

#[test]
fn element_writes_trap_outside_bounds() {
    let source = "fn put(n: i32) -> i32 { var a := [1, 2, 3]; a[n] = 9; a[0] + a[1] + a[2] }";
    assert_eq!(call_index(source, "put", 0, wasmi::Val::I32(2)), Some(12));
    assert_eq!(call_index(source, "put", 0, wasmi::Val::I32(3)), None);
    assert_eq!(call_index(source, "put", 0, wasmi::Val::I32(-1)), None);
    let compound = "fn put(n: i64) -> i32 { var a := [1, 2, 3]; a[n] += 9; a[0] + a[1] + a[2] }";
    assert_eq!(call_index(compound, "put", 0, wasmi::Val::I64(0)), Some(15));
    assert_eq!(
        call_index(compound, "put", 0, wasmi::Val::I64(1 << 32)),
        None
    );
    // A trapping write leaves no partial effect observable to the caller, and
    // the write after a successful one still traps.
    let late = "fn put(n: i32) -> i32 { var a := [0; 2]; a[0] = 1; a[n] = 2; 0 }";
    assert_eq!(call_index(late, "put", 0, wasmi::Val::I32(5)), None);
}

#[test]
fn whole_array_moves_copy_memory() {
    assert_eq!(
        run_main(
            "fn main() -> i32 { let a := [1, 2, 3]; let b := a; b[0] * 100 + b[1] * 10 + b[2] }"
        ),
        123
    );
    assert_eq!(
        run_main(
            "fn main() -> i32 { var a := [1, 2, 3]; var b := [4, 5, 6]; b = a; a = [7; 3]; a[0] = 8; b[2] * 100 + a[0] * 10 + a[2] }"
        ),
        387
    );
    // The destination is independent of the moved-from storage.
    assert_eq!(
        run_main(
            "fn main() -> i32 { var a := [1, 2]; var b := a; b[0] = 9; a = [5, 6]; b[0] * 100 + b[1] * 10 + a[0] }"
        ),
        900 + 20 + 5
    );
    // Self-referential construction reads old elements before writing new ones.
    assert_eq!(
        run_main(
            "fn main() -> i32 { var a := [1, 2, 3]; a = [a[1] + 0, a[2] + 0, a[0] + 0]; a[0] * 100 + a[1] * 10 + a[2] }"
        ),
        231
    );
    assert_eq!(
        run_main("fn main() -> i32 { var a := [1, 2]; a = a; a[0] * 10 + a[1] }"),
        12
    );
    assert_eq!(
        run_main(
            "fn main() -> i32 { var a := [1, 2]; var s := 0; var i := 0; loop { if i >= 3 { break; } a = [i + 10, i + 20]; s += a[0] + a[1]; i += 1; } s }"
        ),
        (10 + 20) + (11 + 21) + (12 + 22)
    );
}

fn span() -> Span {
    Span {
        source: SourceId(0),
        start: 0,
        end: 1,
    }
}

fn operand(source: Source, mode: UseMode) -> Operand {
    Operand {
        source,
        mode,
        span: Some(span()),
    }
}

fn instruction(output: Option<u32>, kind: InstructionKind) -> Instruction {
    Instruction {
        span: Some(span()),
        output: output.map(ValueId),
        kind,
    }
}

/// `fn name() -> i32` that creates an `Array<i32, len>` (literal of 9s or
/// zeroed), assigns it to a local and returns element `index`.
fn array_function(name: &str, len: u32, zeroed: bool, index: i32) -> Function {
    let array = Type::Array {
        element: Box::new(Type::Primitive(Primitive::I32)),
        len,
    };
    let i32_ty = Type::Primitive(Primitive::I32);
    let mut values = vec![array.clone(), i32_ty.clone()];
    let mut instructions = Vec::new();
    let init = if zeroed {
        ArrayInit::Zeroed
    } else {
        let mut elements = Vec::new();
        for _ in 0..len {
            let id = values.len() as u32;
            values.push(i32_ty.clone());
            instructions.push(instruction(
                Some(id),
                InstructionKind::Constant(Constant::Integer("9".into())),
            ));
            elements.push(operand(Source::Value(ValueId(id)), UseMode::Consume));
        }
        ArrayInit::Elements(elements)
    };
    instructions.push(instruction(Some(0), InstructionKind::ArrayNew { init }));
    instructions.push(instruction(
        None,
        InstructionKind::Assign {
            target: LocalId(0),
            value: operand(Source::Value(ValueId(0)), UseMode::Consume),
            initialize: true,
        },
    ));
    let index_value = values.len() as u32;
    values.push(i32_ty.clone());
    instructions.push(instruction(
        Some(index_value),
        InstructionKind::Constant(Constant::Integer(index.to_string())),
    ));
    let reference = values.len() as u32;
    values.push(Type::Reference {
        access: Access::Borrow,
        inner: Box::new(i32_ty.clone()),
    });
    instructions.push(instruction(
        Some(reference),
        InstructionKind::ElementAddr {
            loan: LoanId(0),
            base: operand(Source::Local(LocalId(0)), UseMode::Borrow),
            index: operand(Source::Value(ValueId(index_value)), UseMode::Read),
            access: Access::Borrow,
        },
    ));
    let loaded = values.len() as u32;
    values.push(i32_ty.clone());
    instructions.push(instruction(
        Some(loaded),
        InstructionKind::Load {
            reference: operand(Source::Value(ValueId(reference)), UseMode::Borrow),
        },
    ));
    let zero = values.len() as u32;
    values.push(i32_ty.clone());
    instructions.push(instruction(
        Some(zero),
        InstructionKind::Constant(Constant::Integer("0".into())),
    ));
    instructions.push(instruction(
        Some(1),
        InstructionKind::Binary {
            op: BinaryOp::Add,
            left: operand(Source::Value(ValueId(loaded)), UseMode::Read),
            right: operand(Source::Value(ValueId(zero)), UseMode::Read),
        },
    ));
    Function {
        path: CanonicalFunction {
            package: "test".into(),
            module: vec!["main".into()],
            name: name.into(),
        },
        span: span(),
        signature: Signature {
            parameters: vec![],
            result: Box::new(i32_ty),
        },
        parameter_locals: vec![],
        locals: vec![Local {
            name: "a".into(),
            ty: array,
            mutable: false,
            span: span(),
        }],
        values,
        blocks: vec![Block {
            parameters: vec![],
            instructions,
            terminator: Terminator {
                span: Some(span()),
                kind: TerminatorKind::Return(Some(operand(
                    Source::Value(ValueId(1)),
                    UseMode::Read,
                ))),
            },
        }],
        entry: BlockId(0),
    }
}

#[test]
fn zeroed_arrays_clear_dirty_frame_memory() {
    let program = Program {
        functions: vec![
            array_function("dirty", 4, false, 2),
            array_function("clean", 4, true, 2),
        ],
        ..Program::default()
    };
    let exports = BTreeMap::from([
        ("dirty".to_string(), FunctionId(0)),
        ("clean".to_string(), FunctionId(1)),
    ]);
    let wasm = memobits_wasm::compile(&program, &exports).unwrap();
    let (mut store, instance) = instantiate(&wasm);
    let dirty = instance.get_typed_func::<(), i32>(&store, "dirty").unwrap();
    let clean = instance.get_typed_func::<(), i32>(&store, "clean").unwrap();
    assert_eq!(dirty.call(&mut store, ()).unwrap(), 9);
    assert_eq!(clean.call(&mut store, ()).unwrap(), 0);
}

#[test]
fn oversized_or_overflowing_array_layouts_are_diagnostics() {
    for len in [262145, u32::MAX / 2, u32::MAX] {
        let program = Program {
            functions: vec![array_function("big", len, true, 0)],
            ..Program::default()
        };
        let errors = memobits_wasm::compile(&program, &exports("big", 0)).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("configured stack size")),
            "{len}: {errors:?}"
        );
    }
}

#[test]
fn fixed_iteration_preserves_order_and_control_flow() {
    assert_eq!(
        run_main(
            "fn make(calls: share i32) -> array<i32, 4> {
                calls += 1; [1, 2, 3, 4]
            }
            fn empty(calls: share i32) -> array<i32, 0> {
                calls += 1; []
            }
            fn select(items: share array<u8, 3>) -> u8 {
                loop value in items {
                    if value == 0 { continue; }
                    return value;
                }
                255
            }
            fn main() -> i32 {
                var calls := 0;
                var order := 0;
                loop value in make(calls.share()) {
                    if value == 2 { continue; }
                    loop { break; }
                    order = order * 10 + value;
                    if value == 3 { break; }
                }
                loop value in empty(calls.share()) { return -1; }
                var items: array<u8, 3> = [0, 7, 8];
                if select(items.share()) != 7 { return -2; }
                let items := [[4, 5], [6, 7]];
                var row := 0;
                loop items in items[{ row += 1; row }] {
                    order = order * 10 + items;
                }
                calls * 10000 + order + row
            }"
        ),
        21368
    );
}
