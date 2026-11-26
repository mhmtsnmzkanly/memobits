use memobits_analysis::lower_module;
use memobits_diagnostics::{SourceId, Span};
use memobits_ir::{
    Block, BlockId, CanonicalFunction, Constant, Edge, Function, FunctionId, Instruction,
    InstructionKind, Operand, Primitive, Program, Source, Terminator, TerminatorKind, Type,
    UseMode, ValueId,
};
use memobits_syntax::parse;
use std::collections::BTreeMap;
use wasmi::{Engine, Extern, Linker, Module, Store};

fn lower(source: &str) -> Program {
    let parsed = parse(SourceId(0), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    lower_module(&parsed.module, "test", &["main".into()]).unwrap()
}

fn exports(name: &str, function: u32) -> BTreeMap<String, FunctionId> {
    BTreeMap::from([(name.into(), FunctionId(function))])
}

fn instantiate(bytes: &[u8]) -> (Engine, Store<()>, wasmi::Instance) {
    let engine = Engine::default();
    let module = Module::new(&engine, bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Linker::new(&engine)
        .instantiate_and_start(&mut store, &module)
        .unwrap();
    (engine, store, instance)
}

#[test]
fn generated_constant_module_validates_and_executes() {
    let wasm =
        memobits_wasm::compile(&lower("fn main() -> i32 { 42 }"), &exports("main", 0)).unwrap();
    wasmparser::validate(&wasm).unwrap();
    let (engine, mut store, instance) = instantiate(&wasm);
    let result = instance
        .get_export(&store, "main")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(), i32>(&store)
        .unwrap()
        .call(&mut store, ())
        .unwrap();
    assert_eq!(result, 42);
    let _ = engine;
}

#[test]
fn generated_direct_calls_and_branch_dispatch_execute() {
    let calls = lower("fn id(value: i32) -> i32 { value } fn main() -> i32 { id(42) }");
    let wasm = memobits_wasm::compile(&calls, &exports("main", 1)).unwrap();
    wasmparser::validate(&wasm).unwrap();
    let (_engine, mut store, instance) = instantiate(&wasm);
    let result = instance
        .get_export(&store, "main")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(), i32>(&store)
        .unwrap()
        .call(&mut store, ())
        .unwrap();
    assert_eq!(result, 42);

    let branch = lower("fn main() -> i32 { if true { 17 } else { 22 } }");
    let wasm = memobits_wasm::compile(&branch, &exports("main", 0)).unwrap();
    wasmparser::validate(&wasm).unwrap();
    let (_engine, mut store, instance) = instantiate(&wasm);
    let result = instance
        .get_export(&store, "main")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(), i32>(&store)
        .unwrap()
        .call(&mut store, ())
        .unwrap();
    assert_eq!(result, 17);
}

#[test]
fn unit_calls_and_returns_use_no_external_wasm_result() {
    let program = lower("fn helper() {} fn main() { helper() }");
    let wasm = memobits_wasm::compile(&program, &exports("main", 1)).unwrap();
    wasmparser::validate(&wasm).unwrap();
    let (_engine, mut store, instance) = instantiate(&wasm);
    instance
        .get_export(&store, "main")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(), ()>(&store)
        .unwrap()
        .call(&mut store, ())
        .unwrap();
}

#[test]
fn unit_parameter_carrier_is_restricted_to_zero() {
    use memobits_ir::{
        Access, Block, CanonicalFunction, Function, Local, ParameterType, Signature, Terminator,
        TerminatorKind,
    };
    let span = Span {
        source: SourceId(0),
        start: 0,
        end: 1,
    };
    let unit_ty = Type::Primitive(Primitive::Unit);
    let program = Program {
        functions: vec![Function {
            path: CanonicalFunction {
                package: "test".into(),
                module: vec!["main".into()],
                name: "main".into(),
            },
            span,
            signature: Signature {
                parameters: vec![ParameterType {
                    access: Access::Owned,
                    ty: unit_ty.clone(),
                }],
                result: Box::new(unit_ty.clone()),
            },
            parameter_locals: vec![memobits_ir::LocalId(0)],
            locals: vec![Local {
                name: "unit".into(),
                ty: unit_ty,
                mutable: false,
                kind: memobits_ir::LocalKind::Ordinary,
                span,
            }],
            values: vec![],
            entry: BlockId(0),
            blocks: vec![Block {
                parameters: vec![],
                instructions: vec![],
                terminator: Terminator {
                    span: Some(span),
                    kind: TerminatorKind::Return(None),
                },
            }],
        }],
        ..Program::default()
    };
    let wasm = memobits_wasm::compile(&program, &exports("main", 0)).unwrap();
    let (_engine, mut store, instance) = instantiate(&wasm);
    let main = instance
        .get_export(&store, "main")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<i32, ()>(&store)
        .unwrap();
    main.call(&mut store, 0).unwrap();
    assert!(main.call(&mut store, 1).is_err());
}

fn call_i32_1(bytes: &[u8], name: &str, argument: i32) -> Result<i32, wasmi::Error> {
    let (_engine, mut store, instance) = instantiate(bytes);
    instance
        .get_export(&store, name)
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<i32, i32>(&store)
        .unwrap()
        .call(&mut store, argument)
}

fn call_i64_1(bytes: &[u8], name: &str, argument: i64) -> Result<i64, wasmi::Error> {
    let (_engine, mut store, instance) = instantiate(bytes);
    instance
        .get_export(&store, name)
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<i64, i64>(&store)
        .unwrap()
        .call(&mut store, argument)
}

fn call_i32_2(bytes: &[u8], name: &str, left: i32, right: i32) -> Result<i32, wasmi::Error> {
    let (_engine, mut store, instance) = instantiate(bytes);
    instance
        .get_export(&store, name)
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(i32, i32), i32>(&store)
        .unwrap()
        .call(&mut store, (left, right))
}

fn call_i64_2(bytes: &[u8], name: &str, left: i64, right: i64) -> Result<i64, wasmi::Error> {
    let (_engine, mut store, instance) = instantiate(bytes);
    instance
        .get_export(&store, name)
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(i64, i64), i64>(&store)
        .unwrap()
        .call(&mut store, (left, right))
}

#[test]
fn checked_arithmetic_traps_overflow_across_integer_widths() {
    for (ty, max) in [
        ("i8", i8::MAX as i128),
        ("i16", i16::MAX as i128),
        ("i32", i32::MAX as i128),
        ("i64", i64::MAX as i128),
    ] {
        let program = lower(&format!("fn add(x: {ty}) -> {ty} {{ x + 1 }}"));
        let wasm = memobits_wasm::compile(&program, &exports("add", 0)).unwrap();
        wasmparser::validate(&wasm).unwrap();
        let call = if ty == "i64" {
            call_i64_1(&wasm, "add", max as i64).is_err()
        } else {
            call_i32_1(&wasm, "add", max as i32).is_err()
        };
        assert!(call, "expected {ty} addition overflow to trap");
    }
    for (ty, max) in [
        ("u8", u8::MAX as u64),
        ("u16", u16::MAX as u64),
        ("u32", u32::MAX as u64),
        ("u64", u64::MAX),
    ] {
        let program = lower(&format!("fn add(x: {ty}) -> {ty} {{ x + 1 }}"));
        let wasm = memobits_wasm::compile(&program, &exports("add", 0)).unwrap();
        let call = if ty == "u64" {
            call_i64_1(&wasm, "add", max as i64).is_err()
        } else {
            call_i32_1(&wasm, "add", max as i32).is_err()
        };
        assert!(call, "expected {ty} addition overflow to trap");
    }
    for (ty, min, max) in [
        ("i8", i8::MIN as i64, i8::MAX as i64),
        ("i16", i16::MIN as i64, i16::MAX as i64),
        ("i32", i32::MIN as i64, i32::MAX as i64),
        ("i64", i64::MIN, i64::MAX),
    ] {
        let sub = lower(&format!("fn sub(a: {ty}, b: {ty}) -> {ty} {{ a - b }}"));
        let wasm = memobits_wasm::compile(&sub, &exports("sub", 0)).unwrap();
        let trapped = if ty == "i64" {
            call_i64_2(&wasm, "sub", min, 1).is_err()
        } else {
            call_i32_2(&wasm, "sub", min as i32, 1).is_err()
        };
        assert!(trapped, "expected {ty} subtraction underflow");

        let mul = lower(&format!("fn mul(a: {ty}, b: {ty}) -> {ty} {{ a * b }}"));
        let wasm = memobits_wasm::compile(&mul, &exports("mul", 0)).unwrap();
        let trapped = if ty == "i64" {
            call_i64_2(&wasm, "mul", max, 2).is_err() && call_i64_2(&wasm, "mul", min, -1).is_err()
        } else {
            call_i32_2(&wasm, "mul", max as i32, 2).is_err()
                && call_i32_2(&wasm, "mul", min as i32, -1).is_err()
        };
        assert!(trapped, "expected {ty} multiplication overflow");
    }
    for (ty, max) in [
        ("u8", u8::MAX as u64),
        ("u16", u16::MAX as u64),
        ("u32", u32::MAX as u64),
        ("u64", u64::MAX),
    ] {
        let mul = lower(&format!("fn mul(a: {ty}, b: {ty}) -> {ty} {{ a * b }}"));
        let wasm = memobits_wasm::compile(&mul, &exports("mul", 0)).unwrap();
        let trapped = if ty == "u64" {
            call_i64_2(&wasm, "mul", max as i64, 2).is_err()
                && call_i64_2(&wasm, "mul", 6, 7).unwrap() == 42
        } else {
            call_i32_2(&wasm, "mul", max as i32, 2).is_err()
                && call_i32_2(&wasm, "mul", 6, 7).unwrap() == 42
        };
        assert!(
            trapped,
            "expected {ty} multiplication overflow and valid multiplication"
        );
    }
}

#[test]
fn checked_mul_division_negation_and_remainder_cover_boundaries() {
    for (ty, min, max) in [
        ("i8", i8::MIN as i64, i8::MAX as i64),
        ("i16", i16::MIN as i64, i16::MAX as i64),
        ("i32", i32::MIN as i64, i32::MAX as i64),
        ("i64", i64::MIN, i64::MAX),
    ] {
        let neg = lower(&format!("fn neg(x: {ty}) -> {ty} {{ -x }}"));
        let wasm = memobits_wasm::compile(&neg, &exports("neg", 0)).unwrap();
        let negative_overflow = if ty == "i64" {
            call_i64_1(&wasm, "neg", min).is_err()
        } else {
            call_i32_1(&wasm, "neg", min as i32).is_err()
        };
        assert!(negative_overflow, "expected {ty} negation overflow");

        let div = lower(&format!("fn div(a: {ty}, b: {ty}) -> {ty} {{ a / b }}"));
        let wasm = memobits_wasm::compile(&div, &exports("div", 0)).unwrap();
        let store_setup = |a: i64, b: i64| {
            let (_engine, mut store, instance) = instantiate(&wasm);
            let function = instance
                .get_export(&store, "div")
                .and_then(Extern::into_func)
                .unwrap();
            if ty == "i64" {
                function
                    .typed::<(i64, i64), i64>(&store)
                    .unwrap()
                    .call(&mut store, (a, b))
                    .is_err()
            } else {
                function
                    .typed::<(i32, i32), i32>(&store)
                    .unwrap()
                    .call(&mut store, (a as i32, b as i32))
                    .is_err()
            }
        };
        assert!(store_setup(min, -1), "expected {ty} MIN / -1 to trap");
        assert!(store_setup(1, 0), "expected {ty} division by zero to trap");

        let rem = lower(&format!("fn rem(a: {ty}, b: {ty}) -> {ty} {{ a % b }}"));
        let wasm = memobits_wasm::compile(&rem, &exports("rem", 0)).unwrap();
        let result = if ty == "i64" {
            let (_engine, mut store, instance) = instantiate(&wasm);
            instance
                .get_export(&store, "rem")
                .and_then(Extern::into_func)
                .unwrap()
                .typed::<(i64, i64), i64>(&store)
                .unwrap()
                .call(&mut store, (min, -1))
                .unwrap()
        } else {
            let (_engine, mut store, instance) = instantiate(&wasm);
            instance
                .get_export(&store, "rem")
                .and_then(Extern::into_func)
                .unwrap()
                .typed::<(i32, i32), i32>(&store)
                .unwrap()
                .call(&mut store, (min as i32, -1))
                .unwrap() as i64
        };
        assert_eq!(result, 0, "signed {ty} remainder MIN % -1 is zero");
        let _ = max;
    }

    let u64_mul = lower("fn mul(a: u64, b: u64) -> u64 { a * b }");
    let wasm = memobits_wasm::compile(&u64_mul, &exports("mul", 0)).unwrap();
    let (_engine, mut store, instance) = instantiate(&wasm);
    let mul = instance
        .get_export(&store, "mul")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(i64, i64), i64>(&store)
        .unwrap();
    assert!(mul.call(&mut store, (u64::MAX as i64, 2)).is_err());
    assert_eq!(mul.call(&mut store, (6, 7)).unwrap(), 42);
}

#[test]
fn checked_primitive_remainder_preserves_value_and_zero_trap() {
    let rem = lower("fn rem(a: i32, b: i32) -> i32 { a % b }");
    let wasm = memobits_wasm::compile(&rem, &exports("rem", 0)).unwrap();
    let (_engine, mut store, instance) = instantiate(&wasm);
    let rem = instance
        .get_export(&store, "rem")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(i32, i32), i32>(&store)
        .unwrap();
    assert_eq!(rem.call(&mut store, (17, 5)).unwrap(), 2);
    assert!(rem.call(&mut store, (1, 0)).is_err());
}

#[test]
fn imported_scalar_inputs_and_float_comparisons_are_checked() {
    let narrow = lower("fn id(x: i8) -> i8 { x }");
    let wasm = memobits_wasm::compile(&narrow, &exports("id", 0)).unwrap();
    assert_eq!(call_i32_1(&wasm, "id", 100).unwrap(), 100);
    assert!(call_i32_1(&wasm, "id", 128).is_err());

    let bool_id = lower("fn id(x: bool) -> bool { x }");
    let wasm = memobits_wasm::compile(&bool_id, &exports("id", 0)).unwrap();
    assert!(call_i32_1(&wasm, "id", 2).is_err());

    for (ty, good, bad) in [
        ("i16", 32767, 32768),
        ("u8", 255, 256),
        ("u16", 65535, 65536),
    ] {
        let source = format!("fn id(x: {ty}) -> {ty} {{ x }}");
        let program = lower(&source);
        let wasm = memobits_wasm::compile(&program, &exports("id", 0)).unwrap();
        assert_eq!(call_i32_1(&wasm, "id", good).unwrap(), good);
        assert!(call_i32_1(&wasm, "id", bad).is_err());
    }

    let nan = lower("fn main() -> bool { (0.0 / 0.0) != (0.0 / 0.0) }");
    let wasm = memobits_wasm::compile(&nan, &exports("main", 0)).unwrap();
    let (_engine, mut store, instance) = instantiate(&wasm);
    let result = instance
        .get_export(&store, "main")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(), i32>(&store)
        .unwrap()
        .call(&mut store, ())
        .unwrap();
    assert_eq!(result, 1);
}

#[test]
fn numeric_literal_separators_are_removed_before_wasm_encoding() {
    let integer = lower("fn main() -> i32 { 1_000 }");
    let wasm = memobits_wasm::compile(&integer, &exports("main", 0)).unwrap();
    let (_engine, mut store, instance) = instantiate(&wasm);
    let int_result = instance
        .get_export(&store, "main")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(), i32>(&store)
        .unwrap()
        .call(&mut store, ())
        .unwrap();
    assert_eq!(int_result, 1_000);

    let float = lower("fn main() -> f64 { 1_000.5 }");
    let wasm = memobits_wasm::compile(&float, &exports("main", 0)).unwrap();
    let (_engine, mut store, instance) = instantiate(&wasm);
    let float_result = instance
        .get_export(&store, "main")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(), f64>(&store)
        .unwrap()
        .call(&mut store, ())
        .unwrap();
    assert_eq!(float_result, 1_000.5);
}

#[test]
fn indirect_calls_through_function_values_compile_and_exported_ones_are_rejected() {
    use memobits_ir::{
        Access, Block, CanonicalFunction, Function, Instruction, InstructionKind, Local, Operand,
        ParameterType, Signature, Terminator, TerminatorKind, Type, UseMode, ValueId,
    };
    let span = Span {
        source: SourceId(0),
        start: 0,
        end: 1,
    };
    let i32_ty = Type::Primitive(Primitive::I32);
    let callee_ty = Type::Function(Signature {
        parameters: vec![ParameterType {
            access: Access::Owned,
            ty: i32_ty.clone(),
        }],
        result: Box::new(i32_ty.clone()),
    });
    let program = Program {
        functions: vec![Function {
            path: CanonicalFunction {
                package: "test".into(),
                module: vec!["main".into()],
                name: "apply".into(),
            },
            span,
            signature: Signature {
                parameters: vec![
                    ParameterType {
                        access: Access::Owned,
                        ty: callee_ty.clone(),
                    },
                    ParameterType {
                        access: Access::Owned,
                        ty: i32_ty.clone(),
                    },
                ],
                result: Box::new(i32_ty.clone()),
            },
            parameter_locals: vec![memobits_ir::LocalId(0), memobits_ir::LocalId(1)],
            locals: vec![
                Local {
                    name: "f".into(),
                    ty: callee_ty,
                    mutable: false,
                    kind: memobits_ir::LocalKind::Ordinary,
                    span,
                },
                Local {
                    name: "x".into(),
                    ty: i32_ty.clone(),
                    mutable: false,
                    kind: memobits_ir::LocalKind::Ordinary,
                    span,
                },
            ],
            values: vec![i32_ty],
            entry: BlockId(0),
            blocks: vec![Block {
                parameters: vec![],
                instructions: vec![Instruction {
                    span: Some(span),
                    output: Some(ValueId(0)),
                    kind: InstructionKind::Call {
                        callee: Operand {
                            source: Source::Local(memobits_ir::LocalId(0)),
                            mode: UseMode::Read,
                            span: Some(span),
                        },
                        arguments: vec![Operand {
                            source: Source::Local(memobits_ir::LocalId(1)),
                            mode: UseMode::Consume,
                            span: Some(span),
                        }],
                    },
                }],
                terminator: Terminator {
                    span: Some(span),
                    kind: TerminatorKind::Return(Some(Operand {
                        source: Source::Value(ValueId(0)),
                        mode: UseMode::Consume,
                        span: Some(span),
                    })),
                },
            }],
        }],
        ..Program::default()
    };
    // Indirect calls are supported (H1); the unexported function is simply unreachable.
    memobits_wasm::compile(&program, &BTreeMap::new()).unwrap();
    // A function value in an exported signature has no external ABI.
    let exports = BTreeMap::from([("apply".to_owned(), memobits_ir::FunctionId(0))]);
    let errors = memobits_wasm::compile(&program, &exports).unwrap_err();
    assert!(errors.iter().any(|error| error.code.to_string() == "LE900"));
    assert!(errors.iter().any(|error| error.span == Some(span)));
}

fn sample_u64_pairs(boundaries: &[u64], seed: u64) -> Vec<(u64, u64)> {
    let mut pairs = Vec::new();
    for &left in boundaries {
        for &right in boundaries {
            pairs.push((left, right));
        }
    }
    let mut state = seed;
    for _ in 0..100 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let left = state;
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        pairs.push((left, state));
    }
    pairs
}

fn differential_i64(op: &str, calculate: fn(i64, i64) -> Option<i64>, seed: u64) {
    let program = lower(&format!("fn calc(a: i64, b: i64) -> i64 {{ a {op} b }}"));
    let wasm = memobits_wasm::compile(&program, &exports("calc", 0)).unwrap();
    wasmparser::validate(&wasm).unwrap();
    let (_engine, mut store, instance) = instantiate(&wasm);
    let calc = instance
        .get_export(&store, "calc")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(i64, i64), i64>(&store)
        .unwrap();
    let boundaries = [
        i64::MIN as u64,
        i64::MIN.wrapping_add(1) as u64,
        -(1i64 << 32) as u64,
        -(1i64 << 31) as u64,
        (-2i64) as u64,
        (-1i64) as u64,
        0,
        1,
        2,
        (1i64 << 31) as u64,
        (1i64 << 32) as u64,
        i64::MAX.wrapping_sub(1) as u64,
        i64::MAX as u64,
    ];
    for (a_bits, b_bits) in sample_u64_pairs(&boundaries, seed) {
        let (a, b) = (a_bits as i64, b_bits as i64);
        let expected = if op == "%" && a == i64::MIN && b == -1 {
            Some(0)
        } else {
            calculate(a, b)
        };
        match expected {
            Some(expected) => assert_eq!(
                calc.call(&mut store, (a, b)).unwrap(),
                expected,
                "i64 {a} {op} {b}"
            ),
            None => assert!(calc.call(&mut store, (a, b)).is_err(), "i64 {a} {op} {b}"),
        }
    }
}

fn differential_u64(op: &str, calculate: fn(u64, u64) -> Option<u64>, seed: u64) {
    let program = lower(&format!("fn calc(a: u64, b: u64) -> u64 {{ a {op} b }}"));
    let wasm = memobits_wasm::compile(&program, &exports("calc", 0)).unwrap();
    wasmparser::validate(&wasm).unwrap();
    let (_engine, mut store, instance) = instantiate(&wasm);
    let calc = instance
        .get_export(&store, "calc")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(i64, i64), i64>(&store)
        .unwrap();
    let boundaries = [
        0,
        1,
        2,
        u8::MAX as u64,
        u16::MAX as u64,
        u32::MAX as u64,
        (u32::MAX as u64) + 1,
        1u64 << 63,
        u64::MAX - 1,
        u64::MAX,
    ];
    for (a, b) in sample_u64_pairs(&boundaries, seed) {
        let expected = calculate(a, b).map(|value| value as i64);
        match expected {
            Some(expected) => assert_eq!(
                calc.call(&mut store, (a as i64, b as i64)).unwrap(),
                expected,
                "u64 {a} {op} {b}"
            ),
            None => assert!(
                calc.call(&mut store, (a as i64, b as i64)).is_err(),
                "u64 {a} {op} {b}"
            ),
        }
    }
}

fn differential_i32(op: &str, calculate: fn(i32, i32) -> Option<i32>, seed: u64) {
    let program = lower(&format!("fn calc(a: i32, b: i32) -> i32 {{ a {op} b }}"));
    let wasm = memobits_wasm::compile(&program, &exports("calc", 0)).unwrap();
    let (_engine, mut store, instance) = instantiate(&wasm);
    let calc = instance
        .get_export(&store, "calc")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(i32, i32), i32>(&store)
        .unwrap();
    let boundaries = [
        i32::MIN,
        i32::MIN + 1,
        -(1 << 16),
        -(1 << 8),
        -2,
        -1,
        0,
        1,
        2,
        1 << 8,
        1 << 16,
        i32::MAX - 1,
        i32::MAX,
    ];
    let pairs = sample_u64_pairs(&boundaries.map(|v| v as u32).map(u64::from), seed);
    for (a_bits, b_bits) in pairs {
        let (a, b) = (a_bits as u32 as i32, b_bits as u32 as i32);
        let expected = if op == "%" && a == i32::MIN && b == -1 {
            Some(0)
        } else {
            calculate(a, b)
        };
        match expected {
            Some(expected) => assert_eq!(calc.call(&mut store, (a, b)).unwrap(), expected),
            None => assert!(calc.call(&mut store, (a, b)).is_err(), "i32 {a} {op} {b}"),
        }
    }
}

fn differential_u32(op: &str, calculate: fn(u32, u32) -> Option<u32>, seed: u64) {
    let program = lower(&format!("fn calc(a: u32, b: u32) -> u32 {{ a {op} b }}"));
    let wasm = memobits_wasm::compile(&program, &exports("calc", 0)).unwrap();
    let (_engine, mut store, instance) = instantiate(&wasm);
    let calc = instance
        .get_export(&store, "calc")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(i32, i32), i32>(&store)
        .unwrap();
    let boundaries = [
        0,
        1,
        2,
        u8::MAX as u32,
        u16::MAX as u32,
        u32::MAX - 1,
        u32::MAX,
    ];
    let pairs = sample_u64_pairs(&boundaries.map(u64::from), seed);
    for (a_bits, b_bits) in pairs {
        let (a, b) = (a_bits as u32, b_bits as u32);
        match calculate(a, b).map(|value| value as i32) {
            Some(expected) => {
                assert_eq!(
                    calc.call(&mut store, (a as i32, b as i32)).unwrap(),
                    expected
                )
            }
            None => assert!(
                calc.call(&mut store, (a as i32, b as i32)).is_err(),
                "u32 {a} {op} {b}"
            ),
        }
    }
}

#[test]
fn checked_integer_wasm_matches_rust_checked_operations_at_boundaries_and_samples() {
    let signed_i64 = [
        ("+", i64::checked_add as fn(i64, i64) -> Option<i64>),
        ("-", i64::checked_sub),
        ("*", i64::checked_mul),
        ("/", i64::checked_div),
        ("%", i64::checked_rem),
    ];
    let unsigned_u64 = [
        ("+", u64::checked_add as fn(u64, u64) -> Option<u64>),
        ("-", u64::checked_sub),
        ("*", u64::checked_mul),
        ("/", u64::checked_div),
        ("%", u64::checked_rem),
    ];
    let signed_i32 = [
        ("+", i32::checked_add as fn(i32, i32) -> Option<i32>),
        ("-", i32::checked_sub),
        ("*", i32::checked_mul),
        ("/", i32::checked_div),
        ("%", i32::checked_rem),
    ];
    let unsigned_u32 = [
        ("+", u32::checked_add as fn(u32, u32) -> Option<u32>),
        ("-", u32::checked_sub),
        ("*", u32::checked_mul),
        ("/", u32::checked_div),
        ("%", u32::checked_rem),
    ];
    for (index, (op, calculate)) in signed_i64.into_iter().enumerate() {
        differential_i64(op, calculate, index as u64 + 1);
    }
    for (index, (op, calculate)) in unsigned_u64.into_iter().enumerate() {
        differential_u64(op, calculate, index as u64 + 11);
    }
    for (index, (op, calculate)) in signed_i32.into_iter().enumerate() {
        differential_i32(op, calculate, index as u64 + 21);
    }
    for (index, (op, calculate)) in unsigned_u32.into_iter().enumerate() {
        differential_u32(op, calculate, index as u64 + 31);
    }
}

#[test]
fn rejects_move_errors_before_emission() {
    let program = lower("fn main() { let x := [1]; let y := x; let z := x; }");
    let errors = memobits_wasm::compile(&program, &exports("main", 0)).unwrap_err();
    assert!(errors.iter().any(|error| error.code.to_string() == "BE001"));
}

#[test]
fn block_parameter_edges_stage_parallel_copies() {
    let i32_ty = Type::Primitive(Primitive::I32);
    let span = Span {
        source: SourceId(0),
        start: 0,
        end: 1,
    };
    let value_operand = |id| Operand {
        source: Source::Value(ValueId(id)),
        mode: UseMode::Consume,
        span: Some(span),
    };
    let function = Function {
        path: CanonicalFunction {
            package: "test".into(),
            module: vec!["main".into()],
            name: "main".into(),
        },
        span,
        signature: memobits_ir::Signature {
            parameters: vec![],
            result: Box::new(i32_ty.clone()),
        },
        parameter_locals: vec![],
        locals: vec![],
        values: vec![i32_ty.clone(), i32_ty.clone(), i32_ty.clone(), i32_ty],
        entry: BlockId(0),
        blocks: vec![
            Block {
                parameters: vec![],
                instructions: vec![
                    Instruction {
                        span: Some(span),
                        output: Some(ValueId(0)),
                        kind: InstructionKind::Constant(Constant::Integer("4".into())),
                    },
                    Instruction {
                        span: Some(span),
                        output: Some(ValueId(1)),
                        kind: InstructionKind::Constant(Constant::Integer("9".into())),
                    },
                ],
                terminator: Terminator {
                    span: Some(span),
                    kind: TerminatorKind::Goto(Edge {
                        target: BlockId(1),
                        arguments: vec![value_operand(1), value_operand(0)],
                    }),
                },
            },
            Block {
                parameters: vec![ValueId(2), ValueId(3)],
                instructions: vec![],
                terminator: Terminator {
                    span: Some(span),
                    kind: TerminatorKind::Return(Some(value_operand(2))),
                },
            },
        ],
    };
    let program = Program {
        functions: vec![function],
        ..Program::default()
    };
    let wasm = memobits_wasm::compile(&program, &exports("main", 0)).unwrap();
    wasmparser::validate(&wasm).unwrap();
    let (_engine, mut store, instance) = instantiate(&wasm);
    let result = instance
        .get_export(&store, "main")
        .and_then(Extern::into_func)
        .unwrap()
        .typed::<(), i32>(&store)
        .unwrap()
        .call(&mut store, ())
        .unwrap();
    assert_eq!(result, 9);
}

fn function_count(bytes: &[u8]) -> u32 {
    wasmparser::Parser::new(0)
        .parse_all(bytes)
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::FunctionSection(section) => Some(section.count()),
            _ => None,
        })
        .unwrap()
}

#[test]
fn library_selection_omits_same_module_main_and_unused_functions() {
    let program =
        lower("fn main() -> i32 { 99 } pub fn answer() -> i32 { 42 } fn unused() -> i32 { 7 }");
    let wasm = memobits_wasm::compile(&program, &exports("answer", 1)).unwrap();
    wasmparser::validate(&wasm).unwrap();
    assert_eq!(function_count(&wasm), 1);
    let (_, mut store, instance) = instantiate(&wasm);
    assert_eq!(
        instance
            .get_typed_func::<(), i32>(&store, "answer")
            .unwrap()
            .call(&mut store, ())
            .unwrap(),
        42
    );
}

#[test]
fn selection_remaps_transitive_recursive_calls_and_multiple_export_aliases() {
    let program = lower("fn unused() -> i32 { 99 } fn helper(n: i32) -> i32 { if n == 0 { 42 } else { helper(n - 1) } } fn main() -> i32 { 7 } pub fn answer() -> i32 { helper(2) }");
    let wasm = memobits_wasm::compile(
        &program,
        &BTreeMap::from([
            ("answer".into(), FunctionId(3)),
            ("alias".into(), FunctionId(3)),
        ]),
    )
    .unwrap();
    wasmparser::validate(&wasm).unwrap();
    assert_eq!(function_count(&wasm), 2);
    let (_, mut store, instance) = instantiate(&wasm);
    for name in ["answer", "alias"] {
        assert_eq!(
            instance
                .get_typed_func::<(), i32>(&store, name)
                .unwrap()
                .call(&mut store, ())
                .unwrap(),
            42
        );
    }
}

#[test]
fn no_export_roots_emit_no_function_bodies() {
    let wasm = memobits_wasm::compile(&lower("fn main() -> i32 { 42 }"), &BTreeMap::new()).unwrap();
    wasmparser::validate(&wasm).unwrap();
    assert_eq!(function_count(&wasm), 0);
}

#[test]
fn primitive_reference_widths_and_owner_cells_execute() {
    // Negative values exercise sign extension; large unsigned values exercise
    // zero extension. Every owner begins as a primitive parameter and is then
    // written through a reference forwarded via a local and a nested callee.
    for (ty, initial, replacement) in [
        ("i8", "1", "-117"),
        ("u8", "1", "251"),
        ("i16", "1", "-30001"),
        ("u16", "1", "65001"),
        ("i32", "1", "-2000000001"),
        ("u32", "1", "4000000001"),
        ("i64", "1", "-8000000000000000001"),
        ("u64", "1", "18000000000000000001"),
        ("f32", "1.0", "-12.5"),
        ("f64", "1.0", "-12345.25"),
        ("bool", "false", "true"),
    ] {
        let program = lower(&format!(
            "fn write(x: share {ty}) {{ x = {replacement}; }} fn relay(x: share {ty}) {{ write(x); }} fn run(var x: {ty}) -> bool {{ var r := x.share(); relay(r); x == {replacement} }} fn main() -> bool {{ run({initial}) }}"
        ));
        let wasm = memobits_wasm::compile(&program, &exports("main", 3)).unwrap();
        wasmparser::validate(&wasm).unwrap();
        let (_, mut store, instance) = instantiate(&wasm);
        let main = instance.get_typed_func::<(), i32>(&store, "main").unwrap();
        assert_eq!(main.call(&mut store, ()).unwrap(), 1, "{ty}");
    }
}

#[test]
fn references_reborrow_and_owner_assignments_remain_authoritative() {
    let program = lower("fn read(x: borrow i32) -> i32 { x + 0 } fn main() -> i32 { var x := 3; let r := x.borrow(); let first := read(r); x = 20; let second := read(x.borrow()); x += 2; first + second + x }");
    let wasm = memobits_wasm::compile(&program, &exports("main", 1)).unwrap();
    wasmparser::validate(&wasm).unwrap();
    let (_, mut store, instance) = instantiate(&wasm);
    assert_eq!(
        instance
            .get_typed_func::<(), i32>(&store, "main")
            .unwrap()
            .call(&mut store, ())
            .unwrap(),
        45
    );
}

#[test]
fn references_survive_nested_recursion_early_returns_and_repeated_calls() {
    let program = lower("fn read(x: borrow i32) -> i32 { x + 0 } fn recurse(x: share i32, n: i32) { var own := n + 0; read(own.borrow()); if n == 0 { x += 1; return; } recurse(x, n - 1); x += own; } fn main() -> i32 { var x := 10; recurse(x.share(), 4); x }");
    let wasm = memobits_wasm::compile(&program, &exports("main", 2)).unwrap();
    wasmparser::validate(&wasm).unwrap();
    let (_, mut store, instance) = instantiate(&wasm);
    let main = instance.get_typed_func::<(), i32>(&store, "main").unwrap();
    for _ in 0..5000 {
        assert_eq!(main.call(&mut store, ()).unwrap(), 21);
    }
}

#[test]
fn reference_reads_and_writes_execute_in_loops_and_short_circuit_control_flow() {
    let program = lower("fn bump(x: share i32) -> bool { x += 1; true } fn check(x: borrow bool) -> bool { false || x && true } fn main() -> i32 { var x := 0; var flag := true; loop { if check(flag.borrow()) && bump(x.share()) { if x == 3 { break; } } } false && bump(x.share()); true || bump(x.share()); x }");
    let wasm = memobits_wasm::compile(&program, &exports("main", 2)).unwrap();
    wasmparser::validate(&wasm).unwrap();
    let (_, mut store, instance) = instantiate(&wasm);
    assert_eq!(
        instance
            .get_typed_func::<(), i32>(&store, "main")
            .unwrap()
            .call(&mut store, ())
            .unwrap(),
        3
    );
}

#[test]
fn exported_reference_access_is_rejected_but_internal_access_is_supported() {
    let program = lower("fn read(x: borrow f64) -> f64 { x + 0.0 } fn main() -> f64 { let x := 2.5; read(x.borrow()) }");
    let errors = memobits_wasm::compile(&program, &exports("read", 0)).unwrap_err();
    assert!(
        errors.iter().any(
            |error| error.code.to_string() == "LE900" && error.message.contains("external ABI")
        ),
        "{errors:?}"
    );
    let wasm = memobits_wasm::compile(&program, &exports("main", 1)).unwrap();
    let (_, mut store, instance) = instantiate(&wasm);
    assert_eq!(
        instance
            .get_typed_func::<(), f64>(&store, "main")
            .unwrap()
            .call(&mut store, ())
            .unwrap(),
        2.5
    );
}

#[test]
fn wasm_rejects_live_reference_conflicts_before_encoding() {
    for source in [
        "fn main() { var x := 1; let r := x.borrow(); x = 2; r + 1; }",
        "fn main() { var x := 1; let a := x.borrow(); let b := x.share(); a + b; }",
    ] {
        assert!(memobits_wasm::compile(&lower(source), &exports("main", 0)).is_err());
    }
}

#[test]
fn checked_arithmetic_still_traps_after_reference_writes() {
    for ty in ["i8", "u8", "i16", "u16", "i32", "u32", "i64", "u64"] {
        let max = match ty {
            "i8" => "127",
            "u8" => "255",
            "i16" => "32767",
            "u16" => "65535",
            "i32" => "2147483647",
            "u32" => "4294967295",
            "i64" => "9223372036854775807",
            _ => "18446744073709551615",
        };
        for expression in ["x + 1", "{ var r := x.share(); r += 1; x }"] {
            let program = lower(&format!("fn set(x: share {ty}) {{ x = {max}; }} fn run(var x: {ty}) -> {ty} {{ set(x.share()); {expression} }} fn main() -> {ty} {{ run(0) }}"));
            let wasm = memobits_wasm::compile(&program, &exports("main", 2)).unwrap();
            let (_, mut store, instance) = instantiate(&wasm);
            let main = instance
                .get_export(&store, "main")
                .unwrap()
                .into_func()
                .unwrap();
            let mut outputs = [if ty.ends_with("64") {
                wasmi::Val::I64(0)
            } else {
                wasmi::Val::I32(0)
            }];
            assert!(
                main.call(&mut store, &[], &mut outputs).is_err(),
                "{ty}: {expression}"
            );
        }
    }
}

#[test]
fn address_taken_bool_parameters_feed_branch_edges_and_returns() {
    let program = lower("fn inspect(x: borrow bool) -> bool { !x } fn run(var flag: bool) -> bool { inspect(flag.borrow()); if flag { return flag; } else { flag } }");
    let wasm = memobits_wasm::compile(&program, &exports("run", 1)).unwrap();
    wasmparser::validate(&wasm).unwrap();
    let (_, mut store, instance) = instantiate(&wasm);
    let run = instance.get_typed_func::<i32, i32>(&store, "run").unwrap();
    assert_eq!(run.call(&mut store, 0).unwrap(), 0);
    assert_eq!(run.call(&mut store, 1).unwrap(), 1);
    assert!(run.call(&mut store, 2).is_err());
}

#[test]
fn owner_operand_snapshots_preserve_source_evaluation_order() {
    for (expression, expected) in [
        ("x + { set(x.share()); 0 }", 1),
        ("{ x += { set(x.share()); 2 }; x }", 3),
    ] {
        let program = lower(&format!("fn read(x: borrow i32) -> i32 {{ x + 0 }} fn set(x: share i32) {{ x = 20; }} fn main() -> i32 {{ var x := 1; read(x.borrow()); {expression} }}"));
        let wasm = memobits_wasm::compile(&program, &exports("main", 2)).unwrap();
        let (_, mut store, instance) = instantiate(&wasm);
        assert_eq!(
            instance
                .get_typed_func::<(), i32>(&store, "main")
                .unwrap()
                .call(&mut store, ())
                .unwrap(),
            expected,
            "{expression}"
        );
    }
}
