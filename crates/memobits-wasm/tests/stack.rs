//! The configured stack: frame limits, memory sizing, controlled exhaustion.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_ir::{FunctionId, Program};
use memobits_syntax::parse;
use memobits_wasm::{
    compile_application_traced, compile_with, CompileOptions, STACK_OVERFLOW_EXPORT,
};
use std::collections::BTreeMap;
use wasmi::{Engine, Linker, Module, Store};

fn lower(source: &str) -> Program {
    let parsed = parse(SourceId(0), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"))
}

fn build(source: &str, stack_size: u32) -> Result<Vec<u8>, Vec<memobits_diagnostics::Diagnostic>> {
    let program = lower(source);
    let main = program.functions.len() as u32 - 1;
    let exports = BTreeMap::from([("main".to_string(), FunctionId(main))]);
    compile_with(&program, &exports, &CompileOptions { stack_size })
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

fn run(source: &str, stack_size: u32) -> i32 {
    let bytes = build(source, stack_size).unwrap();
    let (mut store, instance) = instantiate(&bytes);
    instance
        .get_typed_func::<(), i32>(&store, "main")
        .unwrap()
        .call(&mut store, ())
        .unwrap()
}

const DEFAULT: u32 = 1024 * 1024;

#[test]
fn default_stack_holds_a_grid_and_a_quarter_megabyte_array() {
    // 100 x 100 i32 = 40 KB.
    let grid = "fn main() -> i32 { var g: Array<Array<i32, 100>, 100> = [[0; 100]; 100]; \
                g[99][99] = 7; g[99][99] + g[0][0] }";
    assert_eq!(run(grid, DEFAULT), 7);
    // 256 KiB local array (the repetition accumulator doubles it).
    let big =
        "fn main() -> i32 { var a: Array<i32, 65536> = [0; 65536]; a[65535] = 5; a[65535] + a[0] }";
    assert_eq!(run(big, DEFAULT), 5);
}

#[test]
fn two_mebibyte_array_needs_a_larger_stack() {
    let source = "fn main() -> i32 { let a: Array<i32, 524288> = [1; 524288]; a[524287] }";
    let errors = build(source, DEFAULT).unwrap_err();
    let message = &errors[0].message;
    assert!(message.contains("2097152 bytes"), "{message}");
    assert!(message.contains("configured stack size of 1048576 bytes"));
    assert!(message.contains("[build].stack_size"));
    assert_eq!(run(source, 4 * 1024 * 1024), 1);
}

#[test]
fn frame_equal_to_the_stack_fits_and_one_more_element_does_not() {
    let fits = "fn main() -> i32 { let a: Array<i32, 1000> = [3; 1000]; a[999] }";
    // 4000 bytes twice = 8000 -> aligned frame 8000.
    assert!(build(fits, 8000).is_ok());
    assert!(build(fits, 7984).is_err());
}

#[test]
fn memory_covers_reserved_space_and_stack_in_whole_pages() {
    let source = "fn main() -> i32 { let a := [1, 2]; a[0] }";
    for (stack, pages) in [(4096u32, 1u64), (65520, 1), (65536, 2), (1 << 20, 17)] {
        let bytes = build(source, stack).unwrap();
        let memory = wasmparser::Parser::new(0)
            .parse_all(&bytes)
            .find_map(|part| match part.unwrap() {
                wasmparser::Payload::MemorySection(reader) => reader.into_iter().next(),
                _ => None,
            })
            .unwrap()
            .unwrap();
        assert_eq!(memory.initial, pages, "stack {stack}");
        assert_eq!(memory.maximum, Some(pages));
    }
}

#[test]
fn outcome_cell_and_string_data_follow_the_stack_at_a_page_boundary() {
    let program = lower(r#"fn main() -> Result<u32, Error> { Ok("é".len()) }"#);
    let options = CompileOptions { stack_size: 65_520 };
    let artifact = compile_application_traced(&program, FunctionId(0), &options).unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    let (cell, size) = main.call(&mut store, ()).unwrap();
    assert_eq!(cell, 65_536);
    let literal = (cell + size) as usize;
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let data = memory.data(&store);
    assert_eq!(data.len(), 2 * 65_536);
    assert_eq!(
        u32::from_le_bytes(data[literal..literal + 4].try_into().unwrap()) as usize,
        literal + 8
    );
    assert_eq!(&data[literal + 4..literal + 8], &2u32.to_le_bytes());
    assert_eq!(&data[literal + 8..literal + 10], "é".as_bytes());
}

#[test]
fn static_regions_report_page_limit_failures_before_emission() {
    let stack_size = 65_535 * 65_536 - 16;
    let error = build(r#"fn main() -> u32 { "é".len() }"#, stack_size).unwrap_err();
    assert!(error[0]
        .message
        .contains("String literals exceed the supported Wasm memory size"));

    let program = lower("fn main() -> Result<u32, Error> { Ok(1) }");
    let error = compile_application_traced(&program, FunctionId(0), &CompileOptions { stack_size })
        .unwrap_err();
    assert!(error[0]
        .message
        .contains("application entry result exceeds the supported memory size"));
}

#[test]
fn invalid_stack_sizes_are_diagnostics() {
    let source = "fn main() -> i32 { let a := [1, 2]; a[0] }";
    for size in [0, 15, 4100, u32::MAX, u32::MAX - 15] {
        assert!(build(source, size).is_err(), "{size}");
    }
}

#[test]
fn deep_recursion_exhausts_the_stack_with_a_flag_and_leaves_fresh_runs_clean() {
    let source = "fn rec(n: i32) -> i32 { let a: Array<i32, 1024> = [n; 1024]; \
                  if n == 0 { 0 } else { rec(n - 1) + a[1023] } } \
                  fn main() -> i32 { rec(100000) }";
    let bytes = build(source, 64 * 1024).unwrap();
    let (mut store, instance) = instantiate(&bytes);
    let main = instance.get_typed_func::<(), i32>(&store, "main").unwrap();
    assert!(main.call(&mut store, ()).is_err());
    let flag = instance.get_global(&store, STACK_OVERFLOW_EXPORT).unwrap();
    assert_eq!(flag.get(&store).i32(), Some(1));
    // A fresh instance of the same module computes correctly and is unflagged.
    let shallow = "fn rec(n: i32) -> i32 { let a: Array<i32, 1024> = [n; 1024]; \
                   if n == 0 { 0 } else { rec(n - 1) + a[1023] } } \
                   fn main() -> i32 { rec(4) }";
    assert_eq!(run(shallow, 64 * 1024), 10);
    let (mut store, instance) = instantiate(&bytes);
    let flag = instance.get_global(&store, STACK_OVERFLOW_EXPORT).unwrap();
    assert_eq!(flag.get(&store).i32(), Some(0));
    let main = instance.get_typed_func::<(), i32>(&store, "main").unwrap();
    assert!(main.call(&mut store, ()).is_err());
    assert_eq!(flag.get(&store).i32(), Some(1));
}

#[test]
fn other_traps_do_not_set_the_overflow_flag() {
    let source = "fn main() -> i32 { let a := [1, 2]; let i := 5; a[i] }";
    let bytes = build(source, DEFAULT).unwrap();
    let (mut store, instance) = instantiate(&bytes);
    let main = instance.get_typed_func::<(), i32>(&store, "main").unwrap();
    assert!(main.call(&mut store, ()).is_err());
    let flag = instance.get_global(&store, STACK_OVERFLOW_EXPORT).unwrap();
    assert_eq!(flag.get(&store).i32(), Some(0));
}
