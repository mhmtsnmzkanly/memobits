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
fn list_pop_keeps_the_backing_block_when_empty() {
    let program = lower(
        r#"
        fn main() -> Result<Bool, Error> {
            var items: List<u32> = [];
            items.push(305_419_896);
            let removed := match items.pop() {
                Some(value) => value == 305_419_896, None => false
            };
            if removed && items.len() == 0 { Ok(true) } else { Err(Error { code: 1 }) }
        }
    "#,
    );
    let artifact = compile_application_traced(
        &program,
        FunctionId(0),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    for _ in 0..4 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        let data = memory.data(&store);
        assert_eq!(data[result as usize], 0);
        assert_eq!(data.len(), 65_536);
        assert_empty_backed_list(data, 305_419_896);
    }
}

#[test]
fn list_clear_retains_backing_storage_for_repeated_refills() {
    let program = lower(
        r#"
        fn main() -> Result<Bool, Error> {
            var items: List<u32> = [];
            items.push(305_419_896);
            var round: u32 = 0;
            loop {
                items.clear();
                if items.len() != 0 { return Err(Error { code: 1 }); }
                items.push(305_419_896);
                round += 1;
                if round == 1000 { break; }
            }
            items.clear();
            if items.len() == 0 { Ok(true) } else { Err(Error { code: 2 }) }
        }
    "#,
    );
    let artifact = compile_application_traced(
        &program,
        FunctionId(0),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    for _ in 0..4 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        let data = memory.data(&store);
        assert_eq!(data[result as usize], 0);
        assert_eq!(data.len(), 65_536);
        let marker = 305_419_896u32.to_le_bytes();
        let mut payloads = data[4096..].chunks_exact(4).filter(|word| *word == marker);
        assert_eq!(payloads.next(), Some(marker.as_slice()));
        assert_eq!(payloads.next(), None, "refills should use the same block");
        assert_empty_backed_list(data, 305_419_896);
    }
}

fn assert_empty_backed_list(data: &[u8], word: u32) {
    assert!(data[16..4096].windows(12).step_by(4).any(|descriptor| {
        let address = u32::from_le_bytes(descriptor[0..4].try_into().unwrap()) as usize;
        let length = u32::from_le_bytes(descriptor[4..8].try_into().unwrap());
        let block = u32::from_le_bytes(descriptor[8..12].try_into().unwrap()) as usize;
        length == 0
            && block >= 4096
            && block.checked_add(8) == Some(address)
            && data.get(address..address.saturating_add(4)) == Some(word.to_le_bytes().as_slice())
    }));
}

#[test]
fn list_push_grows_and_reuses_aligned_blocks_with_exact_contents() {
    let program = lower(
        r#"
        fn append(bytes: share List<u8>, words: share List<u32>, index: u32) {
            bytes.push(if index % 2 == 0 { 195 } else { 169 });
            words.push(305_419_896 + index);
        }
        fn main() -> Result<Bool, Error> {
            var bytes: List<u8> = [];
            var words: List<u32> = [];
            var index: u32 = 0;
            loop {
                if index % 2 == 0 {
                    append(bytes.share(), words.share(), index);
                } else {
                    var byte_handle := bytes.share();
                    var word_handle := words.share();
                    byte_handle.push(169);
                    word_handle.push(305_419_896 + index);
                }
                index += 1;
                if index == 12_000 { break; }
            }
            let moved := words;
            Ok(bytes.len() == 12_000 && moved.len() == 12_000)
        }
    "#,
    );
    let artifact = compile_application_traced(
        &program,
        FunctionId(1),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let engine = Engine::default();
    let module = Module::new(&engine, &artifact.bytes).unwrap();
    let mut limited = Store::new(
        &engine,
        wasmi::StoreLimitsBuilder::new().memory_size(65_536).build(),
    );
    limited.limiter(|limit| limit);
    let instance = Linker::new(&engine)
        .instantiate_and_start(&mut limited, &module)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&limited, "main")
        .unwrap();
    assert!(main.call(&mut limited, ()).is_err());
    let trap = instance
        .get_global(&limited, memobits_wasm::TRAP_EXPORT)
        .unwrap();
    assert_eq!(
        trap.get(&limited).i32().unwrap() & 255,
        i32::from(memobits_wasm::TrapReason::HeapAllocation.code())
    );

    let (mut store, instance) = instantiate(&artifact.bytes);
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let expected_bytes = [195, 169].repeat(6_000);
    let expected_words: Vec<u8> = (305_419_896u32..305_431_896)
        .flat_map(u32::to_le_bytes)
        .collect();
    let mut warmed_size = 0;
    for iteration in 0..6 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        let data = memory.data(&store);
        assert_eq!(data[result as usize], 0);
        for expected in [&expected_bytes, &expected_words] {
            assert!(data[16..4096].windows(12).step_by(4).any(|descriptor| {
                let address = u32::from_le_bytes(descriptor[0..4].try_into().unwrap()) as usize;
                let length = u32::from_le_bytes(descriptor[4..8].try_into().unwrap());
                let block = u32::from_le_bytes(descriptor[8..12].try_into().unwrap()) as usize;
                length == 12_000
                    && block >= 4096
                    && address == block + 8
                    && address.is_multiple_of(4)
                    && data.get(address..address + expected.len()) == Some(expected.as_slice())
            }));
        }
        if iteration == 1 {
            warmed_size = data.len();
        }
        if iteration >= 2 {
            assert_eq!(data.len(), warmed_size);
        }
    }
}
#[test]
fn list_replacement_reuses_blocks_after_empty_and_mixed_moves() {
    let program = lower(
        r#"
        fn fill() -> List<u32> {
            var items: List<u32> = [];
            loop {
                items.push(items.len());
                if items.len() == 8_000 { break; }
            }
            items
        }
        fn discard(items: List<u32>) {}
        fn refill(items: share List<u32>) { items = fill(); }
        fn clear(items: share List<u32>) { items = []; }
        fn main() -> Result<Bool, Error> {
            var items := fill();
            var step := 0;
            loop {
                if step % 2 == 0 { discard(items); }
                items = fill();
                items = items;
                refill(items.share());
                let tail := match items.get(7_999) { Some(value) => value == 7_999, None => false };
                if !tail { return Err(Error { code: 1 }); }
                if step % 2 == 0 {
                    clear(items.share());
                } else {
                    var handle := items.share();
                    handle = [];
                }
                if items.len() != 0 { return Err(Error { code: 2 }); }
                step += 1;
                if step == 4 { break; }
                items = fill();
            }
            Ok(true)
        }
    "#,
    );
    let artifact = compile_application_traced(
        &program,
        FunctionId(4),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    let mut settled = 0;
    for iteration in 0..5 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        let data = memory.data(&store);
        assert_eq!(data[result as usize], 0);
        if iteration == 1 {
            settled = data.len();
        }
        if iteration >= 2 {
            assert_eq!(data.len(), settled);
        }
    }
}

#[test]
fn owned_list_calls_and_returns_reuse_blocks_after_normal_exits() {
    let program = lower(
        r#"
        fn consume(items: List<u32>, early: Bool) -> Bool {
            if early { return items.len() == 12_000; }
            false
        }
        fn make() -> List<u32> {
            var items: List<u32> = [];
            loop {
                items.push(23);
                if items.len() == 12_000 { break; }
            }
            items
        }
        fn check(skip: Bool) -> Bool {
            let items := make();
            consume(items, { if skip { return true; } true })
        }
        fn main() -> Result<Bool, Error> {
            if check(false) && check(true) { Ok(true) } else { Err(Error { code: 1 }) }
        }
    "#,
    );
    let artifact = compile_application_traced(
        &program,
        FunctionId(3),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    let mut settled = 0;
    for iteration in 0..5 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        let data = memory.data(&store);
        assert_eq!(data[result as usize], 0);
        if iteration == 1 {
            settled = data.len();
        }
        if iteration >= 2 {
            assert_eq!(data.len(), settled);
        }
    }
}

#[test]
fn utf8_validation_keeps_fixed_memory_and_preserves_bytes() {
    let bytes = build(
        r#"
        fn main() -> i32 {
            let input: Bytes<3> = [195, 169, 255];
            let count := match input.validate_utf8(2) {
                Ok(count) => count,
                Err(_) => 0
            };
            let invalid := match input.validate_utf8(3) {
                Ok(_) => false,
                Err(error) => error.code == 2
            };
            if count == 1 && invalid && input[2] == 255 { 1 } else { 0 }
        }
        "#,
        4096,
    )
    .unwrap();
    let memory = wasmparser::Parser::new(0)
        .parse_all(&bytes)
        .find_map(|part| match part.unwrap() {
            wasmparser::Payload::MemorySection(reader) => reader.into_iter().next(),
            _ => None,
        })
        .unwrap()
        .unwrap();
    assert_eq!(memory.maximum, Some(memory.initial));
    let (mut store, instance) = instantiate(&bytes);
    let main = instance.get_typed_func::<(), i32>(&store, "main").unwrap();
    for _ in 0..8 {
        assert_eq!(main.call(&mut store, ()).unwrap(), 1);
    }
}

#[test]
fn utf8_construction_validates_before_growth_and_reuses_storage() {
    let program = lower(
        r#"
        fn valid() -> Result<Bool, Error> {
            let input: Bytes<32_000> = [65; 32_000];
            match input.to_utf8_string(32_000) {
                Ok(text) => { return Ok(text.len() == 32_000); },
                Err(_) => Err(Error { code: 1 })
            }
        }
        fn invalid() -> Result<Bool, Error> {
            var input: Bytes<32_000> = [65; 32_000];
            input[31_999] = 255;
            match input.to_utf8_string(32_000) {
                Ok(text) => Err(Error { code: 1 }),
                Err(error) => {
                    let Utf8Error { code, offset } := error;
                    let last := match offset { Some(index) => index == 31_999, None => false };
                    if code != 2 || !last { return Err(Error { code: 2 }); }
                    Ok(true)
                }
            }
        }
    "#,
    );
    let options = CompileOptions {
        stack_size: 120_000,
    };
    let valid = compile_application_traced(&program, FunctionId(0), &options).unwrap();
    let invalid = compile_application_traced(&program, FunctionId(1), &options).unwrap();
    for (artifact, should_trap) in [(&invalid, false), (&valid, true)] {
        let engine = Engine::default();
        let module = Module::new(&engine, &artifact.bytes).unwrap();
        let mut store = Store::new(
            &engine,
            wasmi::StoreLimitsBuilder::new()
                .memory_size(2 * 65_536)
                .build(),
        );
        store.limiter(|limit| limit);
        let instance = Linker::new(&engine)
            .instantiate_and_start(&mut store, &module)
            .unwrap();
        let main = instance
            .get_typed_func::<(), (i32, i32)>(&store, "main")
            .unwrap();
        let memory = instance
            .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
            .unwrap();
        if should_trap {
            assert!(main.call(&mut store, ()).is_err());
            let trap = instance
                .get_global(&store, memobits_wasm::TRAP_EXPORT)
                .unwrap();
            assert_eq!(
                trap.get(&store).i32().unwrap() & 255,
                i32::from(memobits_wasm::TrapReason::HeapAllocation.code())
            );
        } else {
            let (result, _) = main.call(&mut store, ()).unwrap();
            assert_eq!(memory.data(&store)[result as usize], 0);
        }
        assert_eq!(memory.data(&store).len(), 2 * 65_536);
    }

    let (mut store, instance) = instantiate(&valid.bytes);
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    for _ in 0..4 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        assert_eq!(memory.data(&store)[result as usize], 0);
        assert_eq!(memory.data(&store).len(), 3 * 65_536);
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
        literal + 12
    );
    assert_eq!(&data[literal + 4..literal + 8], &2u32.to_le_bytes());
    assert_eq!(&data[literal + 8..literal + 12], &0u32.to_le_bytes());
    assert_eq!(&data[literal + 12..literal + 14], "é".as_bytes());
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
fn owned_concat_reuses_memory_after_continue_break_and_return() {
    let left = "é".repeat(12_000);
    let right = "😀".repeat(6_000);
    let program = lower(&format!(
        r#"
        fn consume(early: Bool, value: String) -> u32 {{
            if early {{ return value.len(); }}
            let moved := value;
            moved.len()
        }}
        fn forward(value: String, early: Bool) -> u32 {{
            consume(early, value)
        }}
        fn make(left: borrow String, right: borrow String) -> String {{
            let result := left.concat(right);
            result
        }}
        fn measure(left: borrow String, right: borrow String, early: Bool) -> u32 {{
            var steps := 0;
            loop {{
                let joined := make(left, right);
                let len := if steps % 2 == 0 {{
                    forward(joined, {{
                        if early {{ return 48_000; }}
                        if steps == 2 {{ steps += 1; continue; }}
                        if steps == 4 {{ break; }}
                        false
                    }})
                }} else {{
                    joined.len()
                }};
                if early {{ return len; }}
                steps += 1;
                if steps <= 4 {{ continue; }}
                break;
            }}
            let joined := make(left, right);
            forward(joined, false)
        }}
        fn main() -> Result<u32, Error> {{
            let left := "{left}";
            let right := "{right}";
            Ok(measure(left.borrow(), right.borrow(), false)
                + measure(left.borrow(), right.borrow(), true))
        }}
    "#
    ));
    let options = CompileOptions { stack_size: 4096 };
    let artifact = compile_application_traced(&program, FunctionId(4), &options).unwrap();
    let engine = Engine::default();
    let module = Module::new(&engine, &artifact.bytes).unwrap();
    let linker = Linker::new(&engine);
    let mut limited = Store::new(
        &engine,
        wasmi::StoreLimitsBuilder::new().memory_size(65_536).build(),
    );
    limited.limiter(|limits| limits);
    let instance = linker.instantiate_and_start(&mut limited, &module).unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&limited, "main")
        .unwrap();
    assert!(main.call(&mut limited, ()).is_err());
    let trap = instance
        .get_global(&limited, memobits_wasm::TRAP_EXPORT)
        .unwrap();
    assert_eq!(
        trap.get(&limited).i32().unwrap() & 255,
        i32::from(memobits_wasm::TrapReason::HeapAllocation.code())
    );

    let (mut fresh, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&fresh, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&fresh, "main")
        .unwrap();
    let payload_offset = wasmparser::Parser::new(0)
        .parse_all(&artifact.bytes)
        .find_map(|part| match part.unwrap() {
            wasmparser::Payload::CustomSection(section)
                if section.name() == memobits_entry_abi::SECTION =>
            {
                Some(usize::from(
                    memobits_entry_abi::Metadata::decode(section.data())
                        .unwrap()
                        .payload_offset,
                ))
            }
            _ => None,
        })
        .unwrap();
    assert_eq!(memory.data(&fresh).len(), 65_536);
    for _ in 0..3 {
        let (address, _) = main.call(&mut fresh, ()).unwrap();
        let data = memory.data(&fresh);
        assert_eq!(data[address as usize], 0);
        let payload = address as usize + payload_offset;
        assert_eq!(&data[payload..payload + 4], &96_000u32.to_le_bytes());
        assert_eq!(data.len(), 2 * 65_536);
    }
}

#[test]
fn concat_reuses_a_non_head_block_without_losing_its_capacity() {
    let left = "é".repeat(12_000);
    let right = "😀".repeat(6_000);
    let program = lower(&format!(
        r#"
        fn main() -> Result<Bool, Error> {{
            let left := "{left}";
            let right := "{right}";
            {{
                let tiny := "".concat("x");
                let full := left.concat(right);
                if tiny.len() != 1 || full.len() != 48_000 {{ return Err(Error {{ code: 1 }}); }}
            }}
            // The tiny block is at the head. The larger block must remain
            // reusable at full size after satisfying this smaller request.
            {{
                let shorter := left.concat("");
                if shorter.len() != 24_000 {{ return Err(Error {{ code: 2 }}); }}
            }}
            let full := left.concat(right);
            if full.len() != 48_000 {{ return Err(Error {{ code: 3 }}); }}
            Ok(true)
        }}
    "#
    ));
    let artifact = compile_application_traced(
        &program,
        FunctionId(0),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    assert_eq!(memory.data(&store).len(), 65_536);
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    let (result, _) = main.call(&mut store, ()).unwrap();
    assert_eq!(memory.data(&store)[result as usize], 0);
    assert_eq!(memory.data(&store).len(), 2 * 65_536);
}

#[test]
fn temporary_string_arguments_reuse_blocks_after_call_and_early_exit() {
    let literal = "é".repeat(24_000);
    let program = lower(&format!(
        r#"
        fn make(seed: borrow String) -> String {{
            let result := seed.concat("");
            result
        }}
        fn read(text: borrow String, expected: u32) -> Bool {{
            text.len() == expected
        }}
        fn early(seed: borrow String) -> Bool {{
            read(make(seed).borrow(), {{ return true; 0 }})
        }}
        fn consume(text: String, expected: u32) -> Bool {{
            text.len() == expected
        }}
        fn early_owned(seed: borrow String) -> Bool {{
            consume(make(seed), {{ return true; 0 }})
        }}
        fn main() -> Result<Bool, Error> {{
            let seed := "{literal}";
            var step := 0;
            loop {{
                if !read(seed.concat("").borrow(), 48_000) || !early(seed.borrow())
                    || !read(make(seed.borrow()).borrow(), 48_000) {{
                    return Err(Error {{ code: 1 }});
                }}
                if !consume(seed.concat(""), 48_000) || !early_owned(seed.borrow())
                    || !consume(make(seed.borrow()), 48_000) {{
                    return Err(Error {{ code: 2 }});
                }}
                step += 1;
                if step == 8 {{ break; }}
            }}
            Ok(true)
        }}
        "#
    ));
    let artifact = compile_application_traced(
        &program,
        FunctionId(5),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    for _ in 0..3 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        assert_eq!(memory.data(&store)[result as usize], 0);
        assert_eq!(memory.data(&store).len(), 2 * 65_536);
    }
}

#[test]
fn immediate_string_reads_reuse_memory_after_read_and_early_exit() {
    let literal = "é".repeat(24_000);
    let program = lower(&format!(
        r#"
        fn make(seed: borrow String) -> String {{
            let result := seed.concat("");
            result
        }}
        fn early(seed: borrow String) -> Bool {{
            make(seed).byte_at({{ return true; 0 }});
            false
        }}
        fn main() -> Result<Bool, Error> {{
            let seed := "{literal}";
            var step := 0;
            loop {{
                if seed.concat("").len() != 48_000 || !early(seed.borrow()) {{
                    return Err(Error {{ code: 1 }});
                }}
                if !make(seed.borrow()).is_char_boundary(48_000) {{
                    return Err(Error {{ code: 2 }});
                }}
                step += 1;
                if step == 8 {{ break; }}
            }}
            Ok(true)
        }}
        "#
    ));
    let artifact = compile_application_traced(
        &program,
        FunctionId(2),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    for _ in 0..3 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        assert_eq!(memory.data(&store)[result as usize], 0);
        assert_eq!(memory.data(&store).len(), 2 * 65_536);
    }
}

#[test]
fn repeated_list_discard_reuses_storage_in_one_instance() {
    let program = lower(
        r#"
        fn make(count: u32) -> List<u32> {
            var result: List<u32> = [];
            loop {
                result.push(result.len());
                if result.len() == count { break; }
            }
            result
        }
        fn main() -> Result<Bool, Error> {
            var live: List<u32> = [];
            live.push(305_419_896);
            var repeats: u32 = 0;
            loop {
                make(10_000);
                repeats += 1;
                if repeats == 8 { break; }
            }
            match live.get(0) {
                Some(value) => if value == 305_419_896 { Ok(true) } else { Err(Error { code: 1 }) },
                None => Err(Error { code: 2 })
            }
        }
        "#,
    );
    let artifact = compile_application_traced(
        &program,
        FunctionId(1),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    let initial_size = memory.data(&store).len();
    let (result, _) = main.call(&mut store, ()).unwrap();
    assert_eq!(memory.data(&store)[result as usize], 0);
    let warmed_size = memory.data(&store).len();
    assert!(warmed_size > initial_size);
    assert!(warmed_size <= 3 * 65_536);
    for _ in 0..3 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        assert_eq!(memory.data(&store)[result as usize], 0);
        assert_eq!(memory.data(&store).len(), warmed_size);
    }
}

#[test]
fn temporary_list_reads_reuse_storage_across_normal_and_early_exits() {
    let program = lower(
        r#"
        fn make(count: u32) -> List<u32> {
            var result: List<u32> = [];
            loop {
                result.push(result.len());
                if result.len() == count { break; }
            }
            result
        }
        fn early_return() -> Bool {
            make(10_000).get({ return true; });
            false
        }
        fn main() -> Result<Bool, Error> {
            var live: List<u32> = [];
            live.push(305_419_896);
            var repeats: u32 = 0;
            loop {
                if make(10_000).len() != 10_000 || !early_return() {
                    return Err(Error { code: 3 });
                }
                match make(10_000).get(9_999) {
                    Some(value) => if value != 9_999 { return Err(Error { code: 4 }); },
                    None => return Err(Error { code: 5 })
                };
                repeats += 1;
                if repeats == 4 {
                    make(10_000).get({ break; });
                }
                make(10_000).get({ continue; });
            }
            match live.get(0) {
                Some(value) => if value == 305_419_896 { Ok(true) } else { Err(Error { code: 1 }) },
                None => Err(Error { code: 2 })
            }
        }
        "#,
    );
    let artifact = compile_application_traced(
        &program,
        FunctionId(2),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    let initial_size = memory.data(&store).len();
    let (result, _) = main.call(&mut store, ()).unwrap();
    assert_eq!(memory.data(&store)[result as usize], 0);
    let warmed_size = memory.data(&store).len();
    assert!(warmed_size > initial_size);
    assert!(warmed_size <= 3 * 65_536);
    for _ in 0..2 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        assert_eq!(memory.data(&store)[result as usize], 0);
        assert_eq!(memory.data(&store).len(), warmed_size);
    }
}

#[test]
fn temporary_list_arguments_reuse_storage_across_normal_and_early_exits() {
    let program = lower(
        r#"
        fn make(count: u32) -> List<u32> {
            var result: List<u32> = [];
            loop {
                result.push(result.len());
                if result.len() == count { break; }
            }
            result
        }
        fn inspect(items: borrow List<u32>, index: u32) -> Bool {
            match items.get(index) { Some(value) => value == index, None => false }
        }
        fn consume(items: List<u32>, index: u32) -> Bool {
            match items.get(index) { Some(value) => value == index, None => false }
        }
        fn early_return() -> Bool {
            consume(make(10_000), { return true; });
            false
        }
        fn early_borrow_return() -> Bool {
            inspect(make(10_000).borrow(), { return true; });
            false
        }
        fn check(owned: Bool, limit: u32) -> Result<Bool, Error> {
            var live: List<u32> = [];
            live.push(305_419_896);
            var repeats: u32 = 0;
            loop {
                if !inspect(make(10_000).borrow(), 9_999) || !early_borrow_return()
                    || !consume(make(10_000), 9_999) || !early_return() {
                    return Err(Error { code: 3 });
                }
                repeats += 1;
                if repeats == limit {
                    if owned { consume(make(10_000), { break; }); }
                    inspect(make(10_000).borrow(), { break; });
                }
                if owned { consume(make(10_000), { continue; }); }
                inspect(make(10_000).borrow(), { continue; });
            }
            match live.get(0) {
                Some(value) => if value == 305_419_896 { Ok(true) } else { Err(Error { code: 1 }) },
                None => Err(Error { code: 2 })
            }
        }
        fn main() -> Result<Bool, Error> {
            match check(false, 4) {
                Ok(value) => check(true, 4),
                Err(error) => Err(error)
            }
        }
        "#,
    );
    let artifact = compile_application_traced(
        &program,
        FunctionId(6),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    let initial_size = memory.data(&store).len();
    let (result, _) = main.call(&mut store, ()).unwrap();
    assert_eq!(memory.data(&store)[result as usize], 0);
    let warmed_size = memory.data(&store).len();
    assert!(warmed_size > initial_size);
    assert!(warmed_size <= 3 * 65_536);
    for _ in 0..2 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        assert_eq!(memory.data(&store)[result as usize], 0);
        assert_eq!(memory.data(&store).len(), warmed_size);
    }
}

#[test]
fn repeated_string_discard_reuses_one_block() {
    let literal = "é".repeat(24_000);
    let program = lower(&format!(
        r#"
        fn make(seed: borrow String) -> String {{
            let result := seed.concat("");
            result
        }}
        fn main() -> Result<Bool, Error> {{
            let seed := "{literal}";
            var step := 0;
            loop {{
                seed.concat("");
                make(seed.borrow());
                step += 1;
                if step == 8 {{ break; }}
            }}
            Ok(true)
        }}
        "#
    ));
    let artifact = compile_application_traced(
        &program,
        FunctionId(1),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    assert_eq!(memory.data(&store).len(), 65_536);
    for _ in 0..3 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        assert_eq!(memory.data(&store)[result as usize], 0);
        assert_eq!(memory.data(&store).len(), 2 * 65_536);
    }
}

#[test]
fn immediate_heap_result_matches_reuse_the_arm_allocation() {
    let literal = "é".repeat(24_000);
    let program = lower(&format!(
        r#"
        fn check(seed: borrow String, early: Bool) -> Bool {{
            let text := seed.concat("");
            let result: Result<String, Error> = Ok(text);
            match result {{
                Err(_) => false,
                Ok(value) => {{
                    if early {{ return value.len() == 48_000; }}
                    value.len() == 48_000
                }}
            }}
        }}
        fn make(seed: borrow String) -> Result<String, Error> {{
            let text := seed.concat("");
            Ok(text)
        }}
        fn check_return(seed: borrow String, early: Bool) -> Bool {{
            let result := make(seed);
            match result {{
                Ok(value) => {{
                    if early {{ return value.len() == 48_000; }}
                    value.len() == 48_000
                }},
                Err(_) => false
            }}
        }}
        fn main() -> Result<Bool, Error> {{
            let seed := "{literal}";
            var step := 0;
            loop {{
                if !check(seed.borrow(), step % 2 == 0)
                    || !check_return(seed.borrow(), step % 2 == 0) {{
                    return Err(Error {{ code: 1 }});
                }}
                step += 1;
                if step == 8 {{ break; }}
            }}
            Ok(true)
        }}
        "#
    ));
    let artifact = compile_application_traced(
        &program,
        FunctionId(3),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    for _ in 0..3 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        assert_eq!(memory.data(&store)[result as usize], 0);
        assert_eq!(memory.data(&store).len(), 2 * 65_536);
    }
}

#[test]
fn share_string_replacement_and_push_str_reuse_caller_blocks() {
    let literal = "é".repeat(24_000);
    let program = lower(&format!(
        r#"
        fn replace(text: share String, seed: borrow String) {{
            text = seed.concat("");
        }}
        fn inspect(text: share String) -> u32 {{ text.len() }}
        fn append_empty(text: share String) {{ text.push_str(""); }}
        fn main() -> Result<Bool, Error> {{
            let seed := "{literal}";
            var step := 0;
            loop {{
                var text := "";
                replace(text.share(), seed.borrow());
                if inspect(text.share()) != 48_000 {{ return Err(Error {{ code: 1 }}); }}
                replace(text.share(), seed.borrow());
                text.push_str("");
                append_empty(text.share());
                if text.len() != 48_000 {{ return Err(Error {{ code: 2 }}); }}
                step += 1;
                if step == 8 {{ break; }}
            }}
            Ok(true)
        }}
        "#
    ));
    let artifact = compile_application_traced(
        &program,
        FunctionId(3),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    for _ in 0..3 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        assert_eq!(memory.data(&store)[result as usize], 0);
        assert_eq!(memory.data(&store).len(), 3 * 65_536);
    }
}

#[test]
fn mutable_string_replacement_reuses_blocks_after_mixed_moves() {
    let literal = "é".repeat(24_000);
    let program = lower(&format!(
        r#"
        fn main() -> Result<Bool, Error> {{
            let seed := "{literal}";
            var text := seed.concat("");
            var step := 0;
            loop {{
                text = text.concat("");
                if step % 2 == 0 {{
                    let retired := text;
                    if retired.len() != 48_000 {{ return Err(Error {{ code: 1 }}); }}
                }}
                text = seed.concat("");
                if text.len() != 48_000 {{ return Err(Error {{ code: 2 }}); }}
                step += 1;
                if step == 6 {{ break; }}
            }}
            Ok(true)
        }}
        "#
    ));
    let artifact = compile_application_traced(
        &program,
        FunctionId(0),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    for _ in 0..3 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        assert_eq!(memory.data(&store)[result as usize], 0);
        assert_eq!(memory.data(&store).len(), 3 * 65_536);
    }
}

#[test]
fn concat_release_rejects_a_borrow_used_after_scope_exit() {
    use memobits_ir::InstructionKind;

    let mut program = lower(
        r#"fn main() -> u32 {
        let joined := "a".concat("é");
        let view := joined.borrow();
        view.len()
    }"#,
    );
    let instructions = &mut program.functions[0].blocks[0].instructions;
    let end = instructions.pop().unwrap();
    assert!(matches!(end.kind, InstructionKind::EndStringLocal { .. }));
    let read = instructions
        .iter()
        .position(|instruction| matches!(instruction.kind, InstructionKind::StringLen { .. }))
        .unwrap();
    instructions.insert(read, end);

    // The allocation order is still valid. The outstanding alias is what
    // makes this early release unsafe.
    assert!(program.validate().is_ok());
    let errors = compile_application_traced(&program, FunctionId(0), &CompileOptions::default())
        .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.code.to_string() == "BE005"
                && error.message.contains("end the scope")),
        "{errors:?}"
    );
}

#[test]
fn concat_ir_requires_cleanup_but_allows_non_lifo_release() {
    use memobits_ir::InstructionKind;

    let source = r#"fn main() -> u32 {
        let first := "a".concat("b");
        let second := first.concat("c");
        second.len()
    }"#;
    let mut missing = lower(source);
    let mut reversed = missing.clone();
    let instructions = &mut missing.functions[0].blocks[0].instructions;
    instructions.pop();
    assert!(missing.validate().unwrap_err().iter().any(|error| error
        .message
        .contains("return leaves a heap String local in scope")));

    let instructions = &mut reversed.functions[0].blocks[0].instructions;
    let ends: Vec<_> = instructions
        .iter()
        .enumerate()
        .filter_map(|(index, instruction)| {
            matches!(instruction.kind, InstructionKind::EndStringLocal { .. }).then_some(index)
        })
        .collect();
    assert_eq!(ends.len(), 2);
    instructions.swap(ends[0], ends[1]);
    reversed.validate().unwrap();
    let artifact =
        compile_application_traced(&reversed, FunctionId(0), &CompileOptions::default()).unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let main = instance.get_typed_func::<(), i32>(&store, "main").unwrap();
    assert_eq!(main.call(&mut store, ()).unwrap(), 3);
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

#[test]
fn list_iteration_reuses_temporary_storage_after_each_exit() {
    let program = lower(
        r#"
        fn make() -> List<u32> {
            var items: List<u32> = [];
            loop {
                items.push(items.len());
                if items.len() == 10_000 { break; }
            }
            items
        }
        fn run(exit: u32) -> u32 {
            var count: u32 = 0;
            loop value in make() {
                if value == 0 { continue; }
                if exit == 1 { break; }
                if exit == 2 { return value; }
                count += 1;
            }
            count
        }
        fn main() -> Result<Bool, Error> {
            if run(0) != 9999 || run(1) != 0 || run(2) != 1 {
                return Err(Error { code: 1 });
            }
            Ok(true)
        }
        "#,
    );
    let artifact = compile_application_traced(
        &program,
        FunctionId(2),
        &CompileOptions { stack_size: 4096 },
    )
    .unwrap();
    let (mut store, instance) = instantiate(&artifact.bytes);
    let memory = instance
        .get_memory(&store, memobits_entry_abi::MEMORY_EXPORT)
        .unwrap();
    let main = instance
        .get_typed_func::<(), (i32, i32)>(&store, "main")
        .unwrap();
    let (result, _) = main.call(&mut store, ()).unwrap();
    assert_eq!(memory.data(&store)[result as usize], 0);
    let warmed_size = memory.data(&store).len();
    assert!(warmed_size <= 3 * 65_536);
    for _ in 0..3 {
        let (result, _) = main.call(&mut store, ()).unwrap();
        assert_eq!(memory.data(&store)[result as usize], 0);
        assert_eq!(memory.data(&store).len(), warmed_size);
    }
}

#[test]
fn local_struct_strings_reuse_heap_on_lexical_exits() {
    let part = "a".repeat(12_000);
    let bytes = build(
        &format!(
            r#"
        type Label {{ first: String, number: u32, second: String, literal: String }}

        fn staged(part: borrow String, exit: Bool) -> u32 {{
            let first := part.concat("!");
            let second := part.concat("?");
            let label := Label {{
                second: second,
                first: first,
                number: {{ if exit {{ return 1; }} 7 }},
                literal: "é"
            }};
            return label.number;
        }}

        fn main() -> i32 {{
            let part := "{part}";
            var iteration := 0;
            loop {{
                let first := part.concat("!");
                let second := part.concat("?");
                let label := Label {{ second: second, first: first, literal: "é", number: 7 }};
                if iteration != 0 {{
                    let moved := label;
                    if moved.number != 7 || moved.literal.len() != 2 {{ return 0; }}
                    match moved.first.byte_at(12_000) {{
                        Some(byte) => {{ if byte != 33 {{ return 0; }} }},
                        None => {{ return 0; }}
                    }};
                    match moved.second.byte_at(12_000) {{
                        Some(byte) => {{ if byte != 63 {{ return 0; }} }},
                        None => {{ return 0; }}
                    }};
                    if iteration == 1 {{ iteration += 1; continue; }}
                }};
                iteration += 1;
                if iteration == 3 {{ break; }}
            }}
            if staged(part.borrow(), true) == 1 && staged(part.borrow(), false) == 7 {{
                1
            }} else {{ 0 }}
        }}
        "#
        ),
        4096,
    )
    .unwrap();
    wasmparser::validate(&bytes).unwrap();
    let engine = Engine::default();
    let module = Module::new(&engine, &bytes).unwrap();
    let mut store = Store::new(
        &engine,
        wasmi::StoreLimitsBuilder::new().memory_size(65_536).build(),
    );
    store.limiter(|limits| limits);
    let instance = Linker::new(&engine)
        .instantiate_and_start(&mut store, &module)
        .unwrap();
    let main = instance.get_typed_func::<(), i32>(&store, "main").unwrap();
    for _ in 0..16 {
        assert_eq!(main.call(&mut store, ()).unwrap(), 1);
    }
}

#[test]
fn string_field_replacement_reuses_blocks_without_overwriting_live_fields() {
    let part = "a".repeat(20_000);
    let bytes = build(
        &format!(
            r#"
        type Label {{ other: String, text: String }}
        fn byte_is(value: Option<u8>, expected: u8) -> Bool {{
            match value {{ Some(byte) => byte == expected, None => false }}
        }}
        fn main() -> i32 {{
            let part := "{part}";
            var label := Label {{ other: "é", text: "start" }};
            let other := label.other.borrow();
            var iteration := 0;
            loop {{
                let first := part.concat("!");
                if iteration != 0 && !byte_is(label.text.byte_at(20_000), 63) {{ return 0; }}
                label.text = first;
                let second := part.concat("?");
                if !byte_is(label.text.byte_at(20_000), 33) {{ return 0; }}
                label.text = second;
                iteration += 1;
                if iteration == 8 {{ break; }}
            }}
            if other.len() != 2 {{ return 0; }}
            let moved := label;
            if byte_is(moved.text.byte_at(20_000), 63) {{ 1 }} else {{ 0 }}
        }}
        "#
        ),
        4096,
    )
    .unwrap();

    wasmparser::validate(&bytes).unwrap();
    let engine = Engine::default();
    let module = Module::new(&engine, &bytes).unwrap();
    let mut store = Store::new(
        &engine,
        wasmi::StoreLimitsBuilder::new().memory_size(65_536).build(),
    );
    store.limiter(|limits| limits);
    let instance = Linker::new(&engine)
        .instantiate_and_start(&mut store, &module)
        .unwrap();
    let main = instance.get_typed_func::<(), i32>(&store, "main").unwrap();
    for _ in 0..16 {
        assert_eq!(main.call(&mut store, ()).unwrap(), 1);
    }
}

#[test]
fn temporary_string_field_replacements_reuse_memory_after_rhs_exits() {
    let part = "a".repeat(20_000);
    let bytes = build(
        &format!(
            r#"
        type Label {{ text: String, note: String }}
        fn join(left: borrow String, right: borrow String) -> String {{
            let result := left.concat(right);
            result
        }}
        fn byte_is(value: Option<u8>, expected: u8) -> Bool {{
            match value {{ Some(byte) => byte == expected, None => false }}
        }}
        fn early(part: borrow String) -> Bool {{
            var label := Label {{ text: "", note: "" }};
            label.text = part.concat("?");
            label.text = label.text.concat({{
                if label.text.len() == 20_001 {{
                    return byte_is(label.text.byte_at(20_000), 63);
                }}
                "!"
            }});
            false
        }}
        fn forward(value: String, unused: u32) -> String {{
            value
        }}
        fn early_call(part: borrow String) -> Bool {{
            var label := Label {{ text: "", note: "" }};
            label.text = part.concat("?");
            label.text = forward(part.concat("!"), {{
                if label.text.len() == 20_001 {{
                    return byte_is(label.text.byte_at(20_000), 63);
                }}
                0
            }});
            false
        }}
        fn main() -> i32 {{
            let part := "{part}";
            let question := "?";
            var iteration := 0;
            loop {{
                var label := Label {{ text: "", note: "é" }};
                let note := label.note.borrow();
                label.text = join(part.borrow(), question.borrow());
                label.text = label.text.concat({{
                    iteration += 1;
                    if iteration == 1 {{ continue; }}
                    if iteration == 5 {{ break; }}
                    "!"
                }});
                if label.text.len() != 20_002 || !byte_is(label.text.byte_at(20_000), 63)
                    || !byte_is(label.text.byte_at(20_001), 33) {{ return 0; }}
                label.text = join(part.borrow(), note);
                if note.len() != 2 || !byte_is(label.text.byte_at(20_001), 169) {{ return 0; }}
                label.text = "";
                if label.text.len() != 0 {{ return 0; }}
            }}
            if early(part.borrow()) && early_call(part.borrow()) {{ 1 }} else {{ 0 }}
        }}
        "#
        ),
        4096,
    )
    .unwrap();

    wasmparser::validate(&bytes).unwrap();
    let engine = Engine::default();
    let module = Module::new(&engine, &bytes).unwrap();
    let mut store = Store::new(
        &engine,
        wasmi::StoreLimitsBuilder::new().memory_size(65_536).build(),
    );
    store.limiter(|limits| limits);
    let instance = Linker::new(&engine)
        .instantiate_and_start(&mut store, &module)
        .unwrap();
    let main = instance.get_typed_func::<(), i32>(&store, "main").unwrap();
    for _ in 0..16 {
        assert_eq!(main.call(&mut store, ()).unwrap(), 1);
    }
}
