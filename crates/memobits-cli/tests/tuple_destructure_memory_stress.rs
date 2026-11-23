//! Repeated multi-String tuple destructuring must release each iteration's
//! heap blocks so a Wasm run remains bounded by its declared memory maximum.
use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-tuple-memory-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, name: &str, text: &str) {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }

    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_mb"))
            .current_dir(&self.0)
            .args(args)
            .output()
            .unwrap()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn read_uleb(bytes: &[u8], cursor: &mut usize) -> u32 {
    let mut value = 0;
    let mut shift = 0;
    loop {
        let byte = bytes[*cursor];
        *cursor += 1;
        value |= u32::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return value;
        }
        shift += 7;
        assert!(shift < 35, "invalid Wasm LEB128");
    }
}

fn write_uleb(mut value: u32, output: &mut Vec<u8>) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        output.push(byte);
        if value == 0 {
            break;
        }
    }
}

/// Lower this test artifact's memory maximum while preserving every other
/// section. The extra page permits the first String blocks and then forces
/// repeated iterations to reuse released blocks.
fn cap_memory(bytes: &[u8]) -> (Vec<u8>, u32, u32) {
    assert_eq!(&bytes[..8], b"\0asm\x01\0\0\0");
    let mut module = bytes[..8].to_vec();
    let mut section_start = 8;
    let mut result = None;
    while section_start < bytes.len() {
        let id = bytes[section_start];
        let mut header_cursor = section_start + 1;
        let payload_len = read_uleb(bytes, &mut header_cursor) as usize;
        let payload_start = header_cursor;
        let section_end = payload_start + payload_len;
        assert!(section_end <= bytes.len(), "truncated Wasm section");
        if id != 5 {
            module.extend_from_slice(&bytes[section_start..section_end]);
        } else {
            assert!(result.is_none(), "unexpected second Wasm memory section");
            let mut cursor = payload_start;
            assert_eq!(read_uleb(bytes, &mut cursor), 1, "expected one memory");
            let limits = read_uleb(bytes, &mut cursor);
            assert_ne!(limits & 1, 0, "expected a declared maximum");
            let initial = read_uleb(bytes, &mut cursor);
            let maximum_start = cursor;
            let old_maximum = read_uleb(bytes, &mut cursor);
            let new_maximum = initial + 1;
            assert!(new_maximum <= old_maximum);

            let mut payload = bytes[payload_start..maximum_start].to_vec();
            // Replace only the maximum LEB, retaining any remaining memories.
            write_uleb(new_maximum, &mut payload);
            payload.extend_from_slice(&bytes[cursor..section_end]);
            module.push(id);
            write_uleb(payload.len() as u32, &mut module);
            module.extend_from_slice(&payload);
            result = Some((initial, new_maximum));
        }
        section_start = section_end;
    }
    let (initial, maximum) = result.expect("Wasm memory section");
    (module, initial, maximum)
}

#[test]
fn repeated_multi_string_tuple_destructuring_runs_within_wasm_memory_cap() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-memory-stress'\nentry='main::main'\n[build]\nstack_size=4096\n",
    );
    f.write(
        "src/main.mb",
        &format!(
            "fn main() -> u32 {{ var iteration: u32 = 0; var total: u32 = 0; loop {{ if iteration == {ITERATIONS} {{ break; }} let left := \"{text}\".concat(\"\"); let right := \"{text}\".concat(\"\"); let pair := ((iteration, iteration), (iteration, iteration), left, right); let ((a, b), (c, d), first, _) := pair; total += first.len() + a + b + c + d; iteration += 1; }} total }}"
        ),
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(167755776)\n");

    let build = f.run(&["build", "--output", "tuple-memory-stress.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm_path = f.0.join("tuple-memory-stress.wasm");
    let original = fs::read(&wasm_path).unwrap();
    let (capped, initial, maximum) = cap_memory(&original);
    fs::write(&wasm_path, capped).unwrap();
    let wasm = f.run(&["run", "tuple-memory-stress.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(167755776)\n");

    let bytes = fs::read(wasm_path).unwrap();
    let memory = wasmparser::Parser::new(0)
        .parse_all(&bytes)
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

#[test]
fn repeated_owned_string_tuple_temporaries_transfer_and_release_within_wasm_cap() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-temporary-memory-stress'\nentry='main::main'\n[build]\nstack_size=4096\n",
    );
    f.write(
        "src/main.mb",
        &format!(
            "fn consume(pair: (string, string)) -> u32 {{ let (left, right) := pair; left.len() + right.len() }} fn main() -> u32 {{ var iteration: u32 = 0; var total: u32 = 0; loop {{ if iteration == {ITERATIONS} {{ break; }} let left := \"{text}\".concat(\"\"); let right := \"{text}\".concat(\"\"); total += consume((left, right)); iteration += 1; }} total }}"
        ),
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(67108864)\n");

    let build = f.run(&["build", "--output", "tuple-temporary-memory-stress.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm_path = f.0.join("tuple-temporary-memory-stress.wasm");
    let original = fs::read(&wasm_path).unwrap();
    let (capped, initial, maximum) = cap_memory(&original);
    fs::write(&wasm_path, capped).unwrap();

    let wasm = f.run(&["run", "tuple-temporary-memory-stress.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(67108864)\n");
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(wasm_path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

#[test]
fn repeated_string_owning_tuple_enum_payloads_release_on_normal_and_early_exit() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-enum-memory-stress'\nentry='main::main'\n[build]\nstack_size=4096\n",
    );
    f.write(
        "src/main.mb",
        &format!(
            "type TextState [ Texts((string, string), u32), Empty ] fn package(pair: (string, string), count: u32) -> TextState {{ TextState::Texts(pair, count) }} fn consume(state: TextState) -> u32 {{ match state {{ TextState::Texts(pair, count) => {{ let (left, right) := pair; left.len() + right.len() + count }}, TextState::Empty => 0 }} }} fn early(state: TextState, flag: Bool) -> u32 {{ if flag {{ return 1; }} consume(state) }} fn main() -> u32 {{ var iteration: u32 = 0; var total: u32 = 0; loop {{ if iteration == {ITERATIONS} {{ break; }} let a := \"{text}\".concat(\"\"); let b := \"{text}\".concat(\"\"); total += early(package((a, b), iteration), true); let c := \"{text}\".concat(\"\"); let d := \"{text}\".concat(\"\"); let state := package((c, d), 0); total += consume(state); iteration += 1; }} total }}"
        ),
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(67117056)\n");

    let build = f.run(&["build", "--output", "tuple-enum-memory-stress.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let path = f.0.join("tuple-enum-memory-stress.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&path).unwrap());
    fs::write(&path, capped).unwrap();
    let wasm = f.run(&["run", "tuple-enum-memory-stress.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(67117056)\n");
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

#[test]
fn ignored_string_owning_enum_tuple_payloads_are_released_under_wasm_cap() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='ignored-enum-tuples-memory-stress'\nentry='main::main'\n[build]\nstack_size=4096\n",
    );
    f.write(
        "src/main.mb",
        &format!(
            "type TextState [ Texts((string, string), (string, string)), Empty ] fn discard(state: TextState) -> u32 {{ match state {{ TextState::Texts(pair, _) => {{ let (left, right) := pair; left.len() + right.len() }}, TextState::Empty => 0 }} }} fn main() -> u32 {{ var iteration: u32 = 0; var total: u32 = 0; loop {{ if iteration == {ITERATIONS} {{ break; }} let a := \"{text}\".concat(\"\"); let b := \"{text}\".concat(\"\"); let c := \"{text}\".concat(\"\"); let d := \"{text}\".concat(\"\"); total += discard(TextState::Texts((a, b), (c, d))); iteration += 1; }} total }}"
        ),
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(67108864)\n");

    let build = f.run(&["build", "--output", "ignored-enum-tuples.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let path = f.0.join("ignored-enum-tuples.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&path).unwrap());
    fs::write(&path, capped).unwrap();
    let wasm = f.run(&["run", "ignored-enum-tuples.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(67108864)\n");
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

#[test]
fn unused_string_result_payloads_are_released_under_wasm_cap() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='unused-result-string-memory-stress'\nentry='main::main'\n[build]\nstack_size=4096\n",
    );
    f.write(
        "src/main.mb",
        &format!(
            "fn make(text: string) -> Result<string, Error> {{ Ok(text) }} fn main() -> u32 {{ var iteration: u32 = 0; var total: u32 = 0; loop {{ if iteration == {ITERATIONS} {{ break; }} let result := make(\"{text}\".concat(\"\")); let used := match result {{ Ok(value) => 1 as u32, Err(_) => 0 as u32 }}; total += used; iteration += 1; }} total }}"
        ),
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(8192)\n");

    let build = f.run(&["build", "--output", "unused-result-string.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let path = f.0.join("unused-result-string.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&path).unwrap());
    fs::write(&path, capped).unwrap();
    let wasm = f.run(&["run", "unused-result-string.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(8192)\n");
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

#[test]
fn enum_arrays_with_nested_string_tuple_arrays_release_on_normal_and_early_returns_under_wasm_cap()
{
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='enum-nested-string-tuple-array-memory-stress'\nentry='main::main'\n[build]\nstack_size=4096\n",
    );
    f.write(
        "src/main.mb",
        &format!(
            "type Batch [ Rows(Array<(string, u32), 2>), Single((string, u32)), Text(string), Empty ] fn consume(states: Array<Batch, 3>, early: Bool) -> u32 {{ if early {{ return 1; }} 42 }} fn main() -> u32 {{ var iteration: u32 = 0; var total: u32 = 0; loop {{ if iteration == {ITERATIONS} {{ break; }} let a := \"{text}\".concat(\"\"); let b := \"{text}\".concat(\"\"); let c := \"{text}\".concat(\"\"); let d := \"{text}\".concat(\"\"); let first: (string, u32) = (a, 20); let second: (string, u32) = (b, 22); let third: (string, u32) = (c, 7); let rows: Array<(string, u32), 2> = [first, second]; let row_state: Batch = Batch::Rows(rows); let single_state: Batch = Batch::Single(third); let text_state: Batch = Batch::Text(d); let states: Array<Batch, 3> = [row_state, single_state, text_state]; total += consume(states, iteration % 2 == 0); iteration += 1; }} total }}"
        ),
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(176128)\n");

    let build = f.run(&["build", "--output", "enum-nested-string-tuple-array.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let path = f.0.join("enum-nested-string-tuple-array.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&path).unwrap());
    fs::write(&path, capped).unwrap();
    let wasm = f.run(&["run", "enum-nested-string-tuple-array.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(176128)\n");
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

#[test]
fn unused_heap_string_parameters_release_on_normal_and_early_returns_under_wasm_cap() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='unused-string-parameter-memory-stress'\nentry='main::main'\n[build]\nstack_size=4096\n",
    );
    f.write(
        "src/main.mb",
        &format!(
            "fn make_text() -> string {{ let text := \"{text}\".concat(\"\"); text }} fn discard(text: string, early: Bool) {{ if early {{ return; }} }} fn main() -> u32 {{ var iteration: u32 = 0; loop {{ if iteration == {ITERATIONS} {{ break; }} let text := make_text(); discard(text, iteration % 2 == 0); iteration += 1; }} iteration }}"
        ),
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(8192)\n");

    let build = f.run(&["build", "--output", "unused-string-parameter.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let path = f.0.join("unused-string-parameter.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&path).unwrap());
    fs::write(&path, capped).unwrap();
    let wasm = f.run(&["run", "unused-string-parameter.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(8192)\n");
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

#[test]
fn repeated_later_argument_returns_release_staged_tuple_temporaries_under_wasm_cap() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-temporary-early-memory-stress'\nentry='main::main'\n[build]\nstack_size=4096\n",
    );
    f.write(
        "src/main.mb",
        &format!(
            "fn never_called(pair: (string, string), later: u32) -> u32 {{ let (left, right) := pair; left.len() + right.len() + later }} fn return_during_later_argument() -> u32 {{ let left := \"{text}\".concat(\"\"); let right := \"{text}\".concat(\"\"); never_called((left, right), {{ return 1; 0 }}) }} fn main() -> u32 {{ var iteration: u32 = 0; var total: u32 = 0; loop {{ if iteration == {ITERATIONS} {{ break; }} total += return_during_later_argument(); iteration += 1; }} total }}"
        ),
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(8192)\n");

    let build = f.run(&["build", "--output", "tuple-temporary-early-stress.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm_path = f.0.join("tuple-temporary-early-stress.wasm");
    let original = fs::read(&wasm_path).unwrap();
    let (capped, initial, maximum) = cap_memory(&original);
    fs::write(&wasm_path, capped).unwrap();

    let wasm = f.run(&["run", "tuple-temporary-early-stress.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(8192)\n");
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(wasm_path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

#[test]
fn repeated_nested_string_tuple_calls_release_all_owners_under_wasm_cap() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='nested-tuple-memory-stress'\nentry='main::main'\n[build]\nstack_size=4096\n",
    );
    f.write(
        "src/main.mb",
        &format!(
            "fn forward(pair: ((string, string), u32)) -> ((string, string), u32) {{ pair }} fn consume(pair: ((string, string), u32)) -> u32 {{ let ((left, right), count) := pair; left.len() + right.len() + count }} fn main() -> u32 {{ var iteration: u32 = 0; var total: u32 = 0; loop {{ if iteration == {ITERATIONS} {{ break; }} let left := \"{text}\".concat(\"\"); let right := \"{text}\".concat(\"\"); let inner := (left, right); total += consume(forward((inner, 0))); iteration += 1; }} total }}"
        ),
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(67108864)\n");

    let build = f.run(&["build", "--output", "nested-tuple-memory-stress.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm_path = f.0.join("nested-tuple-memory-stress.wasm");
    let original = fs::read(&wasm_path).unwrap();
    let (capped, initial, maximum) = cap_memory(&original);
    fs::write(&wasm_path, capped).unwrap();

    let wasm = f.run(&["run", "nested-tuple-memory-stress.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(67108864)\n");
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(wasm_path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

#[test]
fn unused_nested_string_tuple_parameters_release_on_normal_and_early_returns() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='unused-tuple-parameter-memory-stress'\nentry='main::main'\n[build]\nstack_size=4096\n",
    );
    f.write(
        "src/main.mb",
        &format!(
            "fn discard(pair: ((string, string), u32), early: Bool) {{ if early {{ return; }} }} fn main() -> u32 {{ var iteration: u32 = 0; loop {{ if iteration == {ITERATIONS} {{ break; }} let left := \"{text}\".concat(\"\"); let right := \"{text}\".concat(\"\"); let inner := (left, right); discard((inner, iteration), iteration % 2 == 0); iteration += 1; }} iteration }}"
        ),
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(8192)\n");

    let build = f.run(&["build", "--output", "unused-tuple-parameter.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm_path = f.0.join("unused-tuple-parameter.wasm");
    let original = fs::read(&wasm_path).unwrap();
    let (capped, initial, maximum) = cap_memory(&original);
    fs::write(&wasm_path, capped).unwrap();

    let wasm = f.run(&["run", "unused-tuple-parameter.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(8192)\n");
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(wasm_path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

#[test]
fn nested_string_tuple_fields_in_local_records_release_under_wasm_cap() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-record-memory-stress'\nentry='main::main'\n[build]\nstack_size=4096\n",
    );
    f.write(
        "src/main.mb",
        &format!(
            "type TextRecord {{ values: (string, string), count: u32 }} fn main() -> u32 {{ var iteration: u32 = 0; var total: u32 = 0; loop {{ if iteration == {ITERATIONS} {{ break; }} let left := \"{text}\".concat(\"\"); let right := \"{text}\".concat(\"\"); let values := (left, right); let record := TextRecord {{ values: values, count: iteration }}; total += record.values.0.len() + record.values.1.len(); iteration += 1; }} total }}"
        ),
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(67108864)\n");

    let build = f.run(&["build", "--output", "tuple-record-memory-stress.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm_path = f.0.join("tuple-record-memory-stress.wasm");
    let original = fs::read(&wasm_path).unwrap();
    let (capped, initial, maximum) = cap_memory(&original);
    fs::write(&wasm_path, capped).unwrap();

    let wasm = f.run(&["run", "tuple-record-memory-stress.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(67108864)\n");
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(wasm_path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

#[test]
fn nested_literal_results_in_owned_aggregates_coexist_with_released_heap_strings_under_wasm_cap() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='nested-result-memory-stress'\nentry='main::main'\n[build]\nstack_size=4096\n",
    );
    f.write(
        "src/main.mb",
        &format!(
            "type Box {{ text: Result<string, Error>, n: u32 }} fn consume(items: Array<Result<string, Error>, 2>, early: Bool) -> u32 {{ if early {{ return 1; }} match items[1] {{ Ok(_) => 0 as u32, Err(error) => error.code }} }} fn main() -> u32 {{ var iteration: u32 = 0; var total: u32 = 0; loop {{ if iteration == {ITERATIONS} {{ break; }} let heap := \"{text}\".concat(\"\"); let first: Result<string, Error> = Ok(\"literal\"); let second: Result<string, Error> = Err(Error {{ code: 9 }}); let items := [first, second]; let third: Result<string, Error> = Ok(\"boxed\"); let boxed := Box {{ text: third, n: 1 }}; total += heap.len() + consume(items, iteration % 2 == 0) + boxed.n; iteration += 1; }} total }}"
        ),
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    // Per iteration: 4096 heap bytes, boxed.n = 1, and 1 (early) or 9 (normal).
    assert_eq!(source.stdout, b"Result: u32(33603584)\n");

    let build = f.run(&["build", "--output", "nested-result.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let path = f.0.join("nested-result.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&path).unwrap());
    fs::write(&path, capped).unwrap();
    let wasm = f.run(&["run", "nested-result.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(33603584)\n");
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}
