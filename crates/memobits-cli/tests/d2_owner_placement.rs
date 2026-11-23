//! D2 phase 2c slice 3: flat String-owning nominal structs as tuple elements
//! and fixed-array elements. Ownership, release and rejected neighbours.
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
            "memobits-owner-placement-{}-{}",
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

fn build_wasm(f: &Fixture, name: &str) -> PathBuf {
    let build = f.run(&["build", "--output", name]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    f.0.join(name)
}

fn assert_capped_memory(wasm_path: &PathBuf, initial: u32, maximum: u32) {
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

fn project(f: &Fixture, name: &str, source: &str) {
    f.write(
        "project.toml",
        &format!("[package]\nname='{name}'\nentry='main::main'\n[build]\nstack_size=4096\n"),
    );
    f.write("src/main.mb", source);
}

fn run_source_and_wasm(f: &Fixture, artifact: &str, source_out: &[u8], wasm_out: &[u8]) {
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, source_out);
    build_wasm(f, artifact);
    let wasm = f.run(&["run", artifact]);
    assert!(
        wasm.status.success(),
        "Wasm failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, wasm_out);
}

#[test]
fn flat_string_structs_work_as_tuple_and_array_elements() {
    let f = Fixture::new();
    project(
        &f,
        "owner-placement",
        r#"type Label { text: string, n: u32 }
fn label_len(l: borrow Label) -> u32 { l.text.len() + l.n }
fn row_len(row: borrow (Label, u32)) -> u32 { row.0.text.len() + row.0.n + row.1 }
fn sum(labels: array<Label, 2>) -> u32 {
    label_len(labels[0].borrow()) + label_len(labels[1].borrow())
}
fn early(labels: array<Label, 2>, flag: bool) -> u32 {
    if flag { return 1; }
    2
}
fn main() -> u32 {
    let first_heap := "ab".concat("cd");
    let first := Label { text: first_heap, n: 1 };
    let second_heap := "xyz".concat("");
    let second := Label { text: second_heap, n: 2 };
    let pair := [first, second];
    let borrowed := label_len(pair[0].borrow()) + label_len(pair[1].borrow());
    let literal := Label { text: "lit", n: 0 };
    let literal_row: (Label, u32) = (literal, 7);
    let literal_len := row_len(literal_row.borrow());
    let tuple_heap := "qr".concat("");
    let tuple_label := Label { text: tuple_heap, n: 3 };
    let heap_row: (Label, u32) = (tuple_label, 4);
    let heap_len := row_len(heap_row.borrow());
    let owned := sum(pair);
    let moved_heap := "m".concat("m");
    let moved := Label { text: moved_heap, n: 0 };
    let other_heap := "o".concat("o");
    let other := Label { text: other_heap, n: 0 };
    let dropped := [moved, other];
    let skipped := early(dropped, true);
    let kept_heap := "k".concat("k");
    let kept := Label { text: kept_heap, n: 0 };
    let kept_other := Label { text: "z", n: 0 };
    let consumed := early([kept, kept_other], false);
    let inner_heap := "nn".concat("");
    let inner := Label { text: inner_heap, n: 1 };
    let inner_other_heap := "pp".concat("");
    let inner_other := Label { text: inner_other_heap, n: 2 };
    let left := [inner];
    let right := [inner_other];
    let grid := [left, right];
    // Nested arrays of owners are built and released; reads stay one level deep.
    let grid_total: u32 = 8;
    borrowed + literal_len + heap_len + owned + skipped + consumed + grid_total
}
"#,
    );
    // 10 + 10 + 9 + 10 + 1 + 2 + 8
    run_source_and_wasm(
        &f,
        "owner-placement.wasm",
        b"Result: u32(50)\n",
        b"Result: i32(50)\n",
    );
}

#[test]
fn repeated_string_owner_elements_release_on_normal_and_early_returns() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    project(
        &f,
        "owner-placement-stress",
        &format!(
            r#"type Label {{ text: string, n: u32 }}
fn label_len(l: borrow Label) -> u32 {{ l.text.len() + l.n }}
fn row_len(row: borrow (Label, u32)) -> u32 {{ row.0.text.len() + row.0.n + row.1 }}
fn consume(labels: array<Label, 2>, flag: bool) -> u32 {{
    let extra := "{text}".concat("");
    if flag {{ return 1; }}
    label_len(labels[0].borrow()) + label_len(labels[1].borrow()) + extra.len() - extra.len()
}}
fn caller(flag: bool) -> u32 {{
    let first_heap := "{text}".concat("");
    let first := Label {{ text: first_heap, n: 1 }};
    let second_heap := "{text}".concat("");
    let second := Label {{ text: second_heap, n: 2 }};
    let labels := [first, second];
    if flag {{ return 7; }}
    consume(labels, false)
}}
fn tuple_caller(flag: bool) -> u32 {{
    let heap := "{text}".concat("");
    let label := Label {{ text: heap, n: 0 }};
    let row: (Label, u32) = (label, 3);
    if flag {{ return 5; }}
    row_len(row.borrow())
}}
fn nested_caller(flag: bool) -> u32 {{
    let heap := "{text}".concat("");
    let label := Label {{ text: heap, n: 0 }};
    let inner := [label];
    let grid := [inner];
    if flag {{ return 3; }}
    4
}}
fn make_label() -> Label {{
    let heap := "{text}".concat("");
    let label := Label {{ text: heap, n: 0 }};
    label
}}
fn tuple_temporary_caller(flag: bool) -> u32 {{
    let from_call: (Label, u32) = (make_label(), 1);
    let heap := "{text}".concat("");
    let inline: (Label, u32) = (Label {{ text: heap, n: 0 }}, 2);
    if flag {{ return 9; }}
    row_len(from_call.borrow()) + row_len(inline.borrow())
}}
fn main() -> u32 {{
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {{
        if iteration == {ITERATIONS} {{ break; }}
        total += caller(true);
        total += caller(false);
        total += tuple_caller(true);
        total += tuple_caller(false);
        total += tuple_temporary_caller(true);
        total += tuple_temporary_caller(false);
        total += nested_caller(true);
        total += nested_caller(false);
        let heap := "{text}".concat("");
        let label := Label {{ text: heap, n: 0 }};
        let other := Label {{ text: "lit", n: 0 }};
        total += consume([label, other], true);
        iteration += 1;
    }}
    total
}}
"#
        ),
    );
    // Per iteration: 7 + 8195 + 5 + 4099 + 9 + 8195 + 3 + 4 + 1 = 20518.
    let expected = 20_518u32 * ITERATIONS;
    run_source_and_wasm(
        &f,
        "owner-placement-stress.wasm",
        format!("Result: u32({expected})\n").as_bytes(),
        format!("Result: i32({expected})\n").as_bytes(),
    );
    let wasm_path = f.0.join("owner-placement-stress.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&wasm_path).unwrap());
    fs::write(&wasm_path, capped).unwrap();
    let wasm = f.run(&["run", "owner-placement-stress.wasm"]);
    assert!(
        wasm.status.success(),
        "capped Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, format!("Result: i32({expected})\n").as_bytes());
    assert_capped_memory(&wasm_path, initial, maximum);
}

#[test]
fn string_owner_placements_keep_neighbouring_shapes_rejected() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='owner-placement-negatives'\nentry='main::main'\n",
    );
    let bind = r#"type Label { text: string, n: u32 }
fn take(p: (Label, u32)) {}
fn make() { let t := "a".concat("b"); let l := Label { text: t, n: 1 };"#;
    for (source, code, message) in [
        // Repeat form copies the owner.
        (
            &format!("{bind} let a := [l; 3]; }} fn main() {{}}"),
            "TE018",
            "can only move directly into a new local",
        ),
        // Element move-out (no implicit partial moves).
        (
            &format!("{bind} let a := [l]; let m := a[0]; }} fn main() {{}}"),
            "TE022",
            "cannot be moved out by indexing",
        ),
        (
            &format!("{bind} let p: (Label, u32) = (l, 1); let m := p.0; }} fn main() {{}}"),
            "TE022",
            "cannot be moved out by field access",
        ),
        (
            &format!("{bind} let p: (Label, u32) = (l, 1); let (m, k) := p; }} fn main() {{}}"),
            "TE017",
            "tuple destructuring cannot move nested String-owning aggregates",
        ),
        // Tuples holding an owner are not yet transported or nested.
        (
            &format!("{bind} let p: (Label, u32) = (l, 1); take(p); }} fn main() {{}}"),
            "TE017",
            "owned tuple calls cannot transport nested String-owning aggregates",
        ),
        (
            &format!("{bind} let p: (Label, u32) = (l, 1); let q: ((Label, u32), u32) = (p, 2); }} fn main() {{}}"),
            "TE018",
            "can only move directly into a new local",
        ),
    ] {
        f.write("src/main.mb", source);
        let output = f.run(&["build"]);
        assert_eq!(output.status.code(), Some(1), "{source}: {output:?}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains(code), "{source}: {stderr}");
        assert!(stderr.contains(message), "{source}: {stderr}");
    }
}
