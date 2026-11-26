//! D2 phase 2b: flat String-owning nominal structs travel by value as internal
//! owned arguments (slice 1). Ownership, release and rejected neighbours.
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
            "memobits-owned-struct-{}-{}",
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

#[test]
fn owned_flat_string_struct_arguments_run_in_source_and_wasm() {
    let f = Fixture::new();
    project(
        &f,
        "owned-struct-args",
        r#"type Label { text: string, n: u32 }
fn take(label: Label) -> u32 { label.text.len() + label.n }
fn early(label: Label, flag: bool) -> u32 { if flag { return 1; } label.text.len() }
fn two(first: Label, second: Label) -> u32 { first.text.len() + second.text.len() }
fn main() -> u32 {
    let heap := "ab".concat("cd");
    let first := Label { text: heap, n: 3 };
    let a := take(first);
    let literal := Label { text: "lit", n: 1 };
    let b := take(literal);
    let heap_two := "xx".concat("y");
    let second := Label { text: heap_two, n: 0 };
    let c := early(second, true);
    let heap_three := "xx".concat("y");
    let third := Label { text: heap_three, n: 0 };
    let d := early(third, false);
    let left_heap := "l".concat("l");
    let left := Label { text: left_heap, n: 0 };
    let right_heap := "rrr".concat("r");
    let right := Label { text: right_heap, n: 0 };
    let e := two(left, right);
    a + b + c + d + e
}
"#,
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(21)\n");
    let wasm = build_wasm(&f, "owned-struct-args.wasm");
    let run = f.run(&["run", "owned-struct-args.wasm"]);
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(run.stdout, b"Result: i32(21)\n");
    let _ = wasm;
}

#[test]
fn repeated_owned_string_struct_arguments_release_on_normal_and_early_returns() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    project(
        &f,
        "owned-struct-memory-stress",
        &format!(
            r#"type Label {{ text: string, n: u32 }}
fn consume(label: Label, flag: bool) -> u32 {{
    let extra := "{text}".concat("");
    if flag {{ return 1; }}
    label.text.len() + label.n + extra.len() - extra.len()
}}
fn caller(flag: bool) -> u32 {{
    let heap := "{text}".concat("");
    let label := Label {{ text: heap, n: 1 }};
    if flag {{ return 7; }}
    consume(label, false)
}}
fn main() -> u32 {{
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {{
        if iteration == {ITERATIONS} {{ break; }}
        total += caller(true);
        total += caller(false);
        let heap := "{text}".concat("");
        let label := Label {{ text: heap, n: 0 }};
        total += consume(label, true);
        iteration += 1;
    }}
    total
}}
"#
        ),
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(33628160)\n");
    let wasm_path = build_wasm(&f, "owned-struct-memory-stress.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&wasm_path).unwrap());
    fs::write(&wasm_path, capped).unwrap();
    let wasm = f.run(&["run", "owned-struct-memory-stress.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(33628160)\n");
    assert_capped_memory(&wasm_path, initial, maximum);
}

#[test]
fn owned_string_struct_transport_keeps_neighbouring_shapes_rejected() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='owned-struct-negatives'\nentry='main::main'\n",
    );
    for (source, code, message) in [
        (
            r#"fn main() { let t := "a".concat("b"); let l := Label { text: t, n: 1 }; take(l); take(l); }"#,
            "BE001",
            "unavailable after a move",
        ),
        (
            r#"fn main() { let t := "a".concat("b"); let l := Label { text: t, n: 1 }; let s := l.text; }"#,
            "TE022",
            "cannot be moved out by field access",
        ),
        // Tuple elements are admitted in d2_owner_placement.rs (slice 3).
        // `k = l` (whole-owner reassignment) works since F4; see `f4_followups.rs`.
    ] {
        f.write(
            "src/main.mb",
            &format!(
                "type Label {{ text: string, n: u32 }}\nfn take(label: Label) -> u32 {{ label.text.len() }}\n{source}"
            ),
        );
        let output = f.run(&["build"]);
        assert_eq!(output.status.code(), Some(1), "{source}: {output:?}");
        let diagnostic = String::from_utf8(output.stderr).unwrap();
        assert!(diagnostic.contains(code), "{source}: {diagnostic}");
        assert!(diagnostic.contains(message), "{source}: {diagnostic}");
    }
}

#[test]
fn owned_string_struct_exported_signatures_and_plain_structs_are_unchanged() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='owned-struct-exports'\nentry='main::main'\n[export]\ncheck='main::check'\n",
    );
    f.write(
        "src/main.mb",
        "pub type Label { text: string, n: u32 }\nfn main() {}\npub fn check(l: Label) -> u32 { 1 }\n",
    );
    let output = f.run(&["build", "--lib"]);
    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stderr)
        .contains("exported signatures cannot take structs or struct references"));
    f.write(
        "src/main.mb",
        "pub type Label { text: string, n: u32 }\nfn main() {}\npub fn check() -> Label { Label { text: \"a\", n: 1 } }\n",
    );
    let output = f.run(&["build", "--lib"]);
    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stderr)
        .contains("exported signatures cannot return structs"));

    // A struct without String fields keeps its existing by-value behaviour.
    project(
        &f,
        "plain-struct",
        "type P { a: u32 }\nfn eat(p: P) -> u32 { p.a }\nfn main() -> u32 { let p := P { a: 42 }; eat(p) }\n",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(42)\n");
}

/// A moved struct local must be cleared at the call site: if the caller's
/// cleanup freed the block again, later allocations would alias and the run
/// would hang or corrupt the heap.
#[test]
fn moved_string_struct_locals_are_not_released_twice() {
    let f = Fixture::new();
    project(
        &f,
        "owned-struct-double-free",
        r#"type Label { text: string, n: u32 }
fn take(label: Label) -> u32 { label.text.len() }
fn main() -> u32 {
    var i: u32 = 0;
    var total: u32 = 0;
    loop {
        if i == 3 { break; }
        let t := "ab".concat("cd");
        let l := Label { text: t, n: 3 };
        let a := take(l);
        let p := "AAAA".concat("1");
        let q := "BBBB".concat("2");
        let r := "CCCC".concat("3");
        total += a + p.len() + q.len() + r.len();
        i += 1;
    }
    total
}
"#,
    );
    build_wasm(&f, "owned-struct-double-free.wasm");
    let mut child = Command::new(env!("CARGO_BIN_EXE_mb"))
        .current_dir(&f.0)
        .args(["run", "owned-struct-double-free.wasm"])
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    loop {
        if child.try_wait().unwrap().is_some() {
            break;
        }
        if std::time::Instant::now() > deadline {
            let _ = child.kill();
            panic!("run did not finish: the moved struct was likely released twice");
        }
        std::thread::sleep(std::time::Duration::from_millis(50));
    }
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"Result: i32(57)\n");
}

/// WP6 follow-up probe: a borrowed heap-payload enum that crosses a block
/// boundary (an `if`/`else` join, or a match inside a branch) must still be
/// rejected before extraction. Recorded result: the join form is caught early
/// by analysis (TE017); the in-branch forms are caught by the IR extraction
/// check (TE018).
#[test]
fn borrowed_heap_payload_enum_across_blocks_is_rejected_before_extraction() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='cross-block-probe'\nentry='main::main'\n",
    );
    for (body, code, message) in [
        (
            "fn f(e: borrow E, c: bool) -> u32 { let x := if c { e } else { e }; match x { E::S(s) => s.len(), E::N => 0 } }",
            "TE017",
            "reference-valued branch results are not supported",
        ),
        // An in-place match of a borrowed enum inside a branch is accepted since
        // E1a (the payload binds as a read-only reference); see e1_owned_elements.
        // `let x := e; match x { .. }` inside a branch is accepted since E1a
        // (in-place match, read-only payload reference); see e1_owned_elements.
    ] {
        f.write(
            "src/main.mb",
            &format!("type E [ S(string), N ]\n{body}\nfn main() {{}}\n"),
        );
        let output = f.run(&["build"]);
        assert_eq!(output.status.code(), Some(1), "{body}: {output:?}");
        let diagnostic = String::from_utf8(output.stderr).unwrap();
        assert!(diagnostic.contains(code), "{body}: {diagnostic}");
        assert!(diagnostic.contains(message), "{body}: {diagnostic}");
    }
}

const RESULT_HEADER: &str = "type Label { text: string, n: u32 }\nfn take(l: Label) -> u32 { l.n }\nfn make() -> Label { let l := Label { text: \"a\".concat(\"b\"), n: 1 }; l }\n";

#[test]
fn owned_flat_string_struct_results_run_in_source_and_wasm() {
    let f = Fixture::new();
    project(
        &f,
        "owned-struct-results",
        r#"type Label { text: string, n: u32 }
fn make(k: u32) -> Label {
    let t := "ab".concat("cd");
    let l := Label { text: t, n: k };
    l
}
fn take(l: Label) -> u32 { l.n }
fn lit() -> Label { let l := Label { text: "zz", n: 2 }; l }
fn early(flag: bool) -> Label {
    let t := "ab".concat("cd");
    let l := Label { text: t, n: 1 };
    if flag {
        let u := "q".concat("r");
        let m := Label { text: u, n: 9 };
        return m;
    }
    l
}
fn forward(k: u32) -> Label { let inner := make(k); inner }
fn main() -> u32 {
    let a := make(3);
    let b := lit();
    let c := early(true);
    let d := early(false);
    let e := forward(5);
    let unused := make(7);
    a.text.len() + a.n + b.text.len() + c.n + d.n + e.n + take(e)
}
"#,
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(29)\n");
    build_wasm(&f, "owned-struct-results.wasm");
    let run = f.run(&["run", "owned-struct-results.wasm"]);
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(run.stdout, b"Result: i32(29)\n");
}

#[test]
fn repeated_owned_string_struct_results_release_on_normal_and_early_returns() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    project(
        &f,
        "owned-struct-result-stress",
        &format!(
            r#"type Label {{ text: string, n: u32 }}
fn make(flag: bool) -> Label {{
    let scratch := "{text}".concat("");
    let heap := "{text}".concat("");
    let label := Label {{ text: heap, n: 1 }};
    if flag {{
        let other := "{text}".concat("");
        let early := Label {{ text: other, n: 2 }};
        return early;
    }}
    label
}}
fn use_result(flag: bool, bail: bool) -> u32 {{
    let label := make(flag);
    if bail {{ return 5; }}
    label.text.len() + label.n
}}
fn main() -> u32 {{
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {{
        if iteration == {ITERATIONS} {{ break; }}
        total += use_result(false, false);
        total += use_result(true, false);
        total += use_result(false, true);
        let dropped := make(true);
        iteration += 1;
    }}
    total
}}
"#
        ),
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(67174400)\n");
    let wasm_path = build_wasm(&f, "owned-struct-result-stress.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&wasm_path).unwrap());
    fs::write(&wasm_path, capped).unwrap();
    let wasm = f.run(&["run", "owned-struct-result-stress.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(67174400)\n");
    assert_capped_memory(&wasm_path, initial, maximum);
}

#[test]
fn owned_string_struct_results_keep_neighbouring_shapes_rejected() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='owned-struct-result-negatives'\nentry='main::main'\n",
    );
    for (source, code, message) in [
        (
            "fn main() { let n := make().text.len(); }",
            "TE017",
            "bind the struct to a local first",
        ),
        // `fn main() { make(); }` is accepted since F2: a discarded owner call
        // result is staged in a hidden local and released (see f2_payloads.rs).
        // `var x := make(); x = make();` is accepted since F4 (whole-owner
        // reassignment); see `f4_followups.rs`.
        // `fn forward() -> Label { make() }` is accepted since F1 (the call
        // result is staged in a hidden owner); see `f1_followups.rs`.
        (
            "fn view(l: borrow Label) -> Label { l } fn main() {}",
            "TE017",
            "reference values cannot escape",
        ),
    ] {
        f.write("src/main.mb", &format!("{RESULT_HEADER}{source}\n"));
        let output = f.run(&["build"]);
        assert_eq!(output.status.code(), Some(1), "{source}: {output:?}");
        let diagnostic = String::from_utf8(output.stderr).unwrap();
        assert!(diagnostic.contains(code), "{source}: {diagnostic}");
        assert!(diagnostic.contains(message), "{source}: {diagnostic}");
    }
}
