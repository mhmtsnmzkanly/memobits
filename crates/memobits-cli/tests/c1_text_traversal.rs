//! C1 acceptance tests: `loop ch in text` scalar traversal over `string`
//! receivers (source and standalone Wasm), loan and binding negatives, and the
//! MW003 spelling migration warnings.
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
            "memobits-c1-text-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn project(&self, source: &str) {
        self.project_with("", source);
    }

    fn project_with(&self, build: &str, source: &str) {
        self.write(
            "project.toml",
            &format!("[package]\nname='c1-text'\nentry='main::main'\n{build}"),
        );
        self.write("src/main.mb", source);
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

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// Run `main() -> u32` from source and from a standalone Wasm artifact and
/// require the same value and empty stderr in both.
fn expect_u32(source: &str, expected: u32) {
    let f = Fixture::new();
    f.project(source);
    let run = f.run(&["run"]);
    assert!(run.status.success(), "source failed: {}", text(&run.stderr));
    assert_eq!(text(&run.stdout), format!("Result: u32({expected})\n"));
    assert_eq!(text(&run.stderr), "");
    let build = f.run(&["build", "--output", "out.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        text(&build.stderr)
    );
    let wasm = f.run(&["run", "out.wasm"]);
    assert!(wasm.status.success(), "Wasm failed: {}", text(&wasm.stderr));
    assert_eq!(text(&wasm.stdout), format!("Result: i32({expected})\n"));
    assert_eq!(text(&wasm.stderr), "");
}

fn expect_check_error(body: &str, needle: &str) {
    let f = Fixture::new();
    f.project(&format!("fn main() -> u32 {{ {body} 0 }}\n"));
    let check = f.run(&["check"]);
    assert_eq!(check.status.code(), Some(1), "{body}");
    let stderr = text(&check.stderr);
    assert!(stderr.contains(needle), "{body}: {stderr}");
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

/// Scalar count and byte length of one literal, through a borrowed parameter.
fn count_and_len(literal: &str) -> String {
    format!(
        "fn count(value: borrow string) -> u32 {{ var n: u32 = 0; loop ch in value {{ n += 1; }} n }}\n\
         fn main() -> u32 {{ let value := \"{literal}\"; count(value.borrow()) * 100 + value.len() }}\n"
    )
}

#[test]
fn scalar_traversal_counts_scalars_not_bytes() {
    // (literal, scalars, bytes)
    for (literal, scalars, bytes) in [
        ("", 0, 0),
        ("hello", 5, 5),
        ("\u{e9}", 1, 2),
        ("\u{20ac}", 1, 3),
        ("\u{1F600}", 1, 4),
        ("a\u{e9}\u{20ac}\u{1F600}z", 5, 11),
    ] {
        expect_u32(&count_and_len(literal), scalars * 100 + bytes);
    }
}

#[test]
fn scalar_traversal_binds_exact_chars_in_order() {
    // Fold the scalar sequence into an order-sensitive number.
    let source = "fn code(ch: Char) -> u32 {\n\
        if ch == 'a' { 1 } else if ch == '\u{e9}' { 2 } else if ch == '\u{20ac}' { 3 }\n\
        else if ch == '\u{1F600}' { 4 } else { 9 }\n}\n\
        fn main() -> u32 {\n\
        let text := \"a\u{e9}\u{20ac}\u{1F600}\u{e9}\";\n\
        var acc: u32 = 0;\n\
        loop ch in text { acc = acc * 10 + code(ch); }\n\
        acc\n}\n";
    expect_u32(source, 12342);
}

#[test]
fn scalar_traversal_agrees_with_scalar_at_byte_offsets() {
    let source = "fn main() -> u32 {\n\
        let text := \"a\u{e9}\u{20ac}\u{1F600}\";\n\
        var offset: u32 = 0; var same: u32 = 0;\n\
        loop ch in text {\n\
            let step := match text.scalar_at(offset) { Some(v) => v, None => 0 };\n\
            if ch == '\u{1F600}' { if step == 128512 { same += 1; } }\n\
            else if ch == 'a' { if step == 97 { same += 1; } }\n\
            else if ch == '\u{e9}' { if step == 233 { same += 1; } }\n\
            else if ch == '\u{20ac}' { if step == 8364 { same += 1; } }\n\
            if ch == 'a' { offset += 1; } else if ch == '\u{e9}' { offset += 2; }\n\
            else if ch == '\u{20ac}' { offset += 3; } else { offset += 4; }\n\
        }\n\
        same * 100 + offset\n}\n";
    expect_u32(source, 410);
}

#[test]
fn text_is_still_usable_after_the_loop_and_receiver_is_evaluated_once() {
    let source = "fn main() -> u32 {\n\
        var text := \"a\u{20ac}\".concat(\"b\");\n\
        var n: u32 = 0;\n\
        loop ch in text { n += 1; }\n\
        text.push_str(\"\u{1F600}\");\n\
        loop ch in text { n += 10; }\n\
        n * 100 + text.len()\n}\n";
    // 3 scalars, then 4 more scalars after pushing the emoji; byte length 1 + 3 + 1 + 4.
    expect_u32(source, (3 + 40) * 100 + 9);
}

#[test]
fn nested_traversal_and_break_continue_with_borrowed_text() {
    let source = "fn main() -> u32 {\n\
        let text := \"a\u{e9}\u{20ac}\u{1F600}\";\n\
        var pairs: u32 = 0;\n\
        loop outer in text {\n\
            loop inner in text {\n\
                if inner == '\u{20ac}' { continue; }\n\
                if inner == '\u{1F600}' { break; }\n\
                pairs += 1;\n\
            }\n\
        }\n\
        pairs\n}\n";
    // Each of 4 outer scalars sees 'a' and 'e-acute', skips the euro, breaks at the emoji.
    expect_u32(source, 8);
}

#[test]
fn early_exits_with_heap_text_release_it_under_a_capped_wasm_memory() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let filler = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    f.project_with(
        "[build]\nstack_size=4096\n",
        &format!(
            "fn first_wide(text: borrow string) -> u32 {{\n\
                 loop ch in text {{ if ch == '€' {{ return 2; }} }}\n\
                 0\n}}\n\
             fn scan(flag: Bool) -> u32 {{\n\
                 let heap := \"é€{filler}\".concat(\"\");\n\
                 let other := \"{filler}\".concat(\"\");\n\
                 loop ch in heap {{\n\
                     if flag {{ return first_wide(heap.borrow()); }}\n\
                     if ch == 'é' {{ continue; }}\n\
                     break;\n\
                 }}\n\
                 other.len() - {TEXT_BYTES} + 1\n}}\n\
             fn main() -> u32 {{\n\
                 var iteration: u32 = 0; var total: u32 = 0;\n\
                 loop {{\n\
                     if iteration == {ITERATIONS} {{ break; }}\n\
                     total += scan(true) + scan(false);\n\
                     iteration += 1;\n\
                 }}\n\
                 total\n}}\n"
        ),
    );
    let expected = ITERATIONS * 3;
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        text(&source.stderr)
    );
    assert_eq!(text(&source.stdout), format!("Result: u32({expected})\n"));

    let build = f.run(&["build", "--output", "c1.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        text(&build.stderr)
    );
    let wasm_path = f.0.join("c1.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&wasm_path).unwrap());
    fs::write(&wasm_path, capped).unwrap();
    let wasm = f.run(&["run", "c1.wasm"]);
    assert!(wasm.status.success(), "Wasm failed: {}", text(&wasm.stderr));
    assert_eq!(text(&wasm.stdout), format!("Result: i32({expected})\n"));
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
fn traversal_loan_and_binding_negatives() {
    for (body, needle) in [
        (
            "var s := \"ab\".concat(\"c\"); loop ch in s { s.push_str(\"x\"); }",
            "while it is borrowed",
        ),
        (
            "var s := \"ab\".concat(\"c\"); loop ch in s { s = \"z\".concat(\"y\"); }",
            "cannot assign to `s` while it is borrowed",
        ),
        (
            "let s := \"ab\".concat(\"c\"); loop ch in s { let t := s; }",
            "cannot move `s` while it is borrowed",
        ),
        (
            "let s := \"ab\".concat(\"c\"); loop ch in s { drop(s); }",
            "cannot drop `s` while it is borrowed",
        ),
        (
            "let s := \"ab\"; loop ch in s { ch = 'a'; }",
            "cannot assign to immutable binding 'ch'",
        ),
        (
            "let s := \"ab\"; loop ch in \"abc\" { }",
            "string iteration requires a named string local or parameter",
        ),
        (
            "let s := \"ab\"; loop ch in s { let n: u32 = ch; }",
            "expected u32, found Char",
        ),
        (
            "let s := \"ab\"; loop ch in s { if ch < 'b' { } }",
            "ordering requires numbers",
        ),
    ] {
        expect_check_error(body, needle);
    }
}

#[test]
fn legacy_bytes_spelling_warns_without_failing() {
    let f = Fixture::new();
    f.project(
        "fn length(text: borrow string) -> u32 { text.len() }\n\
         fn main() -> u32 { let bytes: Bytes<2> = [1, 2]; let text := \"ab\"; if bytes[1] == 2 { length(text.borrow()) + 2 } else { 0 } }\n",
    );
    for args in [
        &["check"][..],
        &["build", "--output", "w.wasm"][..],
        &["run"][..],
    ] {
        let output = f.run(args);
        assert_eq!(
            output.status.code(),
            Some(0),
            "{args:?}: {}",
            text(&output.stderr)
        );
        let stderr = text(&output.stderr);
        assert!(!stderr.contains("MW002"), "{args:?}: {stderr}");
        assert!(
            stderr.contains(
                "warning[MW003]: legacy `Bytes<N>` type spelling; write `Array<u8, N>` instead"
            ),
            "{args:?}: {stderr}"
        );
        assert!(stderr.contains("src/main.mb:2:"), "{args:?}: {stderr}");
    }
    assert_eq!(text(&f.run(&["run"]).stdout), "Result: u32(4)\n");
}

#[test]
fn current_spellings_produce_no_warnings() {
    let f = Fixture::new();
    f.project(
        "fn length(text: borrow string) -> u32 { text.len() }\n\
         fn main() -> u32 { let bytes: Array<u8, 2> = [1, 2]; let text := \"ab\"; if bytes[1] == 2 { length(text.borrow()) + 2 } else { 0 } }\n",
    );
    for args in [&["check"][..], &["run"][..]] {
        let output = f.run(args);
        assert_eq!(output.status.code(), Some(0), "{args:?}");
        assert_eq!(text(&output.stderr), "", "{args:?}");
    }
}

#[test]
fn legacy_spelling_warnings_do_not_hide_errors() {
    let f = Fixture::new();
    f.project("fn main() -> u32 { let bytes: Bytes<1> = [1]; let n: u32 = true; n }\n");
    let output = f.run(&["check"]);
    assert_eq!(output.status.code(), Some(1));
    let stderr = text(&output.stderr);
    assert!(stderr.starts_with("warning[MW003]"), "{stderr}");
    assert!(stderr.contains("error[TE"), "{stderr}");
}

#[test]
fn uppercase_string_is_rejected_with_te001_on_check() {
    let f = Fixture::new();
    f.project("fn main() -> u32 { let text: String = \"a\"; text.len() }\n");
    let output = f.run(&["check"]);
    assert_eq!(output.status.code(), Some(1));
    let stderr = text(&output.stderr);
    assert!(stderr.contains("error[TE001]"), "{stderr}");
    assert!(stderr.contains("use lowercase 'string'"), "{stderr}");
    assert!(!stderr.contains("MW002"), "{stderr}");
}

#[test]
fn language_guide_uses_current_spellings_and_runs_with_empty_stderr() {
    let guide = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/guide");
    // The guide is split into topic modules; scan every source file.
    let mut paths: Vec<_> = fs::read_dir(guide.join("src"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "mb"))
        .collect();
    paths.sort();
    let source = paths
        .iter()
        .map(|path| fs::read_to_string(path).unwrap())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        source.contains("loop ch in sample"),
        "guide lacks the text loop example"
    );
    for (number, line) in source.lines().enumerate() {
        let code = line.split("//").next().unwrap();
        assert!(
            !code.contains("Bytes<")
                && !code
                    .split(|c: char| !c.is_alphanumeric())
                    .any(|w| w == "String"),
            "legacy spelling outside a comment at line {}: {line}",
            number + 1
        );
    }
    let f = Fixture::new();
    let run = Command::new(env!("CARGO_BIN_EXE_mb"))
        .current_dir(&guide)
        .arg("run")
        .output()
        .unwrap();
    assert_eq!(text(&run.stdout), "Result: Ok(i32(42))\n");
    assert_eq!(text(&run.stderr), "");
    let out = f.0.join("guide.wasm");
    let build = Command::new(env!("CARGO_BIN_EXE_mb"))
        .current_dir(&guide)
        .args(["build", "--output"])
        .arg(&out)
        .output()
        .unwrap();
    assert!(build.status.success(), "{}", text(&build.stderr));
    assert_eq!(text(&build.stderr), "");
    let wasm = f.run(&["run", "guide.wasm"]);
    assert_eq!(text(&wasm.stdout), "Result: Ok(i32(42))\n");
    assert_eq!(text(&wasm.stderr), "");
}
