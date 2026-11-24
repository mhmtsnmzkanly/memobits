//! G3: range loops `a..b` and `a..=b`.
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
            "memobits-g3-ranges-{}-{}",
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

fn rejects(f: &Fixture, source: &str, code: &str, text: &str) {
    f.write("src/main.mb", source);
    let check = f.run(&["check"]);
    assert!(!check.status.success(), "expected {code} for:\n{source}");
    let stderr = String::from_utf8_lossy(&check.stderr);
    assert!(stderr.contains(code), "expected {code}, got: {stderr}");
    assert!(stderr.contains(text), "expected `{text}`, got: {stderr}");
}

/// Run the source and Wasm artifacts, then the Wasm artifact again with its
/// memory capped to the initial size plus one page.
fn assert_source_wasm_and_capped(f: &Fixture, artifact: &str, expected: u64) {
    run_source_and_wasm(
        f,
        artifact,
        format!("Result: u32({expected})\n").as_bytes(),
        format!("Result: i32({expected})\n").as_bytes(),
    );
    let wasm_path = f.0.join(artifact);
    let (capped, initial, maximum) = cap_memory(&fs::read(&wasm_path).unwrap());
    fs::write(&wasm_path, capped).unwrap();
    let wasm = f.run(&["run", artifact]);
    assert!(
        wasm.status.success(),
        "capped Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, format!("Result: i32({expected})\n").as_bytes());
    assert_capped_memory(&wasm_path, initial, maximum);
}

const ITERATIONS: u32 = 4_096;
const TEXT_BYTES: usize = 1_024;

/// Per integer type: (name, minimum literal, maximum literal).
const WIDTHS: [(&str, &str, &str); 8] = [
    ("i8", "-128", "127"),
    ("i16", "-32768", "32767"),
    ("i32", "-2147483648", "2147483647"),
    ("i64", "-9223372036854775808", "9223372036854775807"),
    ("u8", "0", "255"),
    ("u16", "0", "65535"),
    ("u32", "0", "4294967295"),
    ("u64", "0", "18446744073709551615"),
];

/// Boundary checks for one width: inclusive ranges ending at the maximum
/// terminate without overflow, ranges starting at the minimum work, and
/// degenerate inclusive ranges run once.
fn boundary_functions() -> String {
    let mut text = String::new();
    for (ty, min, max) in WIDTHS {
        text.push_str(&format!(
            r#"fn bounds_{ty}() -> u32 {{
    let lo: {ty} = {min};
    let hi: {ty} = {max};
    var count: u32 = 0;
    var last: {ty} = lo;
    loop i in hi - 2..=hi {{ count += 1; last = i; }}
    assert(count == 3);
    assert(last == hi);
    count = 0;
    loop i in hi - 2..hi {{ count += 1; last = i; }}
    assert(count == 2);
    assert(last == hi - 1);
    count = 0;
    loop i in lo..=lo + 2 {{ count += 1; last = i; }}
    assert(count == 3);
    assert(last == lo + 2);
    count = 0;
    loop i in hi..=hi {{ count += 1; assert(i == hi); }}
    assert(count == 1);
    loop i in lo..=lo {{ count += 1; assert(i == lo); }}
    assert(count == 2);
    loop i in hi..hi {{ assert(false); }}
    loop i in lo..lo {{ assert(false); }}
    loop i in hi..=lo {{ assert(false); }}
    loop i in hi..lo {{ assert(false); }}
    7
}}
"#
        ));
    }
    text
}

fn boundary_program() -> String {
    let mut text = boundary_functions();
    text.push_str("fn main() -> u32 {\n    var total: u32 = 0;\n");
    for (ty, _, _) in WIDTHS {
        text.push_str(&format!("    total += bounds_{ty}();\n"));
    }
    text.push_str("    total\n}\n");
    text
}

const FULL: &str = r#"fn full_u8() -> u32 {
    let hi: u8 = 255;
    var count: u32 = 0;
    var sum: u32 = 0;
    loop i in 0..=hi { count += 1; sum += i as u32; }
    assert(count == 256);
    assert(sum == 32640);
    count
}
fn full_i8() -> i32 {
    let lo: i8 = -128;
    let hi: i8 = 127;
    var count: i32 = 0;
    var sum: i32 = 0;
    var first: i8 = 0;
    var last: i8 = 0;
    loop i in lo..=hi {
        if count == 0 { first = i; }
        count += 1;
        sum += i as i32;
        last = i;
    }
    assert(count == 256);
    assert(sum == -128);
    assert(first == -128);
    assert(last == 127);
    count
}
fn exclusive_u8() -> u32 {
    let hi: u8 = 255;
    var count: u32 = 0;
    loop i in 0..hi { count += 1; }
    assert(count == 255);
    count
}
fn full_u16() -> u32 {
    let hi: u16 = 65535;
    var count: u32 = 0;
    loop i in 0..=hi { count += 1; }
    assert(count == 65536);
    count
}
fn near_max_u64() -> u32 {
    let hi: u64 = 18446744073709551615;
    var count: u32 = 0;
    var last: u64 = 0;
    loop i in hi - 1_000..=hi { count += 1; last = i; }
    assert(count == 1001);
    assert(last == hi);
    count
}
fn near_min_i64() -> u32 {
    let lo: i64 = -9223372036854775808;
    var count: u32 = 0;
    var first: i64 = 0;
    loop i in lo..lo + 500 { if count == 0 { first = i; } count += 1; }
    assert(count == 500);
    assert(first == lo);
    count
}
fn negatives() -> i32 {
    var sum: i32 = 0;
    var count: i32 = 0;
    loop i in -5..-1 { sum += i; count += 1; }
    assert(sum == -14);
    assert(count == 4);
    loop i in -3..=3 { sum += i; count += 1; }
    assert(sum == -14);
    assert(count == 11);
    loop i in -2..=-2 { count += 1; }
    assert(count == 12);
    sum
}
fn empty_ranges() -> u32 {
    let n: u32 = 5;
    var runs: u32 = 0;
    loop i in n..n { runs += 1; }
    loop i in 5..0 { runs += 1; }
    loop i in n..=3 { runs += 1; }
    loop i in 10..=0 { runs += 1; }
    loop i in 0..0 { runs += 1; }
    loop i in 3..=2 { runs += 1; }
    loop i in 0..=n - 5 { runs += 100; }
    runs
}
fn literal_typing() -> u32 {
    let n: u8 = 4;
    var sum: u32 = 0;
    loop i in 0..n { sum += i as u32; }
    loop i in 1..=n { sum += i as u32; }
    let m: u64 = 3;
    loop i in 0..=m { sum += i as u32; }
    var k := 0;
    loop i in 0..3 { k += i; }
    assert(k == 3);
    sum
}
fn main() -> u32 {
    let a := full_u8();
    let b := full_i8();
    exclusive_u8();
    full_u16();
    near_max_u64();
    near_min_i64();
    assert(negatives() == -14);
    assert(empty_ranges() == 100);
    assert(literal_typing() == 6 + 10 + 6);
    a + b as u32
}
"#;

const ORDER: &str = r#"fn step(trace: share u32, digit: u32) -> u32 {
    trace = trace * 10 + digit;
    digit
}
fn bound(trace: share u32, digit: u32, value: u8) -> u8 {
    trace = trace * 10 + digit;
    value
}
fn main() -> u32 {
    var trace: u32 = 0;
    var runs: u32 = 0;
    loop i in bound(trace.share(), 1, 2)..bound(trace.share(), 2, 6) {
        runs += 1;
        trace = trace * 10 + 9;
    }
    assert(runs == 4);
    assert(trace == 129999);
    var second: u32 = 0;
    loop i in bound(second.share(), 3, 250)..=bound(second.share(), 4, 255) {
        runs += 1;
        second = second * 10 + 9;
    }
    assert(runs == 10);
    // Bounds are not re-read: changing the bound variable inside the body
    // does not change the iteration count.
    var limit: u32 = 3;
    var inner: u32 = 0;
    loop i in 0..limit { limit = 100; inner += 1; }
    assert(inner == 3);
    var start: u32 = 0;
    var seen: u32 = 0;
    loop i in start..=2 { start = 50; seen += i; }
    assert(seen == 3);
    // Evaluated before the first iteration, even when empty.
    var calls: u32 = 0;
    loop i in step(calls.share(), 7)..step(calls.share(), 3) { assert(false); }
    assert(calls == 73);
    trace
}
"#;

const CONTROL: &str = r#"fn brk() -> i32 {
    var sum: i32 = 0;
    loop i in 0..100 {
        if i == 5 { break; }
        sum += i;
    }
    sum
}
fn cont() -> i32 {
    var sum: i32 = 0;
    loop i in 0..=10 {
        if i % 2 == 1 { continue; }
        sum += i;
    }
    sum
}
fn cont_at_max() -> i32 {
    let hi: u8 = 255;
    var count: i32 = 0;
    loop i in 250..=hi {
        if i == 255 { continue; }
        count += 1;
    }
    var after: i32 = 0;
    loop i in 253..=hi {
        after += 1;
        if i == 255 { break; }
    }
    count * 10 + after
}
fn ret(target: i32) -> i32 {
    loop i in 0..1000 {
        if i == target { return i * 2; }
    }
    9999
}
fn nested() -> i32 {
    var sum: i32 = 0;
    loop i in 0..4 {
        loop j in i..=3 {
            if j == 2 { continue; }
            sum += i * 10 + j;
        }
    }
    sum
}
fn nested_break() -> i32 {
    var count: i32 = 0;
    loop i in 1..=5 {
        loop j in 1..=5 {
            if j > i { break; }
            count += 1;
        }
        if i == 4 { break; }
    }
    count
}
fn triple() -> i32 {
    var count: i32 = 0;
    loop a in 0..3 { loop b in 0..3 { loop c in 0..=a + b { count += 1; } } }
    count
}
fn shadow() -> i32 {
    let i := 100;
    var sum: i32 = 0;
    loop i in 0..3 { sum += i; }
    sum + i
}
fn with_inner_loop() -> i32 {
    var total: i32 = 0;
    loop i in 0..3 {
        var n: i32 = 0;
        loop {
            n += 1;
            if n > i { break; }
        }
        total += n;
    }
    total
}
fn main() -> u32 {
    assert(brk() == 10);
    assert(cont() == 30);
    assert(cont_at_max() == 53);
    assert(ret(7) == 14);
    assert(ret(5000) == 9999);
    // i=0: j 0,1,3 -> 4; i=1: j 1,3 -> 24; i=2: j 3 -> 23; i=3: j 3 -> 33
    assert(nested() == 4 + 24 + 23 + 33);
    assert(nested_break() == 1 + 2 + 3 + 4);
    assert(triple() == 1 + 2 + 3 + 2 + 3 + 4 + 3 + 4 + 5);
    assert(shadow() == 103);
    assert(with_inner_loop() == 6);
    (brk() + cont() + cont_at_max() + ret(7) + nested() + nested_break() + triple() + shadow()) as u32
}
"#;

const OWNERS: &str = r#"use alloc::List;
type Label { text: string, n: u32 }
fn body_owner(n: u32) -> u32 {
    var total: u32 = 0;
    loop i in 0..n {
        let s := "TEXT".concat("");
        let l := Label { text: "TEXT".concat(""), n: i };
        total += s.len() + l.text.len() + l.n;
    }
    total
}
fn with_continue(n: u32) -> u32 {
    var total: u32 = 0;
    loop i in 0..=n {
        let s := "TEXT".concat("");
        if i % 2 == 0 { continue; }
        total += s.len();
    }
    total
}
fn with_break(n: u32) -> u32 {
    var total: u32 = 0;
    loop i in 0..n {
        let s := "TEXT".concat("");
        if i == 3 { break; }
        total += s.len();
    }
    total
}
fn early(n: u32) -> u32 {
    loop i in 0..n {
        let s := "TEXT".concat("");
        if i == 2 { return s.len() + i; }
    }
    0
}
fn lists(n: u32) -> u32 {
    var items: List<string> = [];
    loop i in 0..n {
        let s := "TEXT".concat("");
        items.push(s);
    }
    let count := items.len();
    items.clear();
    count
}
fn main() -> u32 {
    var total: u32 = 0;
    loop round in 0..ITERATIONS {
        total += body_owner(2);
        total += with_continue(3);
        total += with_break(5);
        total += early(5);
        total += lists(3);
    }
    total
}
"#;

fn run_main(f: &Fixture, artifact: &str, expected: u64) {
    run_source_and_wasm(
        f,
        artifact,
        format!("Result: u32({expected})\n").as_bytes(),
        format!("Result: i32({expected})\n").as_bytes(),
    );
}

#[test]
fn every_width_terminates_at_its_extremes() {
    let f = Fixture::new();
    project(&f, "g3-bounds", &boundary_program());
    run_main(&f, "g3-bounds.wasm", 7 * 8);
}

#[test]
fn full_ranges_negatives_empty_and_literal_typing() {
    let f = Fixture::new();
    project(&f, "g3-full", FULL);
    // 256 (u8 count) + 256 (i8 count)
    run_main(&f, "g3-full.wasm", 512);
}

#[test]
fn bounds_are_evaluated_once_in_written_order() {
    let f = Fixture::new();
    project(&f, "g3-order", ORDER);
    // trace: bound digits 1 then 2 -> 12, then four iterations append 9 each.
    run_main(&f, "g3-order.wasm", 129_999);
}

#[test]
fn break_continue_return_and_nesting() {
    let f = Fixture::new();
    project(&f, "g3-control", CONTROL);
    // 10 + 30 + 53 + 14 + 84 + 10 + 27 + 103
    run_main(&f, "g3-control.wasm", 331);
}

#[test]
fn range_loop_owners_are_released_under_capped_memory() {
    let f = Fixture::new();
    let text = "x".repeat(TEXT_BYTES);
    project(
        &f,
        "g3-owners",
        &OWNERS
            .replace("TEXT", &text)
            .replace("ITERATIONS", &ITERATIONS.to_string()),
    );
    let t = TEXT_BYTES as u64;
    // body_owner(2): 2t + 2t + (0+1); with_continue(3): odd i = 1, 3 -> 2t;
    // with_break(5): i = 0, 1, 2 -> 3t; early(5): t + 2; lists(3): 3.
    let per_iteration = 4 * t + 1 + 2 * t + 3 * t + t + 2 + 3;
    assert_source_wasm_and_capped(&f, "g3-owners.wasm", per_iteration * u64::from(ITERATIONS));
}

#[test]
fn range_loop_misuse_is_rejected() {
    let f = Fixture::new();
    project(&f, "g3-negatives", "fn main() -> u32 { 0 }");
    let wrap = |body: &str| format!("fn main() -> u32 {{\n{body}\n    0\n}}\n");
    rejects(
        &f,
        &wrap("let a: u8 = 1; let b: u32 = 5; loop i in a..b { }"),
        "TE002",
        "expected u8, found u32",
    );
    rejects(
        &f,
        &wrap("let a: u8 = 1; let b: i8 = 5; loop i in a..=b { }"),
        "TE002",
        "expected u8, found i8",
    );
    rejects(
        &f,
        &wrap("loop i in 0.0..2.5 { }"),
        "TE017",
        "range bounds must be integers",
    );
    rejects(
        &f,
        &wrap("let a: f32 = 1.0; loop i in a..a { }"),
        "TE017",
        "range bounds must be integers",
    );
    rejects(
        &f,
        &wrap("loop i in 0..true { }"),
        "TE017",
        "range bounds must be integers",
    );
    rejects(
        &f,
        &wrap("let a: u8 = 1; loop i in a..300 { }"),
        "TE008",
        "integer literal does not fit u8",
    );
    rejects(&f, &wrap("loop i in 0..3 { i = 5; }"), "TE004", "i");
    rejects(&f, &wrap("let r := 0..5;"), "SE002", "is not a value");
    rejects(&f, &wrap("let r := 0..=5;"), "SE002", "is not a value");
    rejects(&f, &wrap("loop i in (0..5) { }"), "SE002", "is not a value");
    rejects(
        &f,
        &wrap("loop i in 0..9 step 2 { }"),
        "SE002",
        "expected '{'",
    );
    rejects(
        &f,
        &wrap("loop i in 0..3 { } assert(i == 0);"),
        "NE001",
        "i",
    );
    rejects(
        &f,
        &wrap("break;"),
        "TE020",
        "'break' is only allowed inside a loop",
    );
}
