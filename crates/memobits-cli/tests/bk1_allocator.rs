//! BK1: the guest allocator's segregated size classes. A performance
//! regression (many small frees before larger allocations scanned one list),
//! size-class boundaries, reuse across classes, the large-block list and
//! failure under a memory cap.
use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new(source: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-bk1-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            "[package]\nname='bk1'\nentry='main::main'\n[build]\nstack_size=4096\n",
        )
        .unwrap();
        fs::write(path.join("src/main.mb"), source).unwrap();
        Self(path)
    }

    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_mb"))
            .current_dir(&self.0)
            .args(args)
            .output()
            .unwrap()
    }

    /// Build the Wasm artifact, optionally lowering its memory maximum to the
    /// initial size plus one page, and run it.
    fn run_wasm(&self, cap: bool) -> Output {
        let build = self.run(&["build", "--output", "bk1.wasm"]);
        assert!(build.status.success(), "{}", text(&build.stderr));
        let path = self.0.join("bk1.wasm");
        if cap {
            let bytes = fs::read(&path).unwrap();
            fs::write(&path, cap_memory(&bytes)).unwrap();
        }
        self.run(&["run", "bk1.wasm"])
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

/// Lower the memory maximum to the initial size plus one page.
fn cap_memory(bytes: &[u8]) -> Vec<u8> {
    let mut module = bytes[..8].to_vec();
    let mut start = 8;
    while start < bytes.len() {
        let id = bytes[start];
        let mut cursor = start + 1;
        let len = read_uleb(bytes, &mut cursor) as usize;
        let payload = cursor;
        let end = payload + len;
        if id != 5 {
            module.extend_from_slice(&bytes[start..end]);
        } else {
            let mut cursor = payload;
            assert_eq!(read_uleb(bytes, &mut cursor), 1);
            let limits = read_uleb(bytes, &mut cursor);
            assert_ne!(limits & 1, 0);
            let initial = read_uleb(bytes, &mut cursor);
            let maximum_start = cursor;
            read_uleb(bytes, &mut cursor);
            let mut body = bytes[payload..maximum_start].to_vec();
            write_uleb(initial + 1, &mut body);
            body.extend_from_slice(&bytes[cursor..end]);
            module.push(id);
            write_uleb(body.len() as u32, &mut module);
            module.extend_from_slice(&body);
        }
        start = end;
    }
    module
}

fn expect(output: &Output, source_style: &str, wasm: bool) {
    assert!(output.status.success(), "{}", text(&output.stderr));
    let expected = if wasm {
        source_style.replace("u32(", "i32(")
    } else {
        source_style.to_string()
    };
    assert_eq!(text(&output.stdout), format!("Result: {expected}\n"));
}

/// Both runs of one program: source, then the Wasm artifact (optionally
/// capped). The Wasm entry renders `u32` results as `i32`.
fn check_both(source: &str, result: u64, cap: bool) {
    let f = Fixture::new(source);
    expect(&f.run(&["run"]), &format!("u32({result})"), false);
    expect(&f.run_wasm(cap), &format!("u32({result})"), true);
}

#[test]
fn small_frees_before_larger_allocations_stay_fast() {
    // 60,000 small blocks are freed at once and then 60,000 larger strings
    // are allocated. A single first-fit free list rescans every freed small
    // block for each larger request (quadratic: the source run exhausts its
    // default fuel budget); size classes serve both phases in constant time.
    let big = "x".repeat(100);
    let source = format!(
        r#"use alloc::List;
fn churn(n: u32) -> u32 {{
    var small: List<string> = [];
    var i: u32 = 0;
    loop {{ if i == n {{ break; }} let s := "ab".concat(""); small.push(s); i += 1; }}
    small.clear();
    var big: List<string> = [];
    var j: u32 = 0;
    loop {{ if j == n {{ break; }} let s := "{big}".concat(""); big.push(s); j += 1; }}
    big.len() + small.len()
}}
fn mixed(n: u32) -> u32 {{
    var total: u32 = 0;
    var round: u32 = 0;
    loop {{
        if round == 20 {{ break; }}
        var a: List<string> = [];
        var i: u32 = 0;
        loop {{
            if i == n {{ break; }}
            if round % 2 == 0 {{ let s := "abcdefgh".concat(""); a.push(s); }}
            else {{ let s := "{big}".concat(""); a.push(s); }}
            i += 1;
        }}
        total += a.len();
        round += 1;
    }}
    total
}}
fn main() -> u32 {{ churn(60000) + mixed(2000) }}
"#
    );
    let started = Instant::now();
    check_both(&source, 60_000 + 40_000, false);
    assert!(
        started.elapsed() < Duration::from_secs(10),
        "allocator churn took {:?}",
        started.elapsed()
    );
}

/// Lengths around every class boundary: exact four-byte classes up to 32,
/// four classes per octave afterwards, the 65,536-byte class limit and
/// larger blocks.
const BOUNDARIES: &[usize] = &[
    0, 1, 3, 4, 5, 8, 31, 32, 33, 36, 40, 41, 48, 49, 56, 57, 64, 65, 80, 81, 96, 97, 112, 113,
    128, 129, 160, 161, 1000, 4096, 4097, 65_535, 65_536, 65_537, 70_000,
];

#[test]
fn size_class_boundaries_round_trip_and_are_reused() {
    let mut functions = String::new();
    let mut calls = String::new();
    for (index, len) in BOUNDARIES.iter().enumerate() {
        let text = "y".repeat(*len);
        functions.push_str(&format!(
            "fn p{index}() -> u32 {{ let s := \"{text}\".concat(\"\"); s.len() }}\n"
        ));
        calls.push_str(&format!("total += p{index}();\n"));
    }
    // Two passes: the second reuses blocks released by the first.
    let source =
        format!("{functions}fn main() -> u32 {{\nvar total: u32 = 0;\n{calls}{calls}total\n}}\n");
    let expected: usize = BOUNDARIES.iter().sum::<usize>() * 2;
    check_both(&source, expected as u64, false);
}

#[test]
fn blocks_are_reused_across_size_classes_under_a_cap() {
    // Every round releases blocks of one class and then allocates larger and
    // smaller ones; initial + 1 page only holds if released blocks of other
    // classes are reused.
    let source = r#"use alloc::List;
fn fill(count: u32, which: u32) -> u32 {
    var items: List<string> = [];
    var i: u32 = 0;
    loop {
        if i == count { break; }
        if which == 0 { let s := "0123456789012345678901234567890123456789".concat(""); items.push(s); }
        else if which == 1 { let s := "0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789".concat(""); items.push(s); }
        else { let s := "ab".concat(""); items.push(s); }
        i += 1;
    }
    items.len()
}
fn main() -> u32 {
    var total: u32 = 0;
    var round: u32 = 0;
    loop {
        if round == 3000 { break; }
        total += fill(100, round % 3);
        total += fill(100, (round + 1) % 3);
        total += fill(60, (round + 2) % 3);
        round += 1;
    }
    total
}
"#;
    check_both(source, 3000 * 260, true);
}

#[test]
fn large_blocks_are_reused_for_small_and_large_requests_under_a_cap() {
    // A 70,000-byte block is above the class limit: it goes on the large list,
    // is taken by a small request and returns there.
    let large = "z".repeat(70_000);
    let source = format!(
        r#"fn round(n: u32) -> u32 {{
    let big := "{large}".concat("");
    let a := big.len();
    let small := "abc".concat("");
    a + small.len() + n
}}
fn main() -> u32 {{
    var total: u32 = 0;
    var i: u32 = 0;
    loop {{
        if i == 400 {{ break; }}
        total += round(i % 2);
        i += 1;
    }}
    total
}}
"#
    );
    check_both(&source, 400 * 70_003 + 200, true);
}

#[test]
fn allocation_failure_under_a_cap_still_traps() {
    // Kept strings must exhaust the capped memory with the unchanged trap.
    let source = r#"use alloc::List;
fn main() -> u32 {
    var kept: List<string> = [];
    var i: u32 = 0;
    loop {
        if i == 100000 { break; }
        let s := "0123456789012345678901234567890123456789".concat("");
        kept.push(s);
        i += 1;
    }
    kept.len()
}
"#;
    let f = Fixture::new(source);
    let output = f.run_wasm(true);
    assert!(!output.status.success(), "{output:?}");
    assert!(
        text(&output.stderr).contains("guest heap allocation failed"),
        "{}",
        text(&output.stderr)
    );
}
