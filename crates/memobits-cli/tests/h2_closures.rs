//! H2: non-escaping closures (`borrow fn` / `share fn`).
//!
//! Parameters of type `borrow fn(...)` / `share fn(...)`, anonymous functions
//! that capture enclosing locals (read-only use borrows, mutation shares),
//! the loan rules for live closures, the escape and access-mode negatives, the
//! stack-allocated environment convention of the Wasm backend, List parameters
//! and results in function types, and exact cleanup of heap captures under a
//! capped memory. Every positive program runs from source and as a standalone
//! Wasm artifact.
use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new(source: &str) -> Self {
        Self::with(source, "")
    }

    fn with(source: &str, extra_manifest: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-h2-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            format!("[package]\nname='h2'\nentry='main::main'\n{extra_manifest}"),
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
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// `check --tests` must fail with `code` and a message containing `needle`.
fn rejects(source: &str, code: &str, needle: &str) {
    let f = Fixture::new(source);
    let output = f.run(&["check", "--tests"]);
    let stderr = text(&output.stderr);
    assert!(!output.status.success(), "accepted:\n{source}");
    assert!(
        stderr.contains(code) && stderr.contains(needle),
        "expected {code} `{needle}` for:\n{source}\n{stderr}"
    );
}

/// `check`, `test` (expected count when nonzero), source `run` and standalone
/// Wasm `run`, each with empty stderr and the same `Result: i32(expected)`.
fn verify(f: &Fixture, tests: usize, expected: i64, label: &str) {
    let checked = f.run(&["check"]);
    assert!(
        checked.status.success(),
        "{label}: {}",
        text(&checked.stderr)
    );
    if tests > 0 {
        let report = f.run(&["test"]);
        let stdout = text(&report.stdout);
        assert!(
            report.status.success()
                && stdout.contains(&format!("test result: ok. {tests} passed; 0 failed")),
            "{label}: {stdout}{}",
            text(&report.stderr)
        );
    }
    let want = format!("Result: i32({expected})\n");
    let source_run = f.run(&["run"]);
    assert!(
        source_run.status.success() && source_run.stderr.is_empty(),
        "{label} source run: {}",
        text(&source_run.stderr)
    );
    assert_eq!(text(&source_run.stdout), want, "{label} (source)");
    let build = f.run(&["build", "--output", "h2.wasm"]);
    assert!(build.status.success(), "{label}: {}", text(&build.stderr));
    let wasm = f.run(&["run", "h2.wasm"]);
    assert!(
        wasm.status.success() && wasm.stderr.is_empty(),
        "{label} wasm run: {}",
        text(&wasm.stderr)
    );
    assert_eq!(text(&wasm.stdout), want, "{label} (wasm)");
}

fn single(source: &str, tests: usize, expected: i64, label: &str) {
    verify(&Fixture::new(source), tests, expected, label);
}

// ---------------------------------------------------------------------------
// Captures: read-only use borrows, mutation shares

#[test]
fn primitive_captures_are_read_and_mutated() {
    // total/flag/wide/ratio are mutated through share captures; scale and
    // offset are read through borrow captures; a plain function is accepted
    // by the same `borrow fn` parameter as a capturing closure.
    // total = 3 * (0+1+2+3) = 18; flag = true; wide = 6000; ratio = 4.0;
    // shifted = 1 + 18 + 7 = 26; plain = 42; out = 27.
    // 27 + 6 + 4 + 42 = 79.
    let source = r#"fn inc(x: i32) -> i32 { x + 1 }
fn visit(f: share fn(i32), n: i32) { loop i in 0..n { f(i); } }
fn probe(f: borrow fn(i32) -> i32, x: i32) -> i32 { f(x) }
fn main() -> i32 {
    var total := 0;
    var flag := false;
    var wide: u64 = 0;
    var ratio := 0.5;
    let scale := 3;
    let offset: u8 = 7;
    visit(fn(i) { total += i * scale; }, 4);
    visit(fn(i) { if i == 2 { flag = true; } }, 4);
    visit(fn(i) { wide += (i as u64) * 1000; }, 4);
    visit(fn(i) { ratio = ratio * 2.0; }, 3);
    let shifted := probe(fn(x) => x + total + (offset as i32), 1);
    let plain := probe(inc, 41);
    var out := shifted;
    if flag { out += 1; }
    out + (wide / 1000) as i32 + (ratio as i32) + plain
}
"#;
    single(source, 0, 79, "primitive captures");
}

#[test]
fn strings_structs_and_lists_are_captured_in_place() {
    // p.x = 1+0+1+2 = 4, p.y = 2*2*2*2 = 16; l = [0,1,4,9]; s = "ab---";
    // bag.items = [0,1]; acc = 14 (a loop over a captured List inside the
    // closure); n = 5 + 4 + 3 = 12. 4 + 16 + 12 + 14 + 2 = 48.
    let source = r#"use alloc::List;
type Point { x: i32, y: i32 }
type Bag { items: List<i32>, label: string }
fn visit(f: share fn(i32), n: i32) { loop i in 0..n { f(i); } }
fn peek_len(f: borrow fn() -> u32) -> u32 { f() }
fn main() -> i32 {
    var p := Point { x: 1, y: 2 };
    var l: List<i32> = [];
    var s := "ab";
    let sep := "-";
    var bag := Bag { items: [], label: "bag" };
    var acc := 0;
    visit(fn(i) { p.x += i; p.y = p.y * 2; }, 3);
    visit(fn(i) { l.push(i * i); }, 4);
    visit(fn(i) { s.push_str(sep); }, 3);
    visit(fn(i) { bag.items.push(i); }, 2);
    visit(fn(i) { loop v in l { acc += v; } }, 1);
    let n := peek_len(fn() => s.len() + (l.len() as u32) + bag.label.len());
    p.x + p.y + (n as i32) + acc + (bag.items.len() as i32)
}
"#;
    single(source, 0, 48, "heap captures");
}

#[test]
fn closures_bound_with_let_are_called_and_passed_on() {
    // bump is shared; after its last use `total` is accessible again.
    // total = 1 + 5 + 5 + 100 = 111; read_twice(peek) = 222; peek() = 111.
    let source = r#"fn call_twice(f: share fn(i32), x: i32) { f(x); f(x); }
fn read_twice(f: borrow fn() -> i32) -> i32 { f() + f() }
fn main() -> i32 {
    var total := 0;
    let bump := fn(x: i32) { total += x; };
    bump(1);
    call_twice(bump, 5);
    total += 100;
    let peek := fn() -> i32 => total;
    let a := read_twice(peek);
    let b := peek();
    total = 0;
    a + b + total
}
"#;
    single(source, 0, 333, "let-bound closures");
}

#[test]
fn nested_closures_and_recursion_through_helpers() {
    // call2(add, 10) = 13 + 14 = 27; wrap = (1+3+100) + (2+3+100) = 209;
    // nested(4) = (0+1+2+3)^2 = 36; fact(f, 4) = 4*3*2*f(1) = 96.
    let source = r#"fn call2(f: borrow fn(i32) -> i32, x: i32) -> i32 { f(x) + f(x + 1) }
fn pass_on(f: borrow fn(i32) -> i32) -> i32 { call2(f, 10) }
fn wrap(f: borrow fn(i32) -> i32, k: i32) -> i32 {
    // A closure that captures a `borrow fn` parameter and only calls it.
    call2(fn(x) => f(x) + k, 1)
}
fn each(f: share fn(i32), n: i32) { loop i in 0..n { f(i); } }
fn nested(n: i32) -> i32 {
    var total := 0;
    each(fn(a) => each(fn(b) => total += a * b, n), n);
    total
}
fn fact(f: borrow fn(i32) -> i32, n: i32) -> i32 {
    if n <= 1 { f(1) } else { n * fact(f, n - 1) }
}
fn main() -> i32 {
    let base := 3;
    let add := fn(x: i32) -> i32 => x + base;
    pass_on(add) + wrap(add, 100) + nested(4) + fact(fn(x) => x + base, 4)
}
"#;
    single(source, 0, 368, "nested closures");
}

#[test]
fn function_type_parameters_take_borrow_and_share_functions() {
    // `h` is a parameter of type `fn(borrow fn(i32) -> i32) -> i32`; the
    // argument is a closure whose own parameter is a `borrow fn`.
    // higher(fn(g) => g(1) + base) = 2 + 7 = 9; higher(plain) = 10.
    let source = r#"fn higher(h: borrow fn(borrow fn(i32) -> i32) -> i32) -> i32 {
    h(fn(x) => x * 2)
}
fn plain(g: borrow fn(i32) -> i32) -> i32 => g(5)
fn main() -> i32 {
    let base := 7;
    higher(fn(g) => g(1) + base) + higher(plain)
}
"#;
    single(source, 0, 19, "function-typed parameters");
}

#[test]
fn closures_work_in_test_functions_and_with_the_alloc_layer_off() {
    let source = r#"fn visit(f: share fn(i32), n: i32) { loop i in 0..n { f(i); } }
fn total_of(n: i32) -> i32 {
    var total := 0;
    let step := 2;
    visit(fn(i) { total += i * step; }, n);
    total
}
test fn closure_in_a_test() {
    var seen := 0;
    visit(fn(i) { seen += 1; }, 4);
    assert(seen == 4);
    assert(total_of(4) == 12);
}
fn main() -> i32 { total_of(5) }
"#;
    // 2 * (0+1+2+3+4) = 20; no heap is involved.
    verify(
        &Fixture::with(source, "[build]\nalloc = false\n"),
        1,
        20,
        "alloc = false",
    );
}

// ---------------------------------------------------------------------------
// List parameters and results in function types

#[test]
fn lists_in_function_types_follow_direct_call_rules() {
    // run: f fills 5 (sum 10), mk(4) sums to 6, c consumes a 4-element List.
    // A closure with a capture takes a `share List<i32>` parameter too:
    // fill_with adds k = 100 to each pushed index, 2 elements -> 100 + 101.
    let source = r#"use alloc::List;
fn fill(l: share List<i32>, n: i32) { loop i in 0..n { l.push(i); } }
fn total(l: borrow List<i32>) -> i32 { var t := 0; loop x in l { t += x; } t }
fn make(n: i32) -> List<i32> { var l: List<i32> = []; fill(l.share(), n); l }
fn consume(l: List<i32>) -> i32 { l.len() as i32 }
fn run(f: fn(share List<i32>, i32), g: fn(borrow List<i32>) -> i32, mk: fn(i32) -> List<i32>, c: fn(List<i32>) -> i32) -> i32 {
    var l: List<i32> = [];
    f(l.share(), 5);
    let m := mk(4);
    g(l.borrow()) + g(m.borrow()) + c(m)
}
fn with_list(f: borrow fn(share List<i32>, i32), n: i32) -> i32 {
    var l: List<i32> = [];
    f(l.share(), n);
    total(l.borrow())
}
fn main() -> i32 {
    let k := 100;
    run(fill, total, make, consume)
        + with_list(fn(l, n) { loop i in 0..n { l.push(i + k); } }, 2)
}
"#;
    single(source, 0, 20 + 201, "lists in function types");
}

// ---------------------------------------------------------------------------
// Wasm: environment records live in the creator's frame; one convention

#[test]
fn indirect_calls_take_a_trailing_environment_pointer() {
    let f = Fixture::new(
        r#"fn inc(x: i32) -> i32 { x + 1 }
fn apply(f: borrow fn(i32) -> i32, x: i32) -> i32 { f(x) }
fn main() -> i32 {
    var total := 0;
    let k := 10;
    let mut_add := fn(x: i32) { total += x + k; };
    mut_add(1);
    mut_add(2);
    apply(inc, 1) + apply(fn(x) => x * k, 2) + total
}
"#,
    );
    // 2 + 20 + (11 + 12) = 45.
    verify(&f, 0, 45, "environment convention");
    let bytes = fs::read(f.0.join("h2.wasm")).unwrap();
    let mut types: Vec<Vec<wasmparser::ValType>> = Vec::new();
    let mut indirect = Vec::new();
    let mut table_size = 0;
    let mut element_functions = 0;
    for payload in wasmparser::Parser::new(0).parse_all(&bytes) {
        match payload.unwrap() {
            wasmparser::Payload::TypeSection(section) => {
                for group in section {
                    for ty in group.unwrap().types() {
                        if let wasmparser::CompositeInnerType::Func(func) = &ty.composite_type.inner
                        {
                            types.push(func.params().to_vec());
                        }
                    }
                }
            }
            wasmparser::Payload::TableSection(section) => {
                for table in section {
                    table_size = table.unwrap().ty.initial;
                }
            }
            wasmparser::Payload::ElementSection(section) => {
                for element in section {
                    if let wasmparser::ElementItems::Functions(functions) = element.unwrap().items {
                        element_functions += functions.count();
                    }
                }
            }
            wasmparser::Payload::CodeSectionEntry(body) => {
                for operator in body.get_operators_reader().unwrap() {
                    if let wasmparser::Operator::CallIndirect { type_index, .. } = operator.unwrap()
                    {
                        indirect.push(type_index as usize);
                    }
                }
            }
            _ => {}
        }
    }
    // Slot 0 stays empty: `inc`, the two closures and the `mut_add` closure.
    assert_eq!(table_size, 4, "one slot per function used as a value");
    assert_eq!(element_functions, 3);
    assert!(!indirect.is_empty());
    for index in indirect {
        let params = &types[index];
        assert_eq!(
            params.last(),
            Some(&wasmparser::ValType::I32),
            "every indirect call ends with the i32 environment pointer: {params:?}"
        );
        // One declared i32 parameter plus the environment pointer.
        assert_eq!(params.len(), 2, "{params:?}");
    }
}

// ---------------------------------------------------------------------------
// Exact cleanup of heap captures under capped memory

const ITERATIONS: u32 = 4_096;
const TEXT_BYTES: usize = 1_024;

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

/// Lower the memory maximum to the initial size plus one page, so repeated
/// iterations must reuse released String blocks.
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
        if id != 5 {
            module.extend_from_slice(&bytes[section_start..section_end]);
        } else {
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

/// The capped program: every round builds heap Strings and a List, shares the
/// String and the List into closures that grow them (`push_str`, `push`),
/// reads them through a borrow closure, and may return early. `{extra}` and
/// `{clear}` let the mutation check keep a String per round or release it.
fn capped_program(extra: &str, clear: &str) -> String {
    let text = "x".repeat(TEXT_BYTES);
    format!(
        r#"use alloc::List;
fn visit(f: share fn(u32), n: u32) {{
    var i: u32 = 0;
    loop {{ if i == n {{ break; }} f(i); i += 1; }}
}}
fn peek(f: borrow fn() -> u32) -> u32 {{ f() }}
fn round(keep: share List<string>, early: bool) -> u32 {{
    var s := "{text}".concat("");
    let t := "{text}".concat("");
    var l: List<u32> = [];
    visit(fn(i) {{ l.push(i); s.push_str("ab"); }}, 3);
    let n := peek(fn() => t.len() + s.len());
    {extra}
    if early {{ return n; }}
    n + (l.len() as u32)
}}
fn main() -> u32 {{
    var keep: List<string> = [];
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {{
        if iteration == {ITERATIONS} {{ break; }}
        total += round(keep.share(), iteration % 2 == 0);
        {clear}
        iteration += 1;
    }}
    total
}}
"#
    )
}

fn run_capped(source: &str) -> (Fixture, Output) {
    let f = Fixture::with(source, "[build]\nstack_size=4096\n");
    let build = f.run(&["build", "--output", "capped.wasm"]);
    assert!(build.status.success(), "{}", text(&build.stderr));
    let path = f.0.join("capped.wasm");
    let (capped, _, _) = cap_memory(&fs::read(&path).unwrap());
    fs::write(&path, capped).unwrap();
    let output = f.run(&["run", "capped.wasm"]);
    (f, output)
}

#[test]
fn heap_captures_release_exactly_under_capped_memory() {
    let t = TEXT_BYTES as u64;
    // Per round: n = t + (t + 6) = 2t + 6; an early round returns n, the
    // others add the 3 List elements.
    let early = 2 * t + 6;
    let late = early + 3;
    let rounds = u64::from(ITERATIONS);
    let expected = (rounds / 2) * early + (rounds / 2) * late;
    let source = capped_program("", "");
    let f = Fixture::with(&source, "[build]\nstack_size=4096\n");
    let source_run = f.run(&["run"]);
    assert!(
        source_run.status.success(),
        "source run: {}",
        text(&source_run.stderr)
    );
    assert_eq!(
        text(&source_run.stdout),
        format!("Result: u32({expected})\n")
    );
    let (f, capped) = run_capped(&source);
    assert!(
        capped.status.success() && capped.stderr.is_empty(),
        "capped Wasm run failed: {}",
        text(&capped.stderr)
    );
    assert_eq!(text(&capped.stdout), format!("Result: i32({expected})\n"));
    // The cap is initial + one page.
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(f.0.join("capped.wasm")).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.maximum, Some(memory.initial + 1));
}

#[test]
fn mutation_check_keeping_a_string_per_round_exhausts_the_capped_memory() {
    // The same program, but every round moves a fresh heap String into a List
    // that is never emptied (a release removed from the clean program): the
    // cap must trap, so the clean run above really measures the cleanup.
    let text = "x".repeat(TEXT_BYTES);
    let keep = format!(r#"let junk := "{text}".concat(""); keep.push(junk);"#);
    let (_f, kept) = run_capped(&capped_program(&keep, ""));
    assert!(!kept.status.success(), "{kept:?}");
    assert!(
        text_of(&kept.stderr).contains("guest heap allocation failed"),
        "{}",
        text_of(&kept.stderr)
    );
    // With the clear restored the same shape runs clean.
    let (_f, cleared) = run_capped(&capped_program(&keep, "keep.clear();"));
    assert!(
        cleared.status.success() && cleared.stderr.is_empty(),
        "{}",
        text_of(&cleared.stderr)
    );
}

fn text_of(bytes: &[u8]) -> String {
    text(bytes)
}

// ---------------------------------------------------------------------------
// Negatives: loans held by a live closure

#[test]
fn a_live_share_closure_blocks_access_to_its_captures() {
    // Reading, assigning or sharing `total` while a share closure that is
    // called later is live.
    rejects(
        "fn main() -> i32 { var total := 0; let f := fn(x: i32) { total += x; }; f(1); total += 5; f(2); total }\n",
        "BE005",
        "cannot read `total` while it is shared",
    );
    rejects(
        "fn main() -> i32 { var total := 0; let f := fn(x: i32) { total += x; }; f(1); total = 5; f(2); total }\n",
        "BE005",
        "cannot assign to `total` while it is shared",
    );
    // A direct use inside another closure literal counts as well.
    rejects(
        "fn main() -> i32 { var t := 0; let f := fn() { t += 1; }; let g := fn() -> i32 => t; f(); g() }\n",
        "BE005",
        "while it is shared",
    );
}

#[test]
fn two_share_closures_over_one_variable_cannot_be_live_together() {
    rejects(
        "fn main() -> i32 { var total := 0; let f := fn(x: i32) { total += x; }; let g := fn(x: i32) { total += x * 2; }; f(1); g(2); total }\n",
        "BE005",
        "cannot share `total` while it is shared",
    );
    // As two arguments of one call.
    rejects(
        "fn two(a: share fn(i32), b: share fn(i32)) { a(1); b(1); }\nfn main() -> i32 { var t := 0; two(fn(x) => t += x, fn(x) => t += x * 2); t }\n",
        "BE005",
        "cannot share `t` while",
    );
    // A read closure and a share closure over the same variable.
    rejects(
        "fn main() -> i32 { var t := 0; let r := fn() -> i32 => t; let w := fn() { t += 1; }; w(); r() }\n",
        "BE005",
        "cannot share `t` while it is borrowed",
    );
}

#[test]
fn a_read_closure_blocks_writes_and_moves_of_its_captures() {
    rejects(
        "fn main() -> i32 { var t := 1; let r := fn() -> i32 => t; t = 5; r() }\n",
        "BE005",
        "cannot assign to `t` while it is borrowed",
    );
    // Capturing and then moving the variable.
    rejects(
        "fn take(s: string) {}\nfn main() -> i32 { var s := \"abc\"; let f := fn() => s.len(); take(s); f(); 0 }\n",
        "BE005",
        "cannot move `s` while it is borrowed",
    );
}

#[test]
fn access_after_the_last_use_of_a_closure_is_allowed() {
    let source = r#"fn main() -> i32 {
    var total := 0;
    let f := fn(x: i32) { total += x; };
    f(1);
    f(2);
    total += 10;
    let g := fn(x: i32) { total += x; };
    g(100);
    total + 1
}
"#;
    single(source, 0, 114, "access after the last use");
}

// ---------------------------------------------------------------------------
// Negatives: closures are second-class

#[test]
fn capturing_closures_cannot_escape() {
    let second_class = "second-class";
    // Returned directly.
    rejects(
        "fn make() -> fn(i32) -> i32 { let base := 3; fn(x: i32) -> i32 => x + base }\nfn main() -> i32 { make()(1) }\n",
        "TE017",
        second_class,
    );
    // Stored in a field, an array, a List.
    rejects(
        "type H { f: fn(i32) -> i32 }\nfn main() -> i32 { let base := 3; let h := H { f: fn(x: i32) -> i32 => x + base }; h.f(1) }\n",
        "TE017",
        second_class,
    );
    rejects(
        "fn main() -> i32 { let base := 3; let g := fn(x: i32) -> i32 => x + base; let fs := [g]; 0 }\n",
        "TE017",
        second_class,
    );
    rejects(
        "use alloc::List;\nfn main() -> i32 { let base := 3; let g := fn(x: i32) -> i32 => x + base; var fs: List<fn(i32) -> i32> = []; fs.push(g); 0 }\n",
        "TE017",
        second_class,
    );
    // Bound with let and then returned.
    rejects(
        "fn make() -> fn(i32) -> i32 { let base := 3; let g := fn(x: i32) -> i32 => x + base; g }\nfn main() -> i32 { 0 }\n",
        "TE017",
        second_class,
    );
    // Moved or copied into another binding, or rebound with var.
    rejects(
        "fn main() -> i32 { var t := 0; let f := fn(y: i32) { t += y; }; var g := f; 0 }\n",
        "TE017",
        second_class,
    );
    rejects(
        "fn main() -> i32 { let n := 5; let f := fn(x: i32) -> i32 => x + n; let g: fn(i32) -> i32 = f; g(1) }\n",
        "TE017",
        second_class,
    );
    rejects(
        "fn main() -> i32 { let n := 5; var f := fn(x: i32) -> i32 => x + n; f(1) }\n",
        "TE017",
        second_class,
    );
    // Passed to an owned `fn` parameter.
    rejects(
        "fn own(f: fn(i32), n: i32) {}\nfn main() -> i32 { var t := 0; own(fn(x) => t += x, 3); t }\n",
        "TE017",
        second_class,
    );
    // A closure that captures a `borrow fn` parameter is a capturing closure.
    rejects(
        "fn keep(f: borrow fn(i32) -> i32) -> fn(i32) -> i32 { fn(x) => f(x) }\nfn main() -> i32 { 0 }\n",
        "TE017",
        second_class,
    );
}

#[test]
fn borrow_and_share_function_parameters_cannot_escape() {
    for source in [
        "fn keep(f: borrow fn(i32) -> i32) -> fn(i32) -> i32 { f }\nfn main() -> i32 { 0 }\n",
        "type H { f: fn(i32) -> i32 }\nfn keep(f: borrow fn(i32) -> i32) -> H { H { f: f } }\nfn main() -> i32 { 0 }\n",
        "fn keep(f: borrow fn(i32) -> i32) { let g: fn(i32) -> i32 = f; g(1); }\nfn main() -> i32 { 0 }\n",
        "fn keep(f: share fn(i32)) -> fn(i32) { f }\nfn main() -> i32 { 0 }\n",
        "fn take(f: fn(i32) -> i32) -> i32 { f(1) }\nfn keep(f: borrow fn(i32) -> i32) -> i32 { take(f) }\nfn main() -> i32 { 0 }\n",
        "use alloc::List;\nfn keep(f: borrow fn(i32) -> i32) { var l: List<fn(i32) -> i32> = []; l.push(f); }\nfn main() -> i32 { 0 }\n",
    ] {
        rejects(source, "TE017", "reference values cannot escape");
    }
}

#[test]
fn closures_must_match_the_access_of_their_parameter() {
    // A literal that mutates, to a `borrow fn` parameter.
    rejects(
        "fn each(f: borrow fn(i32), n: i32) {}\nfn main() -> i32 { var t := 0; each(fn(x) => t += x, 3); t }\n",
        "TE017",
        "needs a `share fn` parameter",
    );
    // A let-bound closure that mutates.
    rejects(
        "fn run(f: borrow fn(i32) -> i32) -> i32 { f(1) }\nfn main() -> i32 { var t := 0; let g := fn(x: i32) -> i32 { t += x; t }; run(g) }\n",
        "TE017",
        "needs a `share fn` parameter",
    );
    // A `share fn` parameter passed on to a `borrow fn` parameter.
    rejects(
        "fn read(f: borrow fn(i32)) { f(1); }\nfn write(f: share fn(i32)) { read(f); }\nfn main() -> i32 { 0 }\n",
        "TE017",
        "needs a `share fn` parameter",
    );
    // A closure calling a `share fn` parameter is a share closure.
    rejects(
        "fn read(f: borrow fn(i32)) { f(1); }\nfn write(f: share fn(i32)) { read(fn(x) => f(x)); }\nfn main() -> i32 { 0 }\n",
        "TE017",
        "needs a `share fn` parameter",
    );
    // The reverse (a read closure to a `share fn` parameter) is fine.
    single(
        "fn each(f: share fn(i32)) { f(1); f(2); }\nfn main() -> i32 { let k := 4; var n := 0; each(fn(x) => n += x * k); n }\n",
        0,
        12,
        "read and share closures to share fn",
    );
}

#[test]
fn captures_of_immutable_variables_cannot_be_mutated() {
    rejects(
        "fn main() -> i32 { let x := 1; let f := fn(y: i32) { x += y; }; f(1); x }\n",
        "TE004",
        "cannot capture 'x' by share because it is not mutable",
    );
    // A captured `borrow` parameter cannot be mutated either.
    rejects(
        "fn bump(n: borrow i32) { let f := fn() { n += 1; }; f(); }\nfn main() -> i32 { 0 }\n",
        "TE004",
        "cannot capture 'n' by share",
    );
}

// ---------------------------------------------------------------------------
// Temporary List owners passed through function values

/// Every round passes fresh List owners (each holding a heap String) to an
/// owned List parameter four ways: directly, through a function-typed local,
/// and through a function value received as a parameter (a local and a name).
/// `{extra}` lets the mutation check keep one String per round.
fn list_owner_program(extra: &str) -> String {
    let text = "x".repeat(TEXT_BYTES);
    format!(
        r#"use alloc::List;
fn make() -> List<string> {{
    var l: List<string> = [];
    let s := "{text}".concat("");
    l.push(s);
    l
}}
fn take(l: List<string>, k: u32) -> u32 {{ (l.len() as u32) + l[0].len() + k }}
fn indirect(f: fn(List<string>, u32) -> u32, l: List<string>, k: u32) -> u32 {{ f(l, k) }}
fn round(early: bool, keep: share List<string>) -> u32 {{
    let f: fn(List<string>, u32) -> u32 = take;
    let a := take(make(), 0);
    if early {{ return a + f(make(), 1); }}
    {extra}
    a + f(make(), 1) + indirect(f, make(), 2) + indirect(take, make(), 3)
}}
fn main() -> u32 {{
    var keep: List<string> = [];
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {{
        if iteration == {ITERATIONS} {{ break; }}
        total += round(iteration % 2 == 0, keep.share());
        iteration += 1;
    }}
    total
}}
"#
    )
}

#[test]
fn temporary_list_owners_through_function_values_release_exactly_under_capped_memory() {
    let t = TEXT_BYTES as u64;
    let one = t + 1; // len() + first element length
    let early = one + (one + 1);
    let late = one + (one + 1) + (one + 2) + (one + 3);
    let rounds = u64::from(ITERATIONS);
    let expected = (rounds / 2) * early + (rounds / 2) * late;
    let source = list_owner_program("");
    let f = Fixture::with(&source, "[build]\nstack_size=4096\n");
    let source_run = f.run(&["run"]);
    assert!(
        source_run.status.success(),
        "source run: {}",
        text(&source_run.stderr)
    );
    assert_eq!(
        text(&source_run.stdout),
        format!("Result: u32({expected})\n")
    );
    let (f, capped) = run_capped(&source);
    assert!(
        capped.status.success() && capped.stderr.is_empty(),
        "capped Wasm run failed: {}",
        text(&capped.stderr)
    );
    assert_eq!(text(&capped.stdout), format!("Result: i32({expected})\n"));
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(f.0.join("capped.wasm")).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.maximum, Some(memory.initial + 1));
}

#[test]
fn mutation_check_keeping_a_list_string_per_round_exhausts_the_capped_memory() {
    // A String moved into a never-emptied List each (late) round: the cap must
    // trap, so the clean run above really measures the cleanup.
    let text = "x".repeat(TEXT_BYTES);
    let keep = format!(r#"let junk := "{text}".concat(""); keep.push(junk);"#);
    let (_f, kept) = run_capped(&list_owner_program(&keep));
    assert!(!kept.status.success(), "{kept:?}");
    assert!(
        text_of(&kept.stderr).contains("guest heap allocation failed"),
        "{}",
        text_of(&kept.stderr)
    );
}

#[test]
fn a_temporary_list_owner_is_accepted_directly_and_through_a_function_value() {
    // 2 + 2 + 2 + 2: the same owner temporary, four routes.
    single(
        r#"use alloc::List;
fn make() -> List<i32> { var l: List<i32> = []; l.push(1); l.push(2); l }
fn take(l: List<i32>, k: i32) -> i32 { (l.len() as i32) + k }
fn indirect(f: fn(List<i32>, i32) -> i32, l: List<i32>, k: i32) -> i32 { f(l, k) }
fn main() -> i32 {
    let f: fn(List<i32>, i32) -> i32 = take;
    take(make(), 0) + f(make(), 0) + indirect(take, make(), 0) + indirect(f, make(), 0)
}
"#,
        0,
        8,
        "temporary List owners",
    );
}

// ---------------------------------------------------------------------------
// Capture classification (structural capture analysis)

/// A chain of `levels` nested `share fn` literals, each binding one parameter,
/// whose innermost body adds all of them to `t`.
fn nested_closures(levels: usize) -> String {
    let names: Vec<String> = (0..levels).map(|i| format!("p{i}")).collect();
    let mut body = format!("t += {};", names.join(" + "));
    for name in names.iter().rev() {
        body = format!("each(fn({name}) {{ {body} }}, 2);");
    }
    format!(
        "fn each(f: share fn(i32), n: i32) {{ loop i in 0..n {{ f(i); }} }}\nfn main() -> i32 {{ var t := 0; {body} t }}\n"
    )
}

#[test]
fn deeply_nested_closures_check_in_linear_time() {
    // Every level is analysed once: 12 levels used to take over a minute
    // (the cost doubled per level). The bound is generous for a debug build.
    for (levels, expected) in [(6, 192), (12, 24_576)] {
        let f = Fixture::new(&nested_closures(levels));
        let start = std::time::Instant::now();
        let checked = f.run(&["check"]);
        let elapsed = start.elapsed();
        assert!(checked.status.success(), "{}", text(&checked.stderr));
        assert!(
            elapsed < std::time::Duration::from_secs(2),
            "{levels} levels took {elapsed:?}"
        );
        if levels == 6 {
            verify(&f, 0, expected, "six nested levels");
        } else {
            let run = f.run(&["run"]);
            assert_eq!(
                text(&run.stdout),
                format!("Result: i32({expected})\n"),
                "{}",
                text(&run.stderr)
            );
        }
    }
}

#[test]
fn mutation_through_a_nested_projection_makes_a_share_capture() {
    single(
        r#"use alloc::List;
type P { x: i32 }
type Q { pts: List<P> }
fn each(f: share fn(i32), n: i32) { loop i in 0..n { f(i); } }
fn main() -> i32 {
    var pts: List<P> = [];
    pts.push(P { x: 1 });
    pts.push(P { x: 2 });
    var q := Q { pts: pts };
    each(fn(i) { q.pts[1].x += i; }, 3);
    q.pts[1].x
}
"#,
        0,
        5,
        "nested projection",
    );
    rejects(
        r#"use alloc::List;
type P { x: i32 }
fn probe(f: borrow fn(i32), n: i32) { f(n); }
fn main() -> i32 { var pts: List<P> = []; pts.push(P { x: 1 }); probe(fn(i) { pts[0].x = i; }, 3); 0 }
"#,
        "TE017",
        "needs a `share fn` parameter",
    );
}

#[test]
fn a_share_self_receiver_makes_a_share_capture() {
    let methods = "type Lane { width: i32 } extend {\n    fn span(borrow self) -> i32 { self.width }\n    fn widen(share self) { self.width += 1; }\n}\n";
    single(
        &format!(
            "{methods}fn each(f: share fn(i32), n: i32) {{ loop i in 0..n {{ f(i); }} }}\nfn main() -> i32 {{ var l := Lane {{ width: 1 }}; each(fn(i) {{ l.widen(); }}, 3); l.span() }}\n"
        ),
        0,
        4,
        "share self receiver",
    );
    // A borrow self receiver only reads: a `borrow fn` parameter accepts it.
    single(
        &format!(
            "{methods}fn probe(f: borrow fn() -> i32) -> i32 {{ f() }}\nfn main() -> i32 {{ var l := Lane {{ width: 1 }}; l.widen(); probe(fn() => l.span()) }}\n"
        ),
        0,
        2,
        "borrow self receiver",
    );
    rejects(
        &format!(
            "{methods}fn probe(f: borrow fn()) {{ f(); }}\nfn main() -> i32 {{ var l := Lane {{ width: 1 }}; probe(fn() {{ l.widen(); }}); 0 }}\n"
        ),
        "TE017",
        "needs a `share fn` parameter",
    );
}

#[test]
fn mutation_through_a_nested_closure_propagates_outward() {
    single(
        "fn each(f: share fn(i32), n: i32) { loop i in 0..n { f(i); } }\nfn main() -> i32 { var t := 0; each(fn(i) { each(fn(j) { t += i + j; }, 2); }, 3); t }\n",
        0,
        9,
        "nested closure mutation",
    );
    // A middle literal that only passes the inner one on still mutates.
    rejects(
        "fn probe(f: borrow fn(i32), n: i32) { f(n); }\nfn each(f: share fn(i32), n: i32) { f(n); }\nfn main() -> i32 { var t := 0; probe(fn(i) { each(fn(j) { t += j; }, 2); }, 3); t }\n",
        "TE017",
        "needs a `share fn` parameter",
    );
}

#[test]
fn a_variable_mutated_only_outside_the_closure_is_a_read_capture() {
    // t is mutated before and after the closure, never inside it, so a
    // `borrow fn` parameter accepts the literal. 7 + 6 = 13.
    single(
        "fn probe(f: borrow fn(i32) -> i32, x: i32) -> i32 { f(x) }\nfn main() -> i32 { var t := 1; t += 4; let r := probe(fn(x) => x + t, 2); t += 1; r + t }\n",
        0,
        13,
        "read capture of a mutated variable",
    );
    // A parameter that shadows the outer name is not a capture at all.
    single(
        "fn each(f: share fn(i32), n: i32) { loop i in 0..n { f(i); } }\nfn main() -> i32 { var t := 0; each(fn(t: i32) { var u := t; u += 1; }, 3); t }\n",
        0,
        0,
        "shadowing parameter",
    );
}

#[test]
fn builtin_mutators_and_overwrites_make_share_captures() {
    single(
        r#"use alloc::List;
fn each(f: share fn(i32), n: i32) { loop i in 0..n { f(i); } }
fn main() -> i32 {
    var l: List<i32> = [];
    var s := "a".concat("");
    var t := 0;
    each(fn(i) { l.push(i); s.push_str("b"); t = i + 1; }, 3);
    each(fn(i) { l.clear(); }, 1);
    (l.len() as i32) + (s.len() as i32) + t
}
"#,
        0,
        7,
        "push, push_str, clear, overwrite",
    );
    single(
        r#"use alloc::List;
fn each(f: share fn(i32), n: i32) { loop i in 0..n { f(i); } }
fn main() -> i32 {
    let first := "ab".concat("");
    let second := "cde".concat("");
    var w: List<string> = [first, second];
    each(fn(i) { swap(w[0], w[1]); }, 3);
    var s := "q".concat("");
    each(fn(i) { let o := replace(s, "zz".concat("")); }, 2);
    (w[0].len() as i32) * 10 + (s.len() as i32)
}
"#,
        0,
        32,
        "swap and replace",
    );
    single(
        "fn bump(n: share i32) { n += 1; }\nfn each(f: share fn(i32), n: i32) { loop i in 0..n { f(i); } }\nfn main() -> i32 { var t := 0; each(fn(i) { bump(t.share()); }, 3); t }\n",
        0,
        3,
        "share argument",
    );
    single(
        "fn each(f: share fn(i32), n: i32) { loop i in 0..n { f(i); } }\nfn bump(n: share i32) { each(fn(i) { n += i; }, 3); }\nfn main() -> i32 { var t := 0; bump(t.share()); t }\n",
        0,
        3,
        "share parameter captured",
    );
}

#[test]
fn function_typed_captures_take_the_access_of_their_effect() {
    single(
        "fn each(f: share fn(i32), n: i32) { loop i in 0..n { f(i); } }\nfn twice(f: share fn(i32)) { each(fn(i) { f(i); f(i); }, 2); }\nfn main() -> i32 { var t := 0; twice(fn(i) { t += i + 1; }); t }\n",
        0,
        6,
        "share fn capture",
    );
    rejects(
        "fn each(f: borrow fn(i32), n: i32) { loop i in 0..n { f(i); } }\nfn twice(f: share fn(i32)) { each(fn(i) { f(i); }, 2); }\nfn main() -> i32 { 0 }\n",
        "TE017",
        "needs a `share fn` parameter",
    );
}
