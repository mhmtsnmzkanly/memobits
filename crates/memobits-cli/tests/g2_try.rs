//! G2: divergence in branch values and `try ... else`.
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
            "memobits-g2-try-{}-{}",
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

const DIVERGE: &str = r#"use alloc::List;
type Label { text: string, n: u32 }
type Tok [ Word(string), Num(u32), Stop ]
fn prim(c: bool) -> u32 {
    let o: u32 = if c { 5 } else { return 7; };
    o
}
fn prim_first(c: bool) -> u32 {
    let o: u32 = if c { return 8; } else { 6 };
    o
}
fn a1(c: bool) -> u32 {
    let a := "aa".concat("");
    let o := if c { return 7; } else { a };
    o.len()
}
fn a2(c: bool) -> u32 {
    let a := "aa".concat("");
    let o := if c { a } else { return 7; };
    o.len()
}
fn m1(t: Tok) -> u32 {
    let w := match t { Word(s) => s, Num(n) => { return n; }, Stop => { return 99; } };
    w.len()
}
fn m2(t: Tok) -> u32 {
    let z: u32 = match t { Word(s) => s.len(), Num(n) => n, Stop => { return 99; } };
    z
}
fn m3(t: Tok) -> u32 {
    let z: u32 = match t { Stop => { return 1; }, Word(s) => s.len(), Num(n) => n };
    z
}
fn s1(c: bool) -> u32 {
    let l := Label { text: "q".concat("r"), n: 3 };
    let m := if c { l } else { return 8; };
    m.text.len() + m.n
}
fn l1(c: bool) -> u32 {
    var xs: List<u32> = [];
    xs.push(1);
    xs.push(2);
    let ys := if c { xs } else { return 4; };
    ys.len()
}
fn loops() -> u32 {
    var t: u32 = 0;
    var i: u32 = 0;
    loop {
        i += 1;
        let q := "x".concat("y");
        let s := if i < 3 { q } else if i < 6 { continue; } else { break; };
        t += s.len();
    }
    t
}
fn nested(x: bool, y: bool) -> u32 {
    let a := "aa".concat("");
    let o := if x { if y { a } else { return 1; } } else { return 2; };
    o.len()
}
fn blk(x: bool) -> u32 {
    let a := "aa".concat("");
    let o := if x { a } else { let z := "k".concat("k"); if z.len() > 0 { return 11; } else { return 12; } };
    o.len()
}
fn main() -> u32 {
    let w := "abc".concat("");
    prim(true) + prim(false) + prim_first(true) + prim_first(false) + m3(Stop) + m3(Num(4))
        + a1(false) + a2(true) + a2(false) + m1(Word(w)) + m1(Num(5)) + m2(Stop) + s1(true) + s1(false)
        + l1(true) + l1(false) + loops() + nested(true, true) + nested(true, false)
        + nested(false, true) + blk(true) + blk(false)
}
"#;

const RESULTS: &str = r#"fn parse(s: string) -> u32 ! Error {
    if s.len() == 0 { return Err(Error { code: 5 }); }
    Ok(s.len())
}
fn opt(n: u32) -> u32? { if n > 2 { Some(n) } else { None } }
fn a(s: string) -> u32 ! Error {
    let n := try parse(s) else e { return Err(e); };
    Ok(n + 1)
}
fn b(s: string) -> u32 {
    let n := try parse(s) else e { e.code };
    n
}
fn c(n: u32) -> u32 {
    let v := try opt(n) else { return 100; };
    v + 1
}
fn d() -> u32 {
    var x: u32 = 1;
    x = try opt(5);
    x = try opt(1);
    try opt(0);
    try parse("");
    x
}
fn ops() -> u32 {
    // A call argument, an arithmetic operand and a method receiver position.
    let n := 3 + try opt(4) else { 0 };
    let m := b("xy") + try opt(9) else { 1 };
    n + m
}
fn main() -> u32 ! Error {
    let r := try a("abc") else e { return Err(e); };
    Ok(r + b("") + c(1) + c(3) + d() + ops())
}
"#;

const HEAP: &str = r#"type Label { text: string, n: u32 }
type NameError: Error { why: u32 }
fn mk(n: u32) -> string ! NameError {
    let s := "ab".concat("cd");
    if n == 0 { return Err(NameError { code: 7, why: 3 }); }
    Ok(s)
}
fn lab(n: u32) -> Label ! NameError {
    let s := "ab".concat("cd");
    if n == 0 { return Err(NameError { code: 7, why: 3 }); }
    let l := Label { text: s, n: n };
    Ok(l)
}
fn a(n: u32) -> u32 {
    let s := try mk(n) else e { return e.why + 100; };
    s.len()
}
fn b(n: u32) -> u32 {
    let l := try lab(n) else e { return e.code; };
    l.text.len() + l.n
}
fn c(n: u32) -> u32 {
    let l := try lab(n) else { let z := "z".concat("z"); Label { text: z, n: 1 } };
    l.text.len() + l.n
}
fn d(n: u32) -> u32 {
    var s := "init".concat("");
    s = try mk(n);
    try lab(n);
    s.len()
}
fn main() -> u32 {
    a(0) + a(1) + b(0) + b(3) + c(0) + c(2) + d(0) + d(1)
}
"#;

const MIX: &str = r#"fn pm(n: u32) -> u32? ! Error {
    if n == 0 { return Err(Error { code: 9 }); }
    if n == 1 { return Ok(None); }
    Ok(Some(n))
}
fn so(n: u32) -> string? {
    if n == 0 { return None; }
    let s := "hi".concat("!");
    Some(s)
}
fn first(n: u32) -> u32? { if n > 5 { None } else { Some(n) } }
fn t1(n: u32) -> u32 {
    let o := try pm(n) else e { return e.code; };
    match o { Some(v) => v, None => 50 }
}
fn t3(n: u32) -> u32 {
    let s := try so(n) else { return 1; };
    s.len()
}
fn t5(n: u32) -> u32 {
    let a := try so(n) else { return 0; };
    let b := try so(n + 1) else { return 1; };
    a.len() + b.len()
}
fn t6() -> u32 {
    var total: u32 = 0;
    var i: u32 = 0;
    loop {
        i += 1;
        if i > 12 { break; }
        let s := try so(i % 3) else { continue; };
        let m := try pm(i % 4) else e { if e.code == 9 { continue; } else { break; } };
        total += s.len();
        match m { Some(x) => { total += x; } None => { total += 1; } }
    }
    total
}
fn t7(n: u32) -> u32 {
    let o := try pm(try first(n) else { return 5; }) else e { return e.code; };
    match o { Some(v) => v + 10, None => 20 }
}
fn main() -> u32 {
    t1(0) + t1(1) + t1(5) + t3(0) + t3(1) + t5(0) + t5(1) + t6() + t7(9) + t7(0) + t7(1) + t7(3)
}
"#;

const STRESS: &str = r#"type Label { text: string, n: u32 }
type NameError: Error { why: u32 }
fn mk(n: u32) -> string ! NameError {
    let s := "TEXT".concat("");
    if n % 3 == 0 { return Err(NameError { code: 7, why: 5 }); }
    Ok(s)
}
fn lab(n: u32) -> Label ! NameError {
    let s := "TEXT".concat("");
    if n % 3 == 0 { return Err(NameError { code: 7, why: 5 }); }
    let l := Label { text: s, n: n };
    Ok(l)
}
fn so(n: u32) -> string? {
    if n % 3 == 0 { return None; }
    let s := "TEXT".concat("");
    Some(s)
}
fn h_ret(n: u32) -> u32 {
    let s := try mk(n) else e { return e.why + 1000; };
    s.len()
}
fn h_val(n: u32) -> u32 {
    let s := try mk(n) else { let z := "TEXT".concat(""); z };
    s.len()
}
fn h_disc(n: u32) -> u32 {
    try mk(n);
    try so(n);
    1
}
fn h_assign(n: u32) -> u32 {
    var s := "TEXT".concat("");
    s = try mk(n);
    s.len()
}
fn h_lab(n: u32) -> u32 {
    let l := try lab(n) else e { return e.code; };
    l.text.len() + l.n
}
fn h_opt(n: u32) -> u32 {
    let s := try so(n) else { return 2; };
    s.len()
}
fn h_loop() -> u32 {
    var total: u32 = 0;
    var i: u32 = 0;
    loop {
        i += 1;
        if i > 6 { break; }
        let s := try mk(i) else e { continue; };
        total += s.len();
    }
    total
}
fn h_brk() -> u32 {
    var total: u32 = 0;
    var i: u32 = 0;
    loop {
        i += 1;
        let s := try mk(i) else e { break; };
        total += s.len();
    }
    total
}
fn h_nested(n: u32) -> u32 {
    let a := try mk(n) else { return 1; };
    let l := try lab(n + 1) else e { return e.code; };
    a.len() + l.text.len() + l.n
}
fn main() -> u32 {
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {
        if iteration == ITERATIONS { break; }
        total += h_ret(1) + h_ret(3);
        total += h_val(1) + h_val(3);
        total += h_disc(1) + h_disc(3);
        total += h_assign(1) + h_assign(3);
        total += h_lab(1) + h_lab(3);
        total += h_opt(1) + h_opt(3);
        total += h_loop() + h_brk();
        total += h_nested(1) + h_nested(2) + h_nested(3);
        iteration += 1;
    }
    total
}
"#;

#[test]
fn diverging_branches_join_with_any_type() {
    let f = Fixture::new();
    project(&f, "g2-diverge", DIVERGE);
    run_source_and_wasm(
        &f,
        "g2-diverge.wasm",
        b"Result: u32(190)\n",
        b"Result: i32(190)\n",
    );
}

#[test]
fn try_else_on_results_and_options() {
    let f = Fixture::new();
    project(&f, "g2-results", RESULTS);
    run_source_and_wasm(
        &f,
        "g2-results.wasm",
        b"Result: Ok(u32(136))\n",
        b"Result: Ok(u32(136))\n",
    );
}

#[test]
fn try_else_moves_heap_payloads() {
    let f = Fixture::new();
    project(&f, "g2-heap", HEAP);
    run_source_and_wasm(
        &f,
        "g2-heap.wasm",
        b"Result: u32(138)\n",
        b"Result: i32(138)\n",
    );
}

#[test]
fn try_else_nested_and_in_loops() {
    let f = Fixture::new();
    project(&f, "g2-mix", MIX);
    run_source_and_wasm(
        &f,
        "g2-mix.wasm",
        b"Result: u32(151)\n",
        b"Result: i32(151)\n",
    );
}

#[test]
fn try_release_heap_payloads_exactly_under_capped_memory() {
    let f = Fixture::new();
    let text = "x".repeat(TEXT_BYTES);
    project(
        &f,
        "g2-try-stress",
        &STRESS
            .replace("TEXT", &text)
            .replace("ITERATIONS", &ITERATIONS.to_string()),
    );
    let t = TEXT_BYTES as u64;
    // h_ret t+1005; h_val 2t; h_disc 2; h_assign 2t; h_lab t+8; h_opt t+2;
    // h_loop 4t; h_brk 2t; h_nested (2t+2)+7+1.
    let per_iteration = 15 * t + 1027;
    assert_source_wasm_and_capped(
        &f,
        "g2-try-stress.wasm",
        per_iteration * u64::from(ITERATIONS),
    );
}

#[test]
fn try_and_divergence_misuse_is_rejected() {
    let f = Fixture::new();
    project(&f, "g2-negatives", "fn main() -> u32 { 0 }");
    let wrap = |body: &str| {
        format!(
            "fn r() -> u32 ! Error {{ Ok(1) }}\nfn o() -> u32? {{ Some(1) }}\nfn g() -> u32 {{ {body} }}\nfn main() -> u32 {{ g() }}\n"
        )
    };
    rejects(
        &f,
        &wrap("let x := try r() else e { \"no\" }; x"),
        "TE013",
        "`try` handler must produce u32 or exit",
    );
    rejects(
        &f,
        &wrap("let x := try r() else e { e }; x"),
        "TE013",
        "`try` handler must produce u32 or exit",
    );
    rejects(
        &f,
        &wrap("let x := try o() else e { 0 }; x"),
        "TE030",
        "has no error to bind",
    );
    rejects(
        &f,
        &wrap("let x := try 5 else { 0 }; x"),
        "TE029",
        "`try` requires a `T ! E` or `T?` value, found i32",
    );
    rejects(
        &f,
        "type S [A, B]\nfn g(s: S) -> u32 { let x := try s else { 0 }; x }\nfn main() -> u32 { 0 }\n",
        "TE029",
        "`try` requires a `T ! E` or `T?` value, found S",
    );
    rejects(
        &f,
        &wrap("let x := try r(); x"),
        "SE002",
        "`try` needs `else`",
    );
    rejects(&f, &wrap("try r()"), "SE002", "`try` needs `else`");
    rejects(
        &f,
        &wrap("if try r() { 1 } else { 2 }"),
        "SE002",
        "`try` needs `else`",
    );
    rejects(
        &f,
        &wrap("var x: u32 = 0; x += try r(); x"),
        "SE002",
        "supports only plain `=` assignment",
    );
    rejects(
        &f,
        &wrap("let x := try r() else { let q := 1; }; x"),
        "TE013",
        "`try` handler must produce u32",
    );
    rejects(
        &f,
        "fn take(s: string) -> string ! Error { Ok(s) }\nfn main() -> u32 { var s := \"ab\".concat(\"\"); s = try take(s); s.len() }\n",
        "BE001",
        "unavailable after a move",
    );
    // A diverging branch joins with any type, but real mismatches remain.
    rejects(
        &f,
        &wrap("let x := if true { \"a\" } else { 1 }; 0"),
        "TE013",
        "if branches have incompatible types",
    );
    rejects(
        &f,
        &wrap("let x := match o() { Some(v) => \"a\", None => 1 }; 0"),
        "TE013",
        "match arms have incompatible types",
    );
}
