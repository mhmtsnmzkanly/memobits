//! G1 limits: `if`/`match` owner values outside `replace`, struct literals as
//! function tail expressions, and nested `List<List<T>>`.
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
            "memobits-g1-limits-{}-{}",
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

const FORMS: &str = r#"use alloc::List;
type Label { text: string, n: u32 }
type Tok [ Word(string), Num(u32) ]
fn take(s: string) -> u32 { s.len() }
fn lit(c: bool) -> u32 {
    let s := if c { "a" } else { "bcd" };
    s.len()
}
fn chain(n: u32) -> u32 {
    let a := "aa".concat("");
    let b := "bbb".concat("");
    let c := "c".concat("");
    let o := if n == 0 { a } else if n == 1 { b } else { c };
    o.len()
}
fn nested(x: bool, y: bool) -> u32 {
    let a := "aa".concat("");
    let b := "bbb".concat("");
    let c := "c".concat("");
    let o := if x { if y { a } else { b } } else { c };
    o.len()
}
fn early(x: bool) -> u32 {
    let a := "aa".concat("");
    let b := "bbb".concat("");
    let o := if x { return 100; } else { a };
    let zz := "z".concat("");
    let p := if x { b } else { if !x { return 200; } zz };
    o.len() + p.len()
}
fn early2(x: bool) -> u32 {
    let a := "aa".concat("");
    let b := "bbb".concat("");
    let o := if x { a } else { b };
    if x { return 5; }
    o.len()
}
fn word(t: Tok) -> string {
    let z := "num".concat("!");
    match t { Word(w) => w, Num(n) => z }
}
fn tail(c: bool) -> string {
    let a := "abcd".concat("");
    let b := "xyz".concat("");
    if c { a } else { b }
}
fn ent(x: bool) -> Tok {
    let a := "aa".concat("");
    let b := "bbb".concat("");
    if x { Word(a) } else { Word(b) }
}
fn tl(x: bool) -> Label {
    let a := "aa".concat("");
    let b := "bbb".concat("");
    if x { Label { text: a, n: 1 } } else { Label { text: b, n: 2 } }
}
fn tl2(t: Tok) -> Label {
    let z := "zz".concat("");
    match t { Word(w) => Label { text: w, n: 1 }, Num(n) => Label { text: z, n: n } }
}
fn tup(x: bool) -> (string, u32) {
    let a := "aa".concat("");
    let b := "bbb".concat("");
    if x { (a, 1) } else { (b, 2) }
}
fn lst(c: bool) -> List<u32> {
    var a: List<u32> = [];
    a.push(1);
    var b: List<u32> = [];
    b.push(2);
    b.push(3);
    if c { a } else { b }
}
fn arg(l: Label, k: u32) -> u32 { l.text.len() + k }
fn tok_len(t: Tok) -> u32 { match t { Word(w) => w.len(), Num(n) => n } }
fn main() -> u32 {
    var r: u32 = lit(true) + lit(false) + chain(0) + chain(1) + chain(2);
    r += nested(true, true) + nested(true, false) + nested(false, true);
    r += early(true) + early(false) + early2(true) + early2(false);
    let w := "hello".concat("");
    r += take(word(Word(w))) + take(word(Num(1)));
    r += take(tail(true)) + take(tail(false));
    r += tok_len(ent(true)) + tok_len(ent(false));
    let l1 := tl(true);
    let l2 := tl2(Num(3));
    r += l1.text.len() + l2.n;
    let t := tup(false);
    r += t.0.len() + t.1;
    let a := "q".concat("qq");
    let b := "r".concat("");
    let c := r > 3;
    r += arg(if c { Label { text: a, n: 1 } } else { Label { text: b, n: 2 } }, 1);
    let x := "p".concat("q");
    let y := "r".concat("st");
    r += take(if c { x } else { y });
    var s := "s".concat("");
    let k := "k".concat("kkk");
    let z := "z".concat("");
    s = if c { k } else { z };
    r += s.len();
    let q := lst(false);
    r += q.len();
    r
}
"#;
const TAIL: &str = r#"type Label { text: string, n: u32 }
type Outer { inner: Label, k: u32 }
fn mk(s: string) -> Label { Label { text: s, n: 3 } }
fn mk2(s: string, t: string) -> Outer { Outer { inner: Label { text: s, n: 1 }, k: t.len() } }
fn rec(s: string) -> { name: string, n: u32 } { return { name: s, n: 4 }; }
fn early(s: string, c: bool) -> Label {
    if c { return Label { text: s, n: 1 }; }
    Label { text: s, n: 2 }
}
fn block_tail(s: string) -> Label { let t := s; { Label { text: t, n: 7 } } }
fn main() -> u32 {
    let a := "abc".concat("");
    let b := "de".concat("");
    let c := "f".concat("");
    let d := "gg".concat("");
    let e := "e".concat("");
    let f := "ff".concat("");
    let g := "g".concat("");
    let l := mk(a);
    let o := mk2(b, c);
    let r := rec(d);
    let x := early(e, true);
    let y := early(f, false);
    let z := block_tail(g);
    l.n + l.text.len() + o.inner.text.len() + o.k + r.name.len() + r.n
        + x.n + y.n + z.n + x.text.len() + y.text.len() + z.text.len()
}
"#;
const NESTED: &str = r#"use alloc::List;
fn fill(outer: share List<List<u32>>, n: u32) {
    var i: u32 = 0;
    loop {
        if i == n { break; }
        var inner: List<u32> = [];
        inner.push(i);
        inner.push(i + 1);
        outer.push(inner);
        i += 1;
    }
}
fn total(outer: borrow List<List<u32>>) -> u32 {
    var t: u32 = 0;
    loop row in outer {
        t += row.len();
        t += row[0];
    }
    t
}
fn row_sum(row: borrow List<u32>) -> u32 { row.len() + row[0] }
fn grow(row: share List<u32>) { row.push(8); }
fn make(n: u32) -> List<List<u32>> {
    var outer: List<List<u32>> = [];
    fill(outer.share(), n);
    outer
}
fn words() -> u32 {
    var w: List<List<string>> = [];
    var a: List<string> = [];
    let xyz := "x".concat("yz");
    a.push(xyz);
    w.push(a);
    w[0].push("q");
    var b: List<string> = [];
    b.push("hello");
    w.push(b);
    w[0].len() + w[1][0].len() + w[0][0].len()
}
fn main() -> u32 {
    var outer := make(10);
    var r: u32 = total(outer.borrow());
    outer[3].push(100);
    r += outer[3][2];
    match outer.pop() {
        Some(last) => { r += last.len(); }
        None => {}
    }
    r += outer.len();
    outer[0] = [5, 6, 7];
    r += outer[0].len();
    var extra: List<u32> = [1];
    let old := replace(outer[1], extra);
    r += old.len();
    outer[2].clear();
    r += outer[2].len();
    r += words();
    grow(outer[4].share());
    r += row_sum(outer[4].borrow()) + outer[4][2];
    match outer[4].get(2) { Some(v) => { r += v; } None => {} }
    if outer[4].contains(5) { r += 1; }
    outer[5][1] = 50;
    r += outer[5][1];
    outer.clear();
    r + outer.len()
}
"#;

#[test]
fn if_and_match_owner_values_work_in_every_position() {
    let f = Fixture::new();
    project(&f, "g1-forms", FORMS);
    run_source_and_wasm(
        &f,
        "g1-forms.wasm",
        b"Result: u32(367)\n",
        b"Result: i32(367)\n",
    );
}

#[test]
fn struct_literal_tail_expressions_work() {
    let f = Fixture::new();
    project(&f, "g1-tail", TAIL);
    run_source_and_wasm(
        &f,
        "g1-tail.wasm",
        b"Result: u32(29)\n",
        b"Result: i32(29)\n",
    );
}

#[test]
fn nested_lists_work_in_source_and_wasm() {
    let f = Fixture::new();
    project(&f, "g1-nested", NESTED);
    run_source_and_wasm(
        &f,
        "g1-nested.wasm",
        b"Result: u32(265)\n",
        b"Result: i32(265)\n",
    );
}

#[test]
fn if_and_match_owner_values_release_exactly_under_capped_memory() {
    let f = Fixture::new();
    let text = "x".repeat(TEXT_BYTES);
    project(
        &f,
        "g1-branches-stress",
        &r#"type Label { text: string, n: u32 }
type Tok [ Word(string), Num(u32) ]
fn take(s: string) -> u32 { s.len() }
fn s_if(flag: bool, c: bool) -> u32 {
    let a := "TEXT".concat("");
    let b := "TEXT".concat("");
    let o := if c { if flag { return 9; } a } else { b };
    o.len()
}
fn s_match(t: Tok) -> u32 {
    let z := "TEXT".concat("");
    let o := match t { Word(w) => w, Num(n) => z };
    o.len()
}
fn s_tail(c: bool) -> string {
    let a := "TEXT".concat("");
    let b := "TEXT".concat("");
    if c { a } else { b }
}
fn s_arg(c: bool) -> u32 {
    let a := "TEXT".concat("");
    let b := "TEXT".concat("");
    take(if c { a } else { b })
}
fn s_label(c: bool) -> u32 {
    let t1 := "TEXT".concat("");
    let t2 := "TEXT".concat("");
    let u := Label { text: t1, n: 1 };
    let v := Label { text: t2, n: 2 };
    let l := if c { u } else { v };
    l.n + l.text.len()
}
fn s_assign(c: bool) -> u32 {
    var s := "TEXT".concat("");
    let a := "TEXT".concat("");
    let b := "TEXT".concat("");
    s = if c { a } else { b };
    s.len()
}
fn s_early_arm(t: Tok) -> u32 {
    let z := "TEXT".concat("");
    let o := match t { Word(w) => { if w.len() > 5 { return 7; } w }, Num(n) => z };
    o.len()
}
fn mk(s: string) -> Label { Label { text: s, n: 3 } }
fn mk_early(s: string, c: bool) -> Label {
    if c { return Label { text: s, n: 1 }; }
    Label { text: s, n: 2 }
}
fn s_mk() -> u32 {
    let a := "TEXT".concat("");
    let l := mk(a);
    l.n + l.text.len()
}
fn s_mk_early(c: bool) -> u32 {
    let a := "TEXT".concat("");
    let l := mk_early(a, c);
    l.n + l.text.len()
}
fn s_inline(c: bool) -> u32 {
    let l := if c { Label { text: "TEXT".concat(""), n: 1 } } else { Label { text: "TEXT".concat(""), n: 2 } };
    l.n + l.text.len()
}
fn main() -> u32 {
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {
        if iteration == ITERATIONS { break; }
        total += s_inline(true) + s_inline(false);
        total += s_if(false, true) + s_if(false, false) + s_if(true, true) + s_if(true, false);
        let w1 := "TEXT".concat("");
        total += s_match(Word(w1)) + s_match(Num(1));
        total += take(s_tail(true)) + take(s_tail(false));
        total += s_arg(true) + s_arg(false);
        total += s_label(true) + s_label(false);
        total += s_assign(true) + s_assign(false);
        let w2 := "TEXT".concat("");
        total += s_early_arm(Word(w2)) + s_early_arm(Num(1));
        total += s_mk() + s_mk_early(true) + s_mk_early(false);
        iteration += 1;
    }
    total
}
"#
        .replace("TEXT", &text)
        .replace("ITERATIONS", &ITERATIONS.to_string()),
    );
    let t = TEXT_BYTES as u64;
    // s_if 3t+9; s_match 2t; s_tail 2t; s_arg 2t; s_label 3+2t; s_assign 2t;
    // s_early_arm 7+t; s_mk 3+t; s_mk_early 3+2t; s_inline 3+2t.
    let per_iteration = 19 * t + 28;
    assert_source_wasm_and_capped(
        &f,
        "g1-branches-stress.wasm",
        per_iteration * u64::from(ITERATIONS),
    );
}

#[test]
fn nested_lists_release_exactly_under_capped_memory() {
    let f = Fixture::new();
    let text = "x".repeat(TEXT_BYTES);
    project(
        &f,
        "g1-nested-stress",
        &r#"use alloc::List;
fn build(n: u32, flag: bool) -> u32 {
    var outer: List<List<u32>> = [];
    var i: u32 = 0;
    loop {
        if i == n { break; }
        var inner: List<u32> = [];
        var j: u32 = 0;
        loop {
            if j == 64 { break; }
            inner.push(j);
            j += 1;
        }
        outer.push(inner);
        i += 1;
    }
    outer[1].push(1000);
    if flag { return outer.len(); }
    var total: u32 = 0;
    match outer.pop() {
        Some(last) => { total += last.len(); }
        None => {}
    }
    outer[0] = [1, 2];
    let old := replace(outer[2], [5]);
    total += old.len();
    outer[3].clear();
    total + outer.len() + outer[1].len() + outer[0].len() + outer[2].len()
        + outer[3].len() + outer[1][64]
}
fn words(flag: bool) -> u32 {
    var w: List<List<string>> = [];
    var k: u32 = 0;
    loop {
        if k == 3 { break; }
        var row: List<string> = [];
        let a := "TEXT".concat("");
        row.push(a);
        w.push(row);
        w[k].push("lit");
        k += 1;
    }
    let extra := "TEXT".concat("");
    w[0].push(extra);
    if flag { return w.len(); }
    var total: u32 = 0;
    match w.pop() {
        Some(last) => { total += last.len(); }
        None => {}
    }
    total + w[1][0].len() + w[0].len() + w.len()
}
fn main() -> u32 {
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {
        if iteration == ITERATIONS { break; }
        total += build(6, true) + build(6, false) + words(true) + words(false);
        iteration += 1;
    }
    total
}
"#
        .replace("TEXT", &text)
        .replace("ITERATIONS", &ITERATIONS.to_string()),
    );
    let t = TEXT_BYTES as u64;
    // build(true) 6; build(false) 64 + 64 + 5 + 65 + 2 + 1 + 0 + 1000 = 1201;
    // words(true) 3; words(false) popped row 2 + t + 3 + 2 = t + 7.
    let per_iteration = 6 + 1201 + 3 + t + 7;
    assert_source_wasm_and_capped(
        &f,
        "g1-nested-stress.wasm",
        per_iteration * u64::from(ITERATIONS),
    );
}

#[test]
fn nested_list_misuse_is_rejected() {
    let f = Fixture::new();
    project(&f, "g1-nested-negatives", "fn main() -> u32 { 0 }");
    let wrap = |body: &str| format!("use alloc::List;\nfn main() -> u32 {{ {body} }}\n");
    rejects(
        &f,
        &wrap("let outer: List<List<u32>> = [[1]]; outer[0].push(2); 0"),
        "TE017",
        "push() requires a mutable List local",
    );
    rejects(
        &f,
        &wrap("var outer: List<List<u32>> = [[1]]; let r := outer[0]; 0"),
        "TE022",
        "cannot be moved out by indexing",
    );
    rejects(
        &f,
        &wrap("var outer: List<List<u32>> = [[1]]; outer.push(outer[0]); 0"),
        "TE022",
        "cannot be moved out by indexing",
    );
    rejects(
        &f,
        &wrap("var outer: List<List<u32>> = [[1]]; loop row in outer { outer[0].push(2); } 0"),
        "BE005",
        "cannot share this value while it is borrowed",
    );
    rejects(
        &f,
        &wrap("var outer: List<List<u32>> = [[1]]; var k: List<u32> = []; outer.push(k); k.push(1); 0"),
        "BE001",
        "unavailable after a move",
    );
    rejects(
        &f,
        "use alloc::List;\nfn add(outer: borrow List<List<u32>>) { outer[0].push(1); }\nfn main() -> u32 { 0 }\n",
        "TE017",
        "push() requires a mutable List local",
    );
    // Arrays of Lists and `Some(list)` are accepted since F2 (see f2_payloads).
}
