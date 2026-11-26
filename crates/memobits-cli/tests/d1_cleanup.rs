//! D1 cleanup: Error-ancestry diagnostic, direct owner temporaries as call
//! arguments, `replace` with `if`/`match` values, the swap overlap note and
//! mixed String/owner-array struct literals.
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
            "memobits-d1-cleanup-{}-{}",
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

#[test]
fn error_derived_types_report_a_dedicated_string_ownership_message() {
    let f = Fixture::new();
    project(&f, "d1-error-ancestry", "fn main() -> u32 { 0 }");
    for (source, name) in [
        (
            "type Label { text: string } type Failure: Error { l: Label } fn main() {}",
            "Failure",
        ),
        (
            "type Failure: Error { text: string } fn main() {}",
            "Failure",
        ),
        (
            "type Label { text: string } type Failure: Error { items: array<Label, 2> } fn main() {}",
            "Failure",
        ),
    ] {
        rejects(
            &f,
            source,
            "LE900",
            &format!("Error-derived type '{name}' cannot own heap Strings yet"),
        );
    }
}

#[test]
fn owner_temporaries_move_into_owned_call_arguments() {
    let f = Fixture::new();
    project(
        &f,
        "d1-direct-temporaries",
        r#"type Label { text: string, n: u32 }
type Outer { inner: Label, k: u32 }
fn take(l: Label) -> u32 { l.n + l.text.len() }
fn take_outer(o: Outer) -> u32 { o.k + o.inner.text.len() }
fn take_arr(a: array<Label, 2>) -> u32 { a[0].n + a[1].text.len() }
fn take_str(s: string) -> u32 { s.len() }
fn take_rec(r: { name: string, n: u32 }) -> u32 { r.name.len() + r.n }
fn make(s: string) -> Label { let l := Label { text: s, n: 3 }; l }
fn main() -> u32 {
    let rs := "ab".concat("c");
    let rec := take_rec({ name: rs, n: 4 }) + take_rec({ name: "lit", n: 1 });
    let s := "ab".concat("c");
    let a := take(Label { text: s, n: 1 });
    let t := "xy".concat("z");
    let b := take(make(t));
    let u := "uu".concat("u");
    let c := take_outer(Outer { inner: Label { text: u, n: 2 }, k: 5 });
    let v := "v".concat("vvv");
    let w := "w".concat("w");
    let d := take_arr([Label { text: v, n: 1 }, Label { text: w, n: 2 }]);
    let e := take_str("a".concat("bcd"));
    let lit := take(Label { text: "lit", n: 4 });
    a + b + c + d + e + lit + rec
}
"#,
    );
    // a 1+3, b 3+3, c 5+3, d 1+2, e 4, lit 4+3, rec (3+4)+(3+1)
    run_source_and_wasm(
        &f,
        "d1-direct.wasm",
        b"Result: u32(43)\n",
        b"Result: i32(43)\n",
    );
}

#[test]
fn direct_owner_temporaries_release_exactly_under_capped_memory() {
    let f = Fixture::new();
    let text = "x".repeat(TEXT_BYTES);
    project(
        &f,
        "d1-temporaries-stress",
        &r#"type Label { text: string, n: u32 }
type Outer { inner: Label, k: u32 }
fn take(l: Label) -> u32 { l.n + l.text.len() }
fn take_outer(o: Outer) -> u32 { o.k + o.inner.text.len() }
fn take2(l: Label, extra: string) -> u32 { l.n + extra.len() }
fn take_arr(a: array<Label, 2>) -> u32 { a[0].n + a[1].text.len() }
fn make(s: string) -> Label { let l := Label { text: s, n: 3 }; l }
fn direct(flag: bool) -> u32 {
    let t1 := "TEXT".concat("");
    let r1 := take(Label { text: t1, n: 1 });
    let t2 := "TEXT".concat("");
    let r2 := take(make(t2));
    let t3 := "TEXT".concat("");
    let r3 := take_outer(Outer { inner: Label { text: t3, n: 2 }, k: 5 });
    let t4 := "TEXT".concat("");
    let t5 := "TEXT".concat("");
    let r4 := take2(Label { text: t4, n: 7 }, t5);
    if flag { return 1; }
    r1 + r2 + r3 + r4
}
fn late(flag: bool) -> u32 {
    let t4 := "TEXT".concat("");
    let t5 := "TEXT".concat("");
    take2(Label { text: t4, n: 7 }, { if flag { return 2; } t5 })
}
fn arrays() -> u32 {
    let t1 := "TEXT".concat("");
    let t2 := "TEXT".concat("");
    take_arr([Label { text: t1, n: 1 }, Label { text: t2, n: 2 }])
}
fn main() -> u32 {
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {
        if iteration == ITERATIONS { break; }
        total += direct(true);
        total += direct(false);
        total += late(true);
        total += late(false);
        total += arrays();
        iteration += 1;
    }
    total
}
"#
        .replace("TEXT", &text)
        .replace("ITERATIONS", &ITERATIONS.to_string()),
    );
    let t = TEXT_BYTES as u64;
    // direct(true) 1; direct(false) (t+1)+(t+3)+(t+5)+(7+t); late(true) 2;
    // late(false) 7+t; arrays 1+t.
    let per_iteration = 1 + (4 * t + 16) + 2 + (7 + t) + (1 + t);
    assert_source_wasm_and_capped(
        &f,
        "d1-temporaries.wasm",
        per_iteration * u64::from(ITERATIONS),
    );
}

#[test]
fn replace_accepts_if_and_match_values_for_owners() {
    let f = Fixture::new();
    project(
        &f,
        "d1-replace-branches",
        r#"type Label { text: string, n: u32 }
type Tok [ Word(string), Num(u32) ]
fn pick(c: bool, d: bool) -> u32 {
    var s := "a".concat("b");
    let a := "x".concat("y");
    let b := "p".concat("qq");
    let e := "k".concat("kkk");
    let o := replace(s, if c { a } else if d { b } else { e });
    s.len() * 10 + o.len()
}
fn tok(t: Tok) -> u32 {
    var s := "a".concat("b");
    let o := replace(s, match t { Word(w) => w, Num(n) => { let z := "n".concat("nn"); z } });
    s.len() * 10 + o.len()
}
fn block_tail(c: bool) -> u32 {
    var s := "a".concat("b");
    let b := "w".concat("wwww");
    let o := replace(s, if c { let z := "n".concat("nn"); z } else { b });
    s.len() * 10 + o.len()
}
fn label(c: bool) -> u32 {
    var l := Label { text: "q".concat("q"), n: 1 };
    let t := "z".concat("zz");
    let u := Label { text: t, n: 2 };
    let t2 := "m".concat("mmmm");
    let v := Label { text: t2, n: 3 };
    let old := replace(l, if c { u } else { v });
    l.n * 100 + old.n
}
fn element(c: bool) -> u32 {
    let a := "a".concat("a");
    let b := "b".concat("bb");
    var items: array<string, 2> = [a, b];
    let x := "x".concat("xxx");
    let y := "y".concat("yyyyy");
    let old := replace(items[1], if c { x } else { y });
    items[0].len() * 100 + items[1].len() * 10 + old.len()
}
fn main() -> u32 {
    let hx := "hello".concat("x");
    pick(true, false) + pick(false, true) + pick(false, false)
        + tok(Word(hx)) + tok(Num(1))
        + block_tail(true) + block_tail(false)
        + label(true) + label(false)
        + element(true) + element(false)
}
"#,
    );
    // pick 22+32+42, tok 62+32, block_tail 32+52, label 201+301,
    // element 243+263 (items[0] is 2 bytes, the old element 3 bytes, the new
    // element 4 or 6 bytes).
    let expected: u32 = 22 + 32 + 42 + 62 + 32 + 32 + 52 + 201 + 301 + 243 + 263;
    run_source_and_wasm(
        &f,
        "d1-branches.wasm",
        format!("Result: u32({expected})\n").as_bytes(),
        format!("Result: i32({expected})\n").as_bytes(),
    );
}

#[test]
fn replace_with_branch_values_releases_exactly_under_capped_memory() {
    let f = Fixture::new();
    let text = "x".repeat(TEXT_BYTES);
    project(
        &f,
        "d1-branches-stress",
        &r#"type Label { text: string, n: u32 }
type Tok [ Word(string), Num(u32) ]
fn rep_if(flag: bool, c: bool) -> u32 {
    var s := "TEXT".concat("");
    let a := "TEXT".concat("");
    let b := "TEXT".concat("");
    let old := replace(s, if c { if flag { return 9; } a } else { b });
    s.len() + old.len()
}
fn rep_block(c: bool) -> u32 {
    var s := "TEXT".concat("");
    let b := "TEXT".concat("");
    let old := replace(s, if c { let q := "TEXT".concat(""); q } else { b });
    s.len() + old.len()
}
fn rep_match(t: Tok) -> u32 {
    var s := "TEXT".concat("");
    let z := "TEXT".concat("");
    let old := replace(s, match t { Word(w) => w, Num(n) => z });
    s.len() + old.len()
}
fn rep_label(c: bool) -> u32 {
    let t0 := "TEXT".concat("");
    var l := Label { text: t0, n: 1 };
    let t1 := "TEXT".concat("");
    let u := Label { text: t1, n: 2 };
    let t2 := "TEXT".concat("");
    let v := Label { text: t2, n: 3 };
    let old := replace(l, if c { u } else { v });
    l.n * 10 + old.n + l.text.len() + old.text.len()
}
fn rep_elem(c: bool) -> u32 {
    let a := "TEXT".concat("");
    let b := "TEXT".concat("");
    var items: array<string, 2> = [a, b];
    let x := "TEXT".concat("");
    let y := "TEXT".concat("");
    let old := replace(items[1], if c { x } else { y });
    items[0].len() + items[1].len() + old.len()
}
fn main() -> u32 {
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {
        if iteration == ITERATIONS { break; }
        total += rep_if(false, true);
        total += rep_if(false, false);
        total += rep_if(true, true);
        total += rep_if(true, false);
        total += rep_block(true);
        total += rep_block(false);
        let w := "TEXT".concat("");
        total += rep_match(Word(w));
        total += rep_match(Num(1));
        total += rep_label(true);
        total += rep_label(false);
        total += rep_elem(true);
        total += rep_elem(false);
        iteration += 1;
    }
    total
}
"#
        .replace("TEXT", &text)
        .replace("ITERATIONS", &ITERATIONS.to_string()),
    );
    let t = TEXT_BYTES as u64;
    // rep_if: 2t + 2t + 9 + 2t; rep_block 2t each; rep_match 2t each;
    // rep_label (10*... ): true 20+1+2t, false 30+1+2t; rep_elem 3t each.
    let per_iteration = (2 * t) * 3 + 9 + 4 * t + 4 * t + (21 + 2 * t) + (31 + 2 * t) + 6 * t;
    assert_source_wasm_and_capped(
        &f,
        "d1-branches-stress.wasm",
        per_iteration * u64::from(ITERATIONS),
    );
}

#[test]
fn swap_overlap_diagnostic_explains_disjoint_places() {
    let f = Fixture::new();
    project(&f, "d1-swap-note", "fn main() -> u32 { 0 }");
    let prelude = "fn main() -> u32 {\n    let a := \"x\".concat(\"y\");\n    let b := \"p\".concat(\"q\");\n    var items: array<string, 2> = [a, b];\n    let i: u32 = 0;\n    let j: u32 = 1;\n";
    for call in ["swap(items[i], items[j])", "swap(items[0], items[0])"] {
        rejects(
            &f,
            &format!("{prelude}    {call};\n    1\n}}"),
            "BE005",
            "swap needs two disjoint places; dynamic indices into the same collection are not provably disjoint",
        );
    }
    // A plain overlapping loan outside swap gets no swap note.
    f.write(
        "src/main.mb",
        &format!("{prelude}    let r := items[i].borrow();\n    items[j] = \"z\".concat(\"z\");\n    r.len()\n}}"),
    );
    let check = f.run(&["check"]);
    assert!(!String::from_utf8_lossy(&check.stderr).contains("swap needs two disjoint places"));
}

#[test]
fn struct_literals_mix_string_and_owner_fields() {
    let f = Fixture::new();
    project(
        &f,
        "d1-mixed-literal",
        r#"type Label { text: string, n: u32 }
type Bag { name: string, items: array<Label, 2>, inner: Label, k: u32 }
fn main() -> u32 {
    let n := "bag".concat("1");
    let t1 := "a".concat("b");
    let t2 := "c".concat("dd");
    let t3 := "e".concat("eee");
    let l1 := Label { text: t1, n: 1 };
    let l2 := Label { text: t2, n: 2 };
    let l3 := Label { text: t3, n: 3 };
    let b := Bag { name: n, items: [l1, l2], inner: l3, k: 7 };
    b.k + b.name.len() + b.items[1].n + b.inner.text.len()
}
"#,
    );
    run_source_and_wasm(
        &f,
        "d1-mixed.wasm",
        b"Result: u32(17)\n",
        b"Result: i32(17)\n",
    );
}

#[test]
fn mixed_struct_literals_release_exactly_under_capped_memory() {
    let f = Fixture::new();
    let text = "x".repeat(TEXT_BYTES);
    project(
        &f,
        "d1-mixed-stress",
        &r#"type Label { text: string, n: u32 }
type Pair { first: Label, second: Label }
type Bag { name: string, items: array<Label, 2>, inner: Label, k: u32 }
type Duo { head: string, pair: Pair }
fn mix(flag: bool) -> u32 {
    let n := "TEXT".concat("");
    let t1 := "TEXT".concat("");
    let t2 := "TEXT".concat("");
    let t3 := "TEXT".concat("");
    let l1 := Label { text: t1, n: 1 };
    let l2 := Label { text: t2, n: 2 };
    let l3 := Label { text: t3, n: 3 };
    let b := Bag { name: n, items: [l1, l2], inner: l3, k: 7 };
    if flag { return 1; }
    b.k + b.name.len() + b.items[1].n + b.inner.text.len() + b.items[0].text.len()
}
fn mix_late(flag: bool) -> u32 {
    let n := "TEXT".concat("");
    let t1 := "TEXT".concat("");
    let t2 := "TEXT".concat("");
    let t3 := "TEXT".concat("");
    let l1 := Label { text: t1, n: 1 };
    let l2 := Label { text: t2, n: 2 };
    let l3 := Label { text: t3, n: 3 };
    let b := Bag { name: n, items: [l1, l2], inner: { if flag { return 3; } l3 }, k: 7 };
    b.k + b.name.len() + b.items[1].n + b.inner.text.len() + b.items[0].text.len()
}
fn duo(flag: bool) -> u32 {
    let h := "TEXT".concat("");
    let t1 := "TEXT".concat("");
    let t2 := "TEXT".concat("");
    let f := Label { text: t1, n: 1 };
    let s := Label { text: t2, n: 2 };
    let d := Duo { head: h, pair: Pair { first: f, second: s } };
    if flag { return 4; }
    d.head.len() + d.pair.first.n + d.pair.second.text.len()
}
fn main() -> u32 {
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {
        if iteration == ITERATIONS { break; }
        total += mix(true);
        total += mix(false);
        total += mix_late(true);
        total += mix_late(false);
        total += duo(true);
        total += duo(false);
        iteration += 1;
    }
    total
}
"#
        .replace("TEXT", &text)
        .replace("ITERATIONS", &ITERATIONS.to_string()),
    );
    let t = TEXT_BYTES as u64;
    // mix(false) = 7 + 2 + 3t; duo(false) = t + 1 + t.
    let per_iteration = 1 + (9 + 3 * t) + 3 + (9 + 3 * t) + 4 + (1 + 2 * t);
    assert_source_wasm_and_capped(
        &f,
        "d1-mixed-stress.wasm",
        per_iteration * u64::from(ITERATIONS),
    );
}
