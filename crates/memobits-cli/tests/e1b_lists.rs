//! E1b: general `List<T>`. Primitives of every width, `string`, owner structs,
//! enums, tuples and arrays as elements; non-empty list literals; `items[i]`
//! element places; `pop`/`clear`/growth cleanup; `loop` lending; capped-memory
//! stress and the rejected neighbours.
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
            "memobits-e1b-lists-{}-{}",
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

#[test]
fn primitive_lists_of_every_width_work_in_source_and_wasm() {
    let f = Fixture::new();
    project(
        &f,
        "e1b-primitives",
        r#"use alloc::List;
fn sum_borrowed(items: borrow List<u16>) -> u32 {
    var total: u32 = 0;
    loop x in items { total += x as u32; }
    total + items[0] as u32
}
fn main() -> u32 {
    var a: List<u8> = [1, 2, 3];
    var b: List<u16> = [10, 20];
    var c: List<u64> = [5_000_000_000];
    var d: List<i8> = [-1, 2];
    var e: List<i64> = [];
    var g: List<f64> = [1.5, 2.5];
    var h: List<bool> = [true, false];
    var k: List<char> = ['a'];
    a.push(4);
    b.push(30);
    c.push(7);
    d.push(-3);
    e.push(-9);
    h.push(true);
    k.push('z');
    let i: u32 = 1;
    b[i] = 21;
    a[0] += 9;
    let r1: u32 = a[0] as u32 + a[3] as u32 + sum_borrowed(b.borrow());
    let r2: u32 = if c[0] == 5_000_000_000 && d[2] == -3 && e[0] == -9 { 100 } else { 0 };
    let r3: u32 = if h[0] && !h[1] && h[2] && k[1] == 'z' { 1000 } else { 0 };
    let r4: u32 = (g[0] + g[1]) as u32;
    let got: u8 = match a.get(1) { Some(v) => v, None => 0 };
    let last: i64 = match e.pop() { Some(v) => v, None => 0 };
    let gone: u32 = match e.pop() { Some(_) => 1, None => 0 };
    let found: u32 = if a.contains(3) { 10000 } else { 0 };
    let at: u32 = match a.index_of(4) { Some(p) => p, None => 99 };
    r1 + r2 + r3 + r4 + got as u32 + (last + 9) as u32 + gone + found + at
}
"#,
    );
    // r1 = 10 + 4 + (10 + 21 + 30 + 10) = 85, r2 = 100, r3 = 1000, r4 = 4,
    // got = 2, last + 9 = 0, gone = 0, found = 10000, at = 3.
    run_source_and_wasm(
        &f,
        "e1b-primitives.wasm",
        b"Result: u32(11194)\n",
        b"Result: i32(11194)\n",
    );
}

#[test]
fn owner_element_lists_work_in_source_and_wasm() {
    let f = Fixture::new();
    project(
        &f,
        "e1b-owners",
        r#"use alloc::List;
type Label { text: string, n: u32 }
type Tok [ Word(string), Num(u32) ]
fn size_of(s: borrow string) -> u32 { s.len() }
fn label_len(l: borrow Label) -> u32 { l.text.len() + l.n }
fn total_len(items: borrow List<string>) -> u32 {
    var t: u32 = 0;
    loop w in items { t += w.len(); }
    t + items[0].len() + items.len()
}
fn add(items: share List<string>, s: string) { items.push(s); }
fn take(items: List<string>) -> u32 { items.len() + items[1].len() }
fn make() -> List<string> {
    let a := "pp".concat("q");
    let items: List<string> = [a, "z"];
    items
}
fn early(flag: bool) -> u32 {
    let a := "pp".concat("q");
    var items: List<string> = [a];
    items.push("k");
    if flag { return 1; }
    items.clear();
    items.push("m");
    items.len()
}
fn main() -> u32 {
    var words: List<string> = make();
    let wx := "wxyz".concat("");
    add(words.share(), wx);
    let r1 := total_len(words.borrow()) + size_of(words[2].borrow());
    let r2 := take(words);
    let r3 := early(true) + early(false);
    let abcd := "abcd".concat("");
    let toks: List<Tok> = [Tok::Word(abcd), Tok::Num(5)];
    let r4 := match toks[0] { Tok::Word(x) => x.len(), Tok::Num(n) => n }
        + match toks[1] { Tok::Word(x) => x.len(), Tok::Num(n) => n };
    var ls: List<Label> = [];
    let ab := "ab".concat("");
    ls.push(Label { text: ab, n: 1 });
    let hello := "hello".concat("");
    ls.push(Label { text: hello, n: 2 });
    let r5 := ls[1].text.len() + label_len(ls[0].borrow());
    var total: u32 = 0;
    loop l in ls { total += l.text.len() + l.n; }
    let popped := ls.pop();
    let r6: u32 = match popped { Some(l) => l.text.len() + l.n, None => 0 };
    let again := ls.pop();
    let r7: u32 = match again { Some(l) => l.n, None => 100 };
    let none := ls.pop();
    let r8: u32 = match none { Some(l) => l.n, None => 1000 };
    let rows: List<array<u32, 2>> = [[1, 2], [3, 4]];
    let r9 := rows[1][0] + rows[0][1];
    r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + total + r9
}
"#,
    );
    // words = [ppq, z, wxyz]: total_len = 8 + 3 + 3, plus size_of(words[2]) = 4
    // gives r1 = 18; r2 = 3 + 1 = 4; r3 = 1 + 1 = 2; r4 = 4 + 5 = 9; r5 = 5 + 3 = 8;
    // total = 3 + 7 = 10; r6 = 7; r7 = 1; r8 = 1000; r9 = 5.
    run_source_and_wasm(
        &f,
        "e1b-owners.wasm",
        b"Result: u32(1064)\n",
        b"Result: i32(1064)\n",
    );
}

#[test]
fn string_lists_release_on_normal_and_early_returns_under_a_memory_cap() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 512;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    project(
        &f,
        "e1b-lists-stress",
        &format!(
            r#"use alloc::List;
type Label {{ text: string, n: u32 }}
type Tok [ Word(string), Num(u32) ]
fn consume(words: List<string>, flag: bool) -> u32 {{
    let extra := "{text}".concat("");
    if flag {{ return 1; }}
    words[0].len() + words.len() + extra.len() - extra.len()
}}
fn caller(flag: bool) -> u32 {{
    let a := "{text}".concat("");
    let b := "{text}".concat("");
    let words: List<string> = [a, b];
    if flag {{ return 7; }}
    consume(words, false)
}}
fn grow(flag: bool) -> u32 {{
    var items: List<string> = [];
    var i: u32 = 0;
    loop {{
        if i == 8 {{ break; }}
        let s := "{text}".concat("");
        items.push(s);
        if flag && i == 4 {{ return 2; }}
        i += 1;
    }}
    items.len() + items[7].len()
}}
fn popped(flag: bool) -> u32 {{
    var items: List<string> = [];
    let a := "{text}".concat("");
    let b := "{text}".concat("");
    items.push(a);
    items.push(b);
    let last := items.pop();
    if flag {{ return 3; }}
    let n: u32 = match last {{ Some(s) => s.len(), None => 0 }};
    items.clear();
    n + items.len()
}}
fn discarded() -> u32 {{
    var items: List<string> = [];
    let a := "{text}".concat("");
    items.push(a);
    let dropped := items.pop();
    5
}}
fn reassign(flag: bool) -> u32 {{
    let a := "{text}".concat("");
    var items: List<string> = [a];
    let b := "{text}".concat("");
    let c := "{text}".concat("");
    items = [b, c];
    if flag {{ return 4; }}
    items.len()
}}
fn make() -> List<string> {{
    let a := "{text}".concat("");
    let items: List<string> = [a, "lit"];
    items
}}
fn returned(flag: bool) -> u32 {{
    let made := make();
    if flag {{ return 6; }}
    made.len()
}}
fn labels(flag: bool) -> u32 {{
    var items: List<Label> = [];
    var i: u32 = 0;
    loop {{
        if i == 6 {{ break; }}
        let t := "{text}".concat("");
        items.push(Label {{ text: t, n: i }});
        i += 1;
    }}
    if flag {{ return 8; }}
    var total: u32 = 0;
    loop l in items {{
        if l.n == 3 {{ break; }}
        total += l.n;
    }}
    total + items[5].text.len()
}}
fn toks(flag: bool) -> u32 {{
    let w := "{text}".concat("");
    let toks: List<Tok> = [Tok::Word(w), Tok::Num(5)];
    if flag {{ return 9; }}
    match toks[0] {{ Tok::Word(s) => s.len(), Tok::Num(n) => n }}
}}
fn lent(flag: bool) -> u32 {{
    let a := "{text}".concat("");
    let b := "{text}".concat("");
    let words: List<string> = [a, b];
    var total: u32 = 0;
    loop w in words {{
        if flag {{ return 10; }}
        total += w.len();
    }}
    total
}}
fn main() -> u32 {{
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {{
        if iteration == 8192 {{ break; }}
        total += caller(true);
        total += caller(false);
        total += grow(true);
        total += grow(false);
        total += popped(true);
        total += popped(false);
        total += discarded();
        total += reassign(true);
        total += reassign(false);
        total += returned(true);
        total += returned(false);
        total += labels(true);
        total += labels(false);
        total += toks(true);
        total += toks(false);
        total += lent(true);
        total += lent(false);
        iteration += 1;
    }}
    total
}}"#
        ),
    );
    // Per iteration: constants 71 plus seven text lengths (see the helpers).
    let t = TEXT_BYTES as u32;
    let expected = (71 + 7 * t) * ITERATIONS;
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(
        source.stdout,
        format!("Result: u32({expected})\n").as_bytes()
    );
    build_wasm(&f, "e1b-lists-stress.wasm");
    let wasm_path = f.0.join("e1b-lists-stress.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&wasm_path).unwrap());
    fs::write(&wasm_path, capped).unwrap();
    let wasm = f.run(&["run", "e1b-lists-stress.wasm"]);
    assert!(
        wasm.status.success(),
        "capped Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, format!("Result: i32({expected})\n").as_bytes());
    assert_capped_memory(&wasm_path, initial, maximum);
}

#[test]
fn element_places_and_lists_reject_unsafe_forms() {
    let f = Fixture::new();
    project(&f, "e1b-negatives", "fn main() -> u32 { 0 }");
    let items = "use alloc::List;\n";
    // Moving an element out of a live list is a partial move.
    for statement in ["let s := items[0];", "let n := eat(items[0]);"] {
        rejects(
            &f,
            &format!(
                "{items}fn eat(s: string) -> u32 {{ s.len() }}\nfn main() -> u32 {{\n    var items: List<string> = [\"ab\"];\n    {statement}\n    1\n}}"
            ),
            "TE022",
            "`replace`, `swap` or `pop`",
        );
    }
    // Overwriting an owning element in place would drop the old value.
    rejects(
        &f,
        &format!("{items}fn main() -> u32 {{\n    var items: List<string> = [\"ab\"];\n    items[0] = \"c\";\n    1\n}}"),
        "TE022",
        "cannot be overwritten in place",
    );
    // A live element loan blocks push, pop, clear, move and reassignment.
    for (call, what) in [
        (
            "items.push(\"q\");",
            "cannot push to `items` while it is borrowed",
        ),
        (
            "let p := items.pop();",
            "cannot pop from `items` while it is borrowed",
        ),
        (
            "items.clear();",
            "cannot clear `items` while it is borrowed",
        ),
        (
            "items = [\"z\"];",
            "cannot assign to `items` while it is borrowed",
        ),
        (
            "let moved := items;",
            "cannot move `items` while it is borrowed",
        ),
    ] {
        rejects(
            &f,
            &format!(
                "{items}fn main() -> u32 {{\n    var items: List<string> = [\"ab\"];\n    let r := items[0].borrow();\n    {call}\n    r.len()\n}}"
            ),
            "BE005",
            what,
        );
    }
    // Mutating the list inside `loop x in items` is a loan conflict.
    rejects(
        &f,
        &format!("{items}fn main() -> u32 {{\n    var items: List<string> = [\"ab\"];\n    loop w in items {{ items.push(\"q\"); }}\n    0\n}}"),
        "BE005",
        "cannot push to `items` while it is borrowed",
    );
    // `get` copies, so it needs a copyable element.
    rejects(
        &f,
        &format!("{items}fn main() -> u32 {{\n    var items: List<string> = [\"ab\"];\n    match items.get(0) {{ Some(w) => 1, None => 0 }}\n}}"),
        "TE022",
        "get() copies its element",
    );
    // Search methods stay primitive-only.
    rejects(
        &f,
        &format!("{items}fn main() -> bool {{\n    var items: List<string> = [\"ab\"];\n    items.contains(\"ab\")\n}}"),
        "TE017",
        "needs primitive elements",
    );
    // Nested lists and reference elements are gated with a diagnostic.
    rejects(
        &f,
        &format!("{items}fn main() -> u32 {{\n    var items: List<List<u8>> = [];\n    0\n}}"),
        "TE017",
        "nested List<List<T>>",
    );
    rejects(
        &f,
        &format!("{items}fn main() -> u32 {{\n    var items: List<borrow string> = [];\n    0\n}}"),
        "TE017",
        "reference type arguments",
    );
    // A literal element of the wrong type.
    rejects(
        &f,
        &format!(
            "{items}fn main() -> u32 {{\n    let items: List<string> = [\"a\", 1];\n    0\n}}"
        ),
        "TE002",
        "",
    );
}

#[test]
fn list_index_out_of_bounds_traps_in_source_and_wasm() {
    let f = Fixture::new();
    project(
        &f,
        "e1b-trap",
        "use alloc::List;\nfn main() -> u32 {\n    var items: List<string> = [\"abc\"];\n    items.push(\"d\");\n    let i: u32 = 2;\n    items[i].len()\n}\n",
    );
    let source = f.run(&["run"]);
    assert!(String::from_utf8_lossy(&source.stderr).contains("RE007"));
    build_wasm(&f, "e1b-trap.wasm");
    let wasm = f.run(&["run", "e1b-trap.wasm"]);
    assert!(String::from_utf8_lossy(&wasm.stderr).contains("array index out of bounds"));
    // An empty list traps on any index, including after pop.
    f.write(
        "src/main.mb",
        "use alloc::List;\nfn main() -> u32 {\n    var items: List<u32> = [1];\n    let p := items.pop();\n    items[0]\n}\n",
    );
    let source = f.run(&["run"]);
    assert!(String::from_utf8_lossy(&source.stderr).contains("RE007"));
}

#[test]
fn string_lists_need_the_alloc_layer() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='e1b-no-alloc'\nentry='main::main'\n[build]\nalloc=false\n",
    );
    f.write(
        "src/main.mb",
        "use alloc::List;\nfn main() -> u32 {\n    let items: List<string> = [\"a\"];\n    items.len()\n}\n",
    );
    let check = f.run(&["check"]);
    assert!(!check.status.success());
    let stderr = String::from_utf8_lossy(&check.stderr);
    assert!(stderr.contains("ME012"), "{stderr}");
    assert!(stderr.contains("[build] alloc"), "{stderr}");
}
