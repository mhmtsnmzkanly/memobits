//! E1a: owned elements in `array<T, N>`. `array<string, N>`, arrays of owner
//! structs, element places (`items[i]`) used in place, lifted element-borrow
//! limits, loans and the rejected neighbours (move-out, repeat).
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
            "memobits-e1-owned-elements-{}-{}",
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
fn owned_elements_work_in_arrays_in_source_and_wasm() {
    let f = Fixture::new();
    project(
        &f,
        "e1-owned-elements",
        r#"type Label { text: string, n: u32 }
type Bag { items: array<Label, 2>, k: u32 }
pub type Name { pub text: string } extend {
    pub fn size(borrow self) -> u32 { self.text.len() }
}
pub type Doc { pub title: Name, pub n: u32 }
type Tok [ Word(string), Num(u32) ]
fn size_of(s: borrow string) -> u32 { s.len() }
fn label_len(l: borrow Label) -> u32 { l.text.len() + l.n }
fn total(words: array<string, 2>) -> u32 {
    size_of(words[0].borrow()) + size_of(words[1].borrow())
}
fn pick(words: borrow array<string, 2>, i: u32) -> u32 { size_of(words[i].borrow()) }
fn both(a: borrow string, b: share string) -> u32 { a.len() + b.len() }
fn make() -> array<string, 2> {
    let a := "pp".concat("q");
    let b := "r".concat("s");
    let words := [a, b];
    words
}
fn early(flag: bool) -> u32 {
    let a := "pp".concat("q");
    let words: array<string, 2> = [a, "z"];
    if flag { return 1; }
    pick(words.borrow(), 0)
}
fn main() -> u32 {
    let a := "ab".concat("c");
    let b := "wxyz".concat("");
    var words: array<string, 2> = [a, b];
    let i: u32 = 1;
    let r1 := words[0].len() + words[i].len();
    let r2 := pick(words.borrow(), i);
    let c := "12345".concat("");
    let d := "6".concat("");
    let other: array<string, 2> = [c, d];
    words = other;
    let r3 := total(words);
    let made := make();
    let r4 := total(made);
    let r5 := early(true) + early(false);
    let t1 := "hello".concat("");
    let l1 := Label { text: t1, n: 1 };
    let t2 := "hi".concat("");
    let l2 := Label { text: t2, n: 2 };
    let labels := [l1, l2];
    let r6 := labels[i].text.len() + label_len(labels[0].borrow());
    let g1 := "aa".concat("");
    let ga := Label { text: g1, n: 10 };
    let gb := Label { text: "b", n: 20 };
    let row := [ga, gb];
    let grid := [row];
    let r7 := label_len(grid[0][1].borrow());
    let e := "eeee".concat("");
    let e1 := Label { text: e, n: 1 };
    let e2 := Label { text: "f", n: 2 };
    let es := [e1, e2];
    let bag := Bag { items: es, k: 5 };
    let r8 := label_len(bag.items[0].borrow()) + bag.items[1].text.len();
    let h := "abcd".concat("");
    let name := Name { text: h };
    let doc := Doc { title: name, n: 3 };
    let r9 := doc.title.size() + doc.n;
    let w := "abcd".concat("");
    let word := Tok::Word(w);
    let num := Tok::Num(5);
    let toks := [word, num];
    let r10 := match toks[0] { Tok::Word(x) => x.len(), Tok::Num(n) => n }
        + match toks[i] { Tok::Word(x) => x.len(), Tok::Num(n) => n };
    let s1 := "xx".concat("");
    let s2 := "yyy".concat("");
    var pair: array<string, 2> = [s1, s2];
    let r11 := both(pair[0].borrow(), pair[1].share());
    r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11
}
"#,
    );
    // 7 + 4 + 6 + 5 + 4 + 8 + 21 + 6 + 7 + 9 + 5
    run_source_and_wasm(
        &f,
        "e1-owned-elements.wasm",
        b"Result: u32(82)\n",
        b"Result: i32(82)\n",
    );
}

#[test]
fn array_owner_elements_release_on_normal_and_early_returns() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    project(
        &f,
        "e1-owned-elements-stress",
        &format!(
            r#"type Label {{ text: string, n: u32 }}
fn label_len(l: borrow Label) -> u32 {{ l.text.len() + l.n }}
fn consume(words: array<string, 2>, flag: bool) -> u32 {{
    let extra := "{text}".concat("");
    if flag {{ return 1; }}
    words[0].len() + words[1].len() + extra.len() - extra.len()
}}
fn caller(flag: bool) -> u32 {{
    let a := "{text}".concat("");
    let b := "{text}".concat("");
    let words := [a, b];
    if flag {{ return 7; }}
    consume(words, false)
}}
fn reassign(flag: bool) -> u32 {{
    let a := "{text}".concat("");
    let b := "{text}".concat("");
    var words: array<string, 2> = [a, b];
    let c := "{text}".concat("");
    let d := "{text}".concat("");
    let other: array<string, 2> = [c, d];
    words = other;
    if flag {{ return 2; }}
    words[0].len()
}}
fn make() -> array<string, 2> {{
    let a := "{text}".concat("");
    let words: array<string, 2> = [a, "lit"];
    words
}}
fn returned(flag: bool) -> u32 {{
    let made := make();
    if flag {{ return 3; }}
    4
}}
fn labels(flag: bool) -> u32 {{
    let t1 := "{text}".concat("");
    let l1 := Label {{ text: t1, n: 1 }};
    let t2 := "{text}".concat("");
    let l2 := Label {{ text: t2, n: 2 }};
    let items := [l1, l2];
    if flag {{ return 5; }}
    items[0].text.len() + items[1].n
}}
fn grid(flag: bool) -> u32 {{
    let t1 := "{text}".concat("");
    let l1 := Label {{ text: t1, n: 1 }};
    let l2 := Label {{ text: "lit", n: 2 }};
    let row := [l1, l2];
    let grid := [row];
    if flag {{ return 6; }}
    label_len(grid[0][1].borrow()) + grid[0][0].text.len()
}}
fn make_label() -> Label {{
    let heap := "{text}".concat("");
    let label := Label {{ text: heap, n: 3 }};
    label
}}
fn from_calls(flag: bool) -> u32 {{
    let items := [make_label(), make_label()];
    if flag {{ return 8; }}
    items[1].text.len() + items[0].n
}}
fn main() -> u32 {{
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {{
        if iteration == {ITERATIONS} {{ break; }}
        total += caller(true);
        total += caller(false);
        total += reassign(true);
        total += reassign(false);
        total += returned(true);
        total += returned(false);
        total += labels(true);
        total += labels(false);
        total += grid(true);
        total += grid(false);
        total += from_calls(true);
        total += from_calls(false);
        iteration += 1;
    }}
    total
}}
"#
        ),
    );
    // caller 7 + 2T, reassign 2 + T, returned 3 + 4, labels 5 + T + 2,
    // grid 6 + (3 + 2) + T, from_calls 8 + T + 3.
    let t = TEXT_BYTES as u32;
    let per_iteration = (7 + 2 * t) + (2 + t) + (3 + 4) + (5 + t + 2) + (6 + 5 + t) + (8 + t + 3);
    let expected = per_iteration * ITERATIONS;
    run_source_and_wasm(
        &f,
        "e1-owned-elements-stress.wasm",
        format!("Result: u32({expected})\n").as_bytes(),
        format!("Result: i32({expected})\n").as_bytes(),
    );
    let wasm_path = f.0.join("e1-owned-elements-stress.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&wasm_path).unwrap());
    fs::write(&wasm_path, capped).unwrap();
    let wasm = f.run(&["run", "e1-owned-elements-stress.wasm"]);
    assert!(
        wasm.status.success(),
        "capped Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, format!("Result: i32({expected})\n").as_bytes());
    assert_capped_memory(&wasm_path, initial, maximum);
}

#[test]
fn element_places_reject_moves_repeats_and_overlapping_loans() {
    let f = Fixture::new();
    project(&f, "e1-negatives", "fn main() -> u32 { 0 }");
    // Moving an element out of a live owner is a partial move.
    for statement in ["let s := items[0];", "let n := eat(items[0]);"] {
        rejects(
            &f,
            &format!(
                "fn eat(s: string) -> u32 {{ s.len() }}\nfn main() -> u32 {{\n    let h := \"ab\".concat(\"c\");\n    let items: array<string, 1> = [h];\n    {statement}\n    1\n}}"
            ),
            "TE022",
            "`replace`, `swap` or `pop`",
        );
    }
    rejects(
        &f,
        "type Label { text: string, n: u32 }\nfn main() -> u32 {\n    let h := \"ab\".concat(\"c\");\n    let l := Label { text: h, n: 1 };\n    let items: array<Label, 1> = [l];\n    let moved := items[0];\n    1\n}",
        "TE022",
        "`replace`, `swap` or `pop`",
    );
    // Repeating an owner would copy it.
    rejects(
        &f,
        "fn main() -> u32 {\n    let h := \"ab\".concat(\"c\");\n    let items: array<string, 2> = [h; 2];\n    1\n}",
        "TE017",
        "would copy a String-owning element",
    );
    rejects(
        &f,
        "type Label { text: string, n: u32 }\nfn main() -> u32 {\n    let h := \"ab\".concat(\"c\");\n    let l := Label { text: h, n: 1 };\n    let items: array<Label, 2> = [l; 2];\n    1\n}",
        "TE017",
        "would copy a String-owning element",
    );
    // Overwriting an owning element is an RHS-first replacement since R1 (see r1_replace_swap.rs).
    // Overlapping element loans (same constant index, dynamic indices).
    let pair = "fn both(a: borrow string, b: share string) -> u32 { a.len() }\n";
    for (call, label) in [
        ("both(items[0].borrow(), items[0].share())", "items[0]"),
        ("both(items[i].borrow(), items[j].share())", "items[_]"),
    ] {
        rejects(
            &f,
            &format!(
                "{pair}fn main() -> u32 {{\n    let a := \"ab\".concat(\"c\");\n    let b := \"d\".concat(\"e\");\n    var items: array<string, 2> = [a, b];\n    let i: u32 = 0;\n    let j: u32 = 1;\n    {call}\n}}"
            ),
            "BE005",
            label,
        );
    }
    // A live element loan blocks moving the array.
    rejects(
        &f,
        "fn two(a: borrow string, items: array<string, 2>) -> u32 { 1 }\nfn main() -> u32 {\n    let a := \"ab\".concat(\"c\");\n    let b := \"d\".concat(\"e\");\n    let items: array<string, 2> = [a, b];\n    two(items[0].borrow(), items)\n}",
        "BE005",
        "cannot move `items` while it is borrowed",
    );
    // A live element loan blocks reassigning the array.
    rejects(
        &f,
        "type Tok [ Word(string), Num(u32) ]\nfn main() -> u32 {\n    let h := \"abc\".concat(\"d\");\n    let a := Tok::Word(h);\n    let b := Tok::Num(5);\n    var items := [a, b];\n    let c := Tok::Num(1);\n    let d := Tok::Num(2);\n    let other := [c, d];\n    match items[0] {\n        Tok::Word(w) => { items = other; w.len() },\n        Tok::Num(n) => n,\n    }\n}",
        "BE005",
        "cannot assign to `items` while it is borrowed",
    );
}

#[test]
fn disjoint_constant_element_loans_are_allowed_and_bounds_trap() {
    let f = Fixture::new();
    project(
        &f,
        "e1-disjoint",
        r#"fn both(a: borrow string, b: share string) -> u32 { a.len() + b.len() }
fn main() -> u32 {
    let a := "ab".concat("c");
    let b := "de".concat("");
    var items: array<string, 2> = [a, b];
    both(items[0].borrow(), items[1].share())
}
"#,
    );
    run_source_and_wasm(
        &f,
        "e1-disjoint.wasm",
        b"Result: u32(5)\n",
        b"Result: i32(5)\n",
    );
    f.write(
        "src/main.mb",
        "fn main() -> u32 {\n    let h := \"abc\".concat(\"d\");\n    let items: array<string, 1> = [h];\n    let i: u32 = 1;\n    items[i].len()\n}\n",
    );
    let source = f.run(&["run"]);
    assert!(String::from_utf8_lossy(&source.stderr).contains("RE007"));
    build_wasm(&f, "e1-trap.wasm");
    let wasm = f.run(&["run", "e1-trap.wasm"]);
    assert!(String::from_utf8_lossy(&wasm.stderr).contains("array index out of bounds"));
}

#[test]
fn in_place_match_of_a_borrowed_string_enum_runs_across_blocks() {
    let f = Fixture::new();
    project(
        &f,
        "e1-in-place-match",
        r#"type E [ S(string), N ]
fn f(e: borrow E, c: bool) -> u32 {
    var r: u32 = 0;
    if c { match e { E::S(s) => { r = s.len(); }, E::N => {} } }
    r
}
fn g(e: borrow E, c: bool) -> u32 {
    let x := e;
    if c { match x { E::S(s) => s.len(), E::N => 0 } } else { 1 }
}
fn main() -> u32 {
    let t := "hello".concat("");
    let e := E::S(t);
    let n := E::N;
    f(e.borrow(), true) + f(e.borrow(), false) + g(e.borrow(), true) + g(n.borrow(), true) + g(e.borrow(), false)
}
"#,
    );
    // 5 + 0 + 5 + 0 + 1
    run_source_and_wasm(
        &f,
        "e1-in-place-match.wasm",
        b"Result: u32(11)\n",
        b"Result: i32(11)\n",
    );
}
