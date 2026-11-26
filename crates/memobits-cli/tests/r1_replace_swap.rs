//! R1: `replace`, `swap` and owning overwrite as RHS-first replacement, for
//! locals, fields and array and list elements.
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
            "memobits-r1-replace-swap-{}-{}",
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

const POSITIVE: &str = r#"use alloc::List;
type Label { text: string, n: u32 }
type Bag { items: array<Label, 2>, k: u32 }
type Tok [ Word(string), Num(u32) ]
fn bump(l: share Label, extra: string) -> u32 {
    let old := replace(l.text, extra);
    l.n = l.n + 1;
    old.len()
}
fn set_item(items: share array<string, 2>, v: string) -> u32 {
    items[1] = v;
    let o := replace(items[0], "zzz");
    o.len()
}
fn early(flag: bool) -> u32 {
    let wa := "a".concat("b");
    let wb := "c".concat("d");
    var words: array<string, 2> = [wa, wb];
    let wx := "x".concat("y");
    words[0] = { if flag { return 5; } wx };
    words[1].len()
}
fn main() -> u32 {
    let t1 := "hello".concat("");
    let l1 := Label { text: t1, n: 1 };
    var lab := l1;
    let e := "ee".concat("");
    let r1 := bump(lab.share(), e);
    let t2 := "ab".concat("");
    let t3 := "cde".concat("");
    let la := Label { text: t2, n: 2 };
    let lb := Label { text: t3, n: 3 };
    var ls: array<Label, 2> = [la, lb];
    let t4 := "wxyz".concat("");
    let lc := Label { text: t4, n: 4 };
    let old := replace(ls[1], lc);
    swap(ls[0], ls[1]);
    let t5 := "q".concat("");
    let ld := Label { text: t5, n: 5 };
    ls[0] = ld;
    let n1 := "nn".concat("");
    let n2 := "mmm".concat("");
    let ba := Label { text: n1, n: 6 };
    let bb := Label { text: n2, n: 7 };
    let pair: array<Label, 2> = [ba, bb];
    let bag0 := Bag { items: pair, k: 3 };
    var bag := bag0;
    let t6 := "r6".concat("");
    let ld2 := Label { text: t6, n: 8 };
    bag.items[1] = ld2;
    swap(bag.items[0], bag.items[1]);
    var bname := "newname".concat("");
    let nm := replace(bname, "k");
    var s1 := "s1".concat("");
    let s0 := replace(s1, "t".concat("tt"));
    let w := "word".concat("");
    var toks: List<Tok> = [Tok::Word(w), Tok::Num(5)];
    let w2 := "other".concat("");
    toks[1] = Tok::Word(w2);
    let ot := replace(toks[0], Tok::Num(1));
    let tl := match ot { Tok::Word(x) => x.len(), Tok::Num(n) => n };
    let am := "m".concat("m");
    let an := "n".concat("");
    var arr: array<string, 2> = [am, an];
    let sv := set_item(arr.share(), "new".concat(""));
    var nums: array<u32, 3> = [1, 2, 3];
    let o2 := replace(nums[1], 20);
    swap(nums[0], nums[2]);
    var counter: u32 = 7;
    let oc := replace(counter, 9);
    r1 + old.text.len() + ls[0].text.len() + ls[1].n + bag.items[0].n + bname.len() + nm.len()
        + s1.len() + s0.len() + tl + early(true) + early(false) + sv + arr[1].len()
        + o2 + nums[0] + oc + counter
}
"#;

#[test]
fn replace_swap_and_overwrite_work_for_every_place_kind() {
    let f = Fixture::new();
    project(&f, "r1-places", POSITIVE);
    // 48 (strings, structs, lists, enums) + o2 2 + nums[0] 3 + oc 7 + counter 9
    run_source_and_wasm(
        &f,
        "r1-places.wasm",
        b"Result: u32(69)\n",
        b"Result: i32(69)\n",
    );
}

#[test]
fn rhs_reads_the_old_value_and_early_return_keeps_the_place() {
    let f = Fixture::new();
    project(
        &f,
        "r1-rhs",
        r#"fn grow(flag: bool) -> u32 {
    let a := "ab".concat("c");
    let b := "d".concat("");
    var words: array<string, 2> = [a, b];
    words[0] = words[0].concat("!!");
    let old := replace(words[1], words[0].concat("?"));
    if flag { return 100; }
    words[0].len() * 100 + words[1].len() * 10 + old.len()
}
fn kept(flag: bool) -> u32 {
    let a := "ab".concat("c");
    let b := "d".concat("");
    var words: array<string, 2> = [a, b];
    let x := "wxyz".concat("");
    let o := replace(words[0], { if flag { return words[0].len(); } x });
    o.len() + words[0].len() * 10
}
fn main() -> u32 { grow(false) + grow(true) + kept(true) * 1000 + kept(false) * 100000 }
"#,
    );
    // grow(false): words[0]="abc!!"(5), words[1]="abc!!?"(6), old=1 -> 561; grow(true) 100
    // kept(true): early return with the original 3 -> 3000
    // kept(false): o="abc"(3) + 4*10 = 43 -> 4300000
    run_source_and_wasm(
        &f,
        "r1-rhs.wasm",
        b"Result: u32(4303661)\n",
        b"Result: i32(4303661)\n",
    );
}

#[test]
fn loop_over_arrays_of_owners_binds_read_only_borrows() {
    let f = Fixture::new();
    project(
        &f,
        "r1-loop",
        r#"type Label { text: string, n: u32 }
fn main() -> u32 {
    let a := "ab".concat("c");
    let b := "d".concat("");
    let words: array<string, 2> = [a, b];
    var total: u32 = 0;
    loop w in words { total += w.len(); }
    let t1 := "xyz".concat("");
    let l1 := Label { text: t1, n: 5 };
    let l2 := Label { text: "q", n: 6 };
    let ls := [l1, l2];
    loop l in ls { total += l.n + l.text.len(); }
    total
}
"#,
    );
    run_source_and_wasm(
        &f,
        "r1-loop.wasm",
        b"Result: u32(19)\n",
        b"Result: i32(19)\n",
    );
    rejects(
        &f,
        "fn main() -> u32 {\n    let a := \"ab\".concat(\"c\");\n    let b := \"d\".concat(\"\");\n    var words: array<string, 2> = [a, b];\n    loop w in words { words[0] = \"x\"; }\n    1\n}",
        "BE005",
        "words",
    );
}

#[test]
fn replace_traps_on_out_of_bounds_after_the_value_is_evaluated() {
    let f = Fixture::new();
    project(&f, "r1-trap", "fn main() -> u32 { 0 }");
    f.write(
        "src/main.mb",
        "fn main() -> u32 {\n    let a := \"abc\".concat(\"d\");\n    var items: array<string, 1> = [a];\n    let i: u32 = 1;\n    let o := replace(items[i], \"x\");\n    o.len()\n}\n",
    );
    let source = f.run(&["run"]);
    assert!(String::from_utf8_lossy(&source.stderr).contains("RE007"));
    build_wasm(&f, "r1-trap.wasm");
    let wasm = f.run(&["run", "r1-trap.wasm"]);
    assert!(String::from_utf8_lossy(&wasm.stderr).contains("array index out of bounds"));
}

#[test]
fn replace_swap_overwrite_release_every_value_under_capped_memory() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    project(
        &f,
        "r1-stress",
        &format!(
            r#"use alloc::List;
type Label {{ text: string, n: u32 }}
fn arr_str(flag: bool) -> u32 {{
    let a := "{text}".concat("");
    let b := "{text}".concat("");
    var words: array<string, 2> = [a, b];
    let x := "{text}".concat("");
    words[0] = x;
    let y := "{text}".concat("");
    let old := replace(words[1], y);
    swap(words[0], words[1]);
    words[1] = words[1].concat("!");
    if flag {{ return 1; }}
    words[0].len() + words[1].len() + old.len()
}}
fn arr_early(flag: bool) -> u32 {{
    let a := "{text}".concat("");
    let b := "{text}".concat("");
    var words: array<string, 2> = [a, b];
    let x := "{text}".concat("");
    words[0] = {{ if flag {{ return 2; }} x }};
    words[1].len()
}}
fn list_str(flag: bool) -> u32 {{
    let a := "{text}".concat("");
    let b := "{text}".concat("");
    var xs: List<string> = [a, b];
    let x := "{text}".concat("");
    xs[0] = x;
    let y := "{text}".concat("");
    let o := replace(xs[1], y);
    swap(xs[0], xs[1]);
    let z := "{text}".concat("");
    xs.push(z);
    if flag {{ return 3; }}
    xs[0].len() + xs[1].len() + xs.len() + o.len()
}}
fn labels(flag: bool) -> u32 {{
    let t1 := "{text}".concat("");
    let t2 := "{text}".concat("");
    let la := Label {{ text: t1, n: 1 }};
    let lb := Label {{ text: t2, n: 2 }};
    var ls: array<Label, 2> = [la, lb];
    let t3 := "{text}".concat("");
    let lc := Label {{ text: t3, n: 4 }};
    ls[0] = lc;
    let t4 := "{text}".concat("");
    let ld := Label {{ text: t4, n: 5 }};
    let old := replace(ls[1], ld);
    swap(ls[0], ls[1]);
    let t5 := "{text}".concat("");
    ls[0].text = t5;
    if flag {{ return 4; }}
    ls[0].text.len() + ls[1].n + old.n + old.text.len()
}}
fn label_list(flag: bool) -> u32 {{
    let t1 := "{text}".concat("");
    let t2 := "{text}".concat("");
    let la := Label {{ text: t1, n: 1 }};
    let lb := Label {{ text: t2, n: 2 }};
    var ls: List<Label> = [la, lb];
    let t3 := "{text}".concat("");
    let lc := Label {{ text: t3, n: 4 }};
    ls[0] = lc;
    let t4 := "{text}".concat("");
    let ld := Label {{ text: t4, n: 5 }};
    let old := replace(ls[1], ld);
    swap(ls[0], ls[1]);
    let t5 := "{text}".concat("");
    ls[0].text = t5;
    if flag {{ return 5; }}
    ls[0].text.len() + ls[1].n + old.n + old.text.len()
}}
fn set_item(items: share array<string, 2>, v: string) -> u32 {{
    items[1] = v;
    let o := replace(items[0], "lit");
    o.len()
}}
fn via_share(flag: bool) -> u32 {{
    let a := "{text}".concat("");
    let b := "{text}".concat("");
    var words: array<string, 2> = [a, b];
    let v := "{text}".concat("");
    let n := set_item(words.share(), v);
    if flag {{ return 6; }}
    n + words[1].len()
}}
fn main() -> u32 {{
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {{
        if iteration == {ITERATIONS} {{ break; }}
        total += arr_str(true);
        total += arr_str(false);
        total += arr_early(true);
        total += arr_early(false);
        total += list_str(true);
        total += list_str(false);
        total += labels(true);
        total += labels(false);
        total += label_list(true);
        total += label_list(false);
        total += via_share(true);
        total += via_share(false);
        iteration += 1;
    }}
    total
}}
"#
        ),
    );
    let t = TEXT_BYTES as u32;
    // arr_str 1 + (3T + 1), arr_early 2 + T, list_str 3 + (3T + 3),
    // labels 4 + (2T + 6), label_list 5 + (2T + 6), via_share 6 + 2T.
    let per_iteration = (1 + 3 * t + 1)
        + (2 + t)
        + (3 + 3 * t + 3)
        + (4 + 2 * t + 6)
        + (5 + 2 * t + 6)
        + (6 + 2 * t);
    let expected = per_iteration * ITERATIONS;
    run_source_and_wasm(
        &f,
        "r1-stress.wasm",
        format!("Result: u32({expected})\n").as_bytes(),
        format!("Result: i32({expected})\n").as_bytes(),
    );
    let wasm_path = f.0.join("r1-stress.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&wasm_path).unwrap());
    fs::write(&wasm_path, capped).unwrap();
    let wasm = f.run(&["run", "r1-stress.wasm"]);
    assert!(
        wasm.status.success(),
        "capped Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, format!("Result: i32({expected})\n").as_bytes());
    assert_capped_memory(&wasm_path, initial, maximum);
}

#[test]
fn replace_and_swap_reject_bad_places_types_and_loans() {
    let f = Fixture::new();
    project(&f, "r1-negatives", "fn main() -> u32 { 0 }");
    let prelude = "fn main() -> u32 {\n    let a := \"x\".concat(\"y\");\n    let b := \"p\".concat(\"q\");\n";
    // Immutable owner.
    rejects(
        &f,
        &format!("{prelude}    let items: array<string, 2> = [a, b];\n    let o := replace(items[0], \"z\");\n    o.len()\n}}"),
        "TE004",
        "must be a `var` or a `share` parameter",
    );
    rejects(
        &f,
        &format!("{prelude}    let items: array<string, 2> = [a, b];\n    swap(items[0], items[1]);\n    1\n}}"),
        "TE004",
        "must be a `var` or a `share` parameter",
    );
    rejects(
        &f,
        &format!("{prelude}    let s := a;\n    let o := replace(s, \"z\");\n    o.len()\n}}"),
        "TE004",
        "immutable",
    );
    // Non-place first argument.
    rejects(
        &f,
        &format!("{prelude}    var items: array<string, 2> = [a, b];\n    let o := replace(items[0].len(), 3);\n    1\n}}"),
        "TE006",
        "requires a place",
    );
    // Type mismatch.
    rejects(
        &f,
        &format!("{prelude}    var items: array<string, 2> = [a, b];\n    let o := replace(items[0], 3);\n    1\n}}"),
        "TE002",
        "expected string",
    );
    rejects(
        &f,
        &format!("{prelude}    var items: array<string, 2> = [a, b];\n    var n: u32 = 1;\n    swap(items[0], n);\n    1\n}}"),
        "TE007",
        "same type",
    );
    // Overlapping swap: same constant element, dynamic indices into one array,
    // the same local.
    for call in ["swap(items[0], items[0])", "swap(items[i], items[j])"] {
        rejects(
            &f,
            &format!("{prelude}    var items: array<string, 2> = [a, b];\n    let i: u32 = 0;\n    let j: u32 = 1;\n    {call};\n    1\n}}"),
            "BE005",
            "items[",
        );
    }
    rejects(
        &f,
        &format!("{prelude}    var s := a;\n    swap(s, s);\n    1\n}}"),
        "BE005",
        "`s`",
    );
    // A live loan of the place blocks the replacement.
    rejects(
        &f,
        &format!("fn both(a: borrow string, b: string) -> u32 {{ a.len() }}\n{prelude}    var items: array<string, 2> = [a, b];\n    both(items[0].borrow(), replace(items[0], \"w\"))\n}}"),
        "BE005",
        "borrowed",
    );
    // A user-defined `replace` or `swap` takes precedence over the built-in.
    f.write(
        "src/main.mb",
        "fn replace(a: u32, b: u32) -> u32 { a + b }\nfn swap(a: u32, b: u32) -> u32 { a * b }\nfn main() -> u32 { replace(1, 2) + swap(3, 4) }\n",
    );
    run_source_and_wasm(
        &f,
        "r1-user.wasm",
        b"Result: u32(15)\n",
        b"Result: i32(15)\n",
    );
}
