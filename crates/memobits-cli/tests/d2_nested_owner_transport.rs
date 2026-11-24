//! D2 phase 2c slice 4: String-owning nominal structs nested in structs, as
//! enum payloads, and arrays of owners inside struct and enum payloads.
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
            "memobits-nested-owner-{}-{}",
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

#[test]
fn nested_string_owners_run_in_source_and_wasm() {
    let f = Fixture::new();
    project(
        &f,
        "nested-owner",
        r#"type Label { text: string, n: u32 }
type Outer { inner: Label, k: u32 }
type Both { first: Label, second: Label }
type Bag { items: array<Label, 2>, k: u32 }
type Slot [Empty, Full(Outer), One(Label), Many(array<Label, 2>)]
fn label_len(l: borrow Label) -> u32 { l.text.len() + l.n }
fn outer_len(o: borrow Outer) -> u32 { o.inner.text.len() + o.inner.n + o.k }
fn take(o: Outer) -> u32 { o.inner.text.len() + o.k }
fn early(o: Outer, flag: bool) -> u32 {
    if flag { return 1; }
    take(o)
}
fn make() -> Outer {
    let h := "ab".concat("c");
    let l := Label { text: h, n: 1 };
    let o := Outer { inner: l, k: 2 };
    o
}
fn lens(b: borrow Both) -> u32 { b.first.text.len() + b.second.text.len() }
fn array_len(a: array<Label, 2>) -> u32 { label_len(a[0].borrow()) + label_len(a[1].borrow()) }
fn bag_k(b: Bag) -> u32 { b.k }
fn slot_len(s: Slot) -> u32 {
    match s {
        Slot::Empty => 0,
        Slot::Full(x) => x.inner.text.len() + x.k,
        Slot::One(l) => l.text.len() + l.n,
        Slot::Many(arr) => array_len(arr),
    }
}
fn main() -> u32 {
    let h := "ab".concat("cd");
    let l := Label { text: h, n: 1 };
    let o := Outer { inner: l, k: 2 };
    let a := outer_len(o.borrow());
    let m := make();
    let c_heap := "x".concat("y");
    let c := Label { text: c_heap, n: 0 };
    let d_heap := "x".concat("yy");
    let d := Label { text: d_heap, n: 0 };
    let both := Both { first: c, second: d };
    let q_heap := "q".concat("r");
    let q := Label { text: q_heap, n: 0 };
    let qo := Outer { inner: q, k: 4 };
    let z_heap := "zz".concat("z");
    let z := Label { text: z_heap, n: 1 };
    let r_heap := "ab".concat("");
    let r := Label { text: r_heap, n: 1 };
    let s_heap := "x".concat("y");
    let s := Label { text: s_heap, n: 2 };
    let items := [r, s];
    let bag_heap := "a".concat("b");
    let bl := Label { text: bag_heap, n: 0 };
    let bl2 := Label { text: "c", n: 0 };
    let bag := Bag { items: [bl, bl2], k: 3 };
    let k_heap := "k".concat("k");
    let k := Label { text: k_heap, n: 0 };
    let ko := Outer { inner: k, k: 1 };
    let e_heap := "e".concat("e");
    let e := Label { text: e_heap, n: 0 };
    let eo := Outer { inner: e, k: 1 };
    var v := Outer { inner: Label { text: "lit", n: 0 }, k: 1 };
    v.k = 5;
    a + take(m) + take(o) + lens(both.borrow()) + slot_len(Slot::Full(qo)) + slot_len(Slot::One(z))
        + slot_len(Slot::Many(items)) + bag_k(bag) + early(ko, true) + early(eo, false) + v.k
}
"#,
    );
    // 7 + 5 + 6 + 5 + 6 + 4 + 7 + 3 + 1 + 3 + 5
    run_source_and_wasm(
        &f,
        "nested-owner.wasm",
        b"Result: u32(52)\n",
        b"Result: i32(52)\n",
    );
}

#[test]
fn repeated_nested_string_owners_release_on_normal_and_early_returns() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    project(
        &f,
        "nested-owner-stress",
        &format!(
            r#"type Label {{ text: string, n: u32 }}
type Outer {{ inner: Label, k: u32 }}
type Bag {{ items: array<Label, 2>, k: u32 }}
type Slot [Empty, Full(Outer), One(Label), Many(array<Label, 2>)]
fn make_outer() -> Outer {{
    let heap := "{text}".concat("");
    let label := Label {{ text: heap, n: 1 }};
    let outer := Outer {{ inner: label, k: 2 }};
    outer
}}
fn consume_outer(outer: Outer, flag: bool) -> u32 {{
    let extra := "{text}".concat("");
    if flag {{ return 1; }}
    outer.inner.text.len() + outer.k + extra.len() - extra.len()
}}
fn outer_caller(flag: bool) -> u32 {{
    let heap := "{text}".concat("");
    let label := Label {{ text: heap, n: 1 }};
    let outer := Outer {{ inner: label, k: 2 }};
    if flag {{ return 7; }}
    consume_outer(outer, false)
}}
fn result_caller(flag: bool) -> u32 {{
    let made := make_outer();
    if flag {{ return 5; }}
    consume_outer(made, false)
}}
fn bag_caller(flag: bool) -> u32 {{
    let first_heap := "{text}".concat("");
    let first := Label {{ text: first_heap, n: 0 }};
    let second_heap := "{text}".concat("");
    let second := Label {{ text: second_heap, n: 0 }};
    let bag := Bag {{ items: [first, second], k: 3 }};
    if flag {{ return 9; }}
    consume_bag(bag)
}}
fn consume_bag(bag: Bag) -> u32 {{ bag.k }}
fn slot_len(slot: Slot, flag: bool) -> u32 {{
    if flag {{ return 11; }}
    match slot {{
        Slot::Empty => 0,
        Slot::Full(x) => x.inner.text.len() + x.k,
        Slot::One(l) => l.text.len(),
        Slot::Many(arr) => 13,
    }}
}}
fn slot_caller(flag: bool, consume: bool) -> u32 {{
    let heap := "{text}".concat("");
    let label := Label {{ text: heap, n: 1 }};
    let outer := Outer {{ inner: label, k: 2 }};
    let slot := Slot::Full(outer);
    if flag {{ return 3; }}
    slot_len(slot, consume)
}}
fn many_caller(consume: bool) -> u32 {{
    let first_heap := "{text}".concat("");
    let first := Label {{ text: first_heap, n: 0 }};
    let second := Label {{ text: "lit", n: 0 }};
    let pair := [first, second];
    let slot := Slot::Many(pair);
    slot_len(slot, consume)
}}
fn main() -> u32 {{
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {{
        if iteration == {ITERATIONS} {{ break; }}
        total += outer_caller(true);
        total += outer_caller(false);
        total += result_caller(true);
        total += result_caller(false);
        total += bag_caller(true);
        total += bag_caller(false);
        total += slot_caller(true, false);
        total += slot_caller(false, true);
        total += slot_caller(false, false);
        total += many_caller(true);
        total += many_caller(false);
        iteration += 1;
    }}
    total
}}
"#
        ),
    );
    // Per iteration: 7 + 4098 + 5 + 4098 + 9 + 3 + 3 + 11 + 4098 + 11 + 13 = 12356.
    let expected = 12_356u32 * ITERATIONS;
    run_source_and_wasm(
        &f,
        "nested-owner-stress.wasm",
        format!("Result: u32({expected})\n").as_bytes(),
        format!("Result: i32({expected})\n").as_bytes(),
    );
    let wasm_path = f.0.join("nested-owner-stress.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&wasm_path).unwrap());
    fs::write(&wasm_path, capped).unwrap();
    let wasm = f.run(&["run", "nested-owner-stress.wasm"]);
    assert!(
        wasm.status.success(),
        "capped Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, format!("Result: i32({expected})\n").as_bytes());
    assert_capped_memory(&wasm_path, initial, maximum);
}

#[test]
fn nested_string_owners_keep_neighbouring_shapes_rejected() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='nested-owner-negatives'\nentry='main::main'\n",
    );
    let bind = r#"type Label { text: string, n: u32 }
type Outer { inner: Label, k: u32 }
type Slot [Empty, Full(Outer)]
fn take(o: Outer) {}
fn make() { let t := "a".concat("b"); let l := Label { text: t, n: 1 }; let o := Outer { inner: l, k: 1 };"#;
    for (source, code, message) in [
        // Field, element and payload move-out from a live owner.
        (
            format!("{bind} let m := o.inner; }} fn main() {{}}"),
            "TE022",
            "cannot be moved out by field access",
        ),
        (
            format!("{bind} let a := [o]; let m := a[0]; }} fn main() {{}}"),
            "TE022",
            "cannot be moved out by indexing",
        ),
        (
            format!("{bind} let s := Slot::Full(o); match s {{ Slot::Full(x) => {{ let m := x.inner; }}, Slot::Empty => {{}} }} }} fn main() {{}}"),
            "TE022",
            "cannot be moved out by field access",
        ),
        // Use after move of the outer owner and of the moved-in inner owner.
        (
            format!("{bind} take(o); take(o); }} fn main() {{}}"),
            "BE001",
            "unavailable after a move",
        ),
        (
            format!("{bind} let again := l.n; }} fn main() {{}}"),
            "BE001",
            "unavailable after a move",
        ),
        // Repeat form copies the owner.
        (
            format!("{bind} let a := [o; 3]; }} fn main() {{}}"),
            "TE017",
            "would copy a String-owning element",
        ),
        // Whole-owner reassignment stays rejected.
        (
            format!("{bind} let t2 := \"c\".concat(\"d\"); let l2 := Label {{ text: t2, n: 1 }}; var p := Outer {{ inner: l2, k: 1 }}; p = o; }} fn main() {{}}"),
            "TE018",
            "can only move directly into a new local",
        ),
        // Recursive by-value types and Error ancestry.
        (
            "type Rec { next: Rec, s: string } fn main() {}".to_string(),
            "TE026",
            "recursive struct",
        ),
        (
            "type Label { text: string } type Rec { l: Label, back: Back } type Back { r: Rec } fn main() {}".to_string(),
            "TE026",
            "recursive struct",
        ),
        (
            "type Label { text: string } type Failure: Error { l: Label } fn main() {}".to_string(),
            "LE900",
            "Error-derived type 'Failure' cannot own heap Strings yet",
        ),
        // A struct with a plain (non-owner) aggregate next to an owner stays rejected.
        (
            "type Label { text: string } type Point { x: u32 } type Mixed { l: Label, p: Point } fn main() {}".to_string(),
            "LE900",
            "nesting structs with String fields",
        ),
    ] {
        f.write("src/main.mb", &source);
        let output = f.run(&["build"]);
        assert_eq!(output.status.code(), Some(1), "{source}: {output:?}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains(code), "{source}: {stderr}");
        assert!(stderr.contains(message), "{source}: {stderr}");
    }
}

#[test]
fn nested_string_owner_exported_signatures_stay_rejected() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='nested-owner-exports'\nentry='main::main'\n[export]\ncheck='main::check'\n",
    );
    f.write(
        "src/main.mb",
        "pub type Label { text: string }\npub type Outer { inner: Label }\nfn main() {}\npub fn check(o: Outer) -> u32 { 1 }\n",
    );
    let output = f.run(&["build", "--lib"]);
    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stderr)
        .contains("exported signatures cannot take structs or struct references"));
}
