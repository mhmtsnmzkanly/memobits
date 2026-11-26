//! F1: method calls with aggregate arguments, heap String call results used
//! directly, hexadecimal / binary / octal literals with `_` separators, and
//! the single diagnostic for a misplaced `Self`.
//!
//! Every runtime check runs from source and from the standalone Wasm
//! artifact (same result, empty stderr). The stress programs run under a Wasm
//! memory capped to the initial size plus one page, so a block that a staged
//! call result, a method argument or an early return leaves behind makes them
//! trap; mutated programs that keep the value prove the cap bites.
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
            "memobits-f1-followups-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let fixture = Self(path);
        fixture.write(
            "project.toml",
            "[package]\nname='f1'\nentry='app::main'\n[build]\nstack_size=4096\n",
        );
        fixture
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

    /// Run from source and from the built artifact; both must print the same
    /// result and the artifact run must leave stderr empty.
    fn result(&self, source: &str) -> String {
        self.write("src/app.mb", source);
        let from_source = self.run(&["run"]);
        assert!(
            from_source.status.success() && from_source.stderr.is_empty(),
            "{source}: {}",
            String::from_utf8_lossy(&from_source.stderr)
        );
        let built = self.run(&["build"]);
        assert!(
            built.status.success(),
            "{source}: {}",
            String::from_utf8_lossy(&built.stderr)
        );
        let from_artifact = self.run(&["run", "target/memobits/app.wasm"]);
        assert!(from_artifact.status.success());
        assert!(from_artifact.stderr.is_empty());
        let source_text = String::from_utf8(from_source.stdout).unwrap();
        let artifact_text = String::from_utf8(from_artifact.stdout).unwrap();
        // The source run prints the declared result type (`u32(..)`); the raw
        // Wasm entry prints `i32(..)`.
        assert_eq!(
            source_text.replace("u32(", "i32("),
            artifact_text,
            "{source}"
        );
        source_text.trim().into()
    }

    /// The stderr of a program that must fail to compile with `code`
    /// mentioning `text`.
    fn rejects(&self, source: &str, code: &str, text: &str) -> String {
        self.write("src/app.mb", source);
        let output = self.run(&["check"]);
        assert!(!output.status.success(), "expected {code} for:\n{source}");
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert!(
            stderr.contains(&format!("error[{code}]")),
            "expected {code} for:\n{source}\ngot: {stderr}"
        );
        assert!(
            stderr.contains(text),
            "expected `{text}` for:\n{source}\ngot: {stderr}"
        );
        stderr
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

// ---- capped Wasm memory ----

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

/// Lower the memory maximum to one page above the initial size.
fn cap_memory(bytes: &[u8]) -> Vec<u8> {
    assert_eq!(&bytes[..8], b"\0asm\x01\0\0\0");
    let mut module = bytes[..8].to_vec();
    let mut section_start = 8;
    let mut capped = false;
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
            assert!(initial < old_maximum);
            let mut payload = bytes[payload_start..maximum_start].to_vec();
            write_uleb(initial + 1, &mut payload);
            payload.extend_from_slice(&bytes[cursor..section_end]);
            module.push(id);
            write_uleb(payload.len() as u32, &mut module);
            module.extend_from_slice(&payload);
            capped = true;
        }
        section_start = section_end;
    }
    assert!(capped, "Wasm memory section");
    module
}

/// Build `source`, cap its memory and run it; returns the process output.
fn run_capped(source: &str) -> (Fixture, Output) {
    let f = Fixture::new();
    f.write("src/app.mb", source);
    let build = f.run(&["build", "--output", "capped.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let path = f.0.join("capped.wasm");
    let original = fs::read(&path).unwrap();
    fs::write(&path, cap_memory(&original)).unwrap();
    let output = f.run(&["run", "capped.wasm", "--no-fuel-limit"]);
    (f, output)
}

// ---- method calls with aggregate arguments ----

const METHOD_ARGS: &str = r#"use alloc::List;
type Pair { a: i32, b: i32 }
type Named { name: string, n: i32 }
type Kind [ Num(i32), Word(string) ]
type Q { v: i32 }
type Wrap<T> { item: T }
interface Scale { fn scale(borrow self, by: Named) -> i32; }
fn make_name(k: i32) -> string {
    let s := "ab".concat("cde");
    let t := s.concat("f");
    if k > 0 { return t; }
    s
}
fn make_named(k: i32) -> Named { let s := make_name(k); Named { name: s, n: k } }
extend Q {
    fn eq_pair(borrow self, r: Pair) -> bool { self.v == r.a }
    fn peek(borrow self, r: borrow Pair) -> i32 { self.v + r.b }
    fn bump(share self, r: share Pair) { self.v += r.a; r.a = 0; }
    fn named(borrow self, n: Named) -> i32 { self.v + n.n + n.name.len() as i32 }
    fn word(borrow self, s: string) -> i32 { if s.len() > 100 { return 0; } self.v + s.len() as i32 }
    fn sees(borrow self, s: borrow string) -> i32 { self.v + s.len() as i32 }
    fn tup(borrow self, t: (string, i32)) -> i32 { self.v + t.0.len() as i32 + t.1 }
    fn kind(borrow self, k: Kind) -> i32 {
        match k { Kind::Num(n) => n, Kind::Word(w) => w.len() as i32 }
    }
    fn arr(borrow self, a: array<i32, 3>) -> i32 { self.v + a[0] + a[2] }
    fn strs(borrow self, a: array<string, 2>) -> i32 { self.v + a[0].len() as i32 + a[1].len() as i32 }
    fn total(borrow self, items: List<i32>) -> i32 { self.v + items.len() as i32 }
    fn pair_opt(borrow self, o: Named?) -> i32 { match o { Some(n) => n.n, None => 0 } }
}
extend Q of Scale {
    fn scale(borrow self, by: Named) -> i32 { self.v * by.n + by.name.len() as i32 }
}
extend Wrap<i32> {
    fn mix(borrow self, p: Pair, n: Named) -> i32 { self.item + p.a + p.b + n.n + n.name.len() as i32 }
}
fn main() -> i32 {
    let q := Q { v: 2 };
    var w := Q { v: 1 };
    let r := Pair { a: 2, b: 3 };
    var s := 0;
    s += q.peek(r.borrow());
    if q.eq_pair(Pair { a: 2, b: 0 }) { s += 1; }
    var p := Pair { a: 5, b: 0 };
    w.bump(p.share());
    s += w.v;
    s += q.named(make_named(1));
    s += q.named(Named { name: "xy", n: 1 });
    s += q.word(make_name(1));
    s += q.word("lit");
    let heap := make_name(0);
    s += q.sees(heap.borrow());
    s += q.tup((make_name(1), 3));
    s += q.kind(Kind::Word(make_name(0))) + q.kind(Kind::Num(4));
    s += q.arr([1, 2, 3]);
    s += q.strs([make_name(1), make_name(0)]);
    let l: List<i32> = [1, 2];
    s += q.total(l);
    s += q.pair_opt(Some(make_named(2)));
    s += q.scale(make_named(3)) of Scale;
    let wr := Wrap<i32> { item: 1 };
    s += wr.mix(Pair { a: 1, b: 1 }, make_named(1));
    s
}
"#;

#[test]
fn method_calls_take_aggregate_arguments_like_function_calls() {
    // Hand-computed per call: 5 + 1 + 6 + 9 + 5 + 8 + 5 + 7 + 11 + 9 + 6 + 13
    // + 4 + 2 + 12 + 10 (the running total is 113).
    assert_eq!(Fixture::new().result(METHOD_ARGS), "Result: i32(113)");
}

#[test]
fn method_argument_diagnostics_match_function_calls() {
    let f = Fixture::new();
    let prelude = "type Pair { a: i32, b: i32 }\ntype Q { v: i32 }\nextend Q {\n    \
        fn eat(borrow self, r: Pair) -> i32 { r.a }\n    \
        fn look(borrow self, r: borrow Pair) -> i32 { r.a }\n    fn bump(share self, r: share Pair) { r.a = self.v; }\n}\n";
    for (body, code, text) in [
        (
            "let q := Q { v: 1 }; let r := Pair { a: 1, b: 2 }; let n := q.eat(r) + r.a; n",
            "BE001",
            "unavailable after a move",
        ),
        ("let q := Q { v: 1 }; q.eat(5)", "TE002", "expected Pair"),
        (
            "let q := Q { v: 1 }; let r := Pair { a: 1, b: 2 }; q.look(r)",
            "TE017",
            "does not match the borrow parameter access",
        ),
        (
            "var q := Q { v: 1 }; let r := Pair { a: 1, b: 2 }; q.bump(r.borrow())",
            "TE017",
            "does not match the share parameter access",
        ),
        (
            "let q := Q { v: 1 }; q.eat(Pair { a: 1, b: 2 }, 3)",
            "TE010",
            "expected 1 method arguments",
        ),
    ] {
        f.rejects(
            &format!("{prelude}fn main() -> i32 {{ {body} }}\n"),
            code,
            text,
        );
    }
}

// ---- heap String and owner call results used directly ----

const CALL_RESULTS: &str = r#"use alloc::List;
type Label { text: string }
type Pair { a: string, n: i32 }
type Kind [ Word(string), Num(i32) ]
fn g() -> string { let s := "ab".concat("cd"); s }
fn h() -> string { g() }
fn r(c: bool) -> string { if c { return g(); } h() }
fn take(s: string) -> i32 { s.len() as i32 }
fn gl() -> Label { Label { text: g() } }
fn gl2() -> Label { gl() }
fn gl3() -> Label { return gl2(); }
fn gp() -> (string, i32) { (g(), 2) }
fn gp2() -> (string, i32) { gp() }
fn gk() -> Kind { Kind::Word(g()) }
fn gk2() -> Kind { gk() }
fn tl(l: Label) -> i32 { l.text.len() as i32 }
extend Label { fn dup(borrow self) -> string { let s := self.text.concat(self.text); s } }
fn main() -> i32 {
    var xs: List<string> = [];
    xs.push(g());
    xs.push(h());
    var x := g();
    x = g();
    x = r(true);
    x.push_str(g());
    let arr := [g(), h()];
    let tup := (g(), 1);
    let opt: string? = Some(g());
    let lab := Label { text: g() };
    let pair := Pair { a: h(), n: 7 };
    let big := [gl(), gl2()];
    var labels: List<Label> = [];
    labels.push(gl3());
    let some_label: Label? = Some(gl());
    let word := lab.dup();
    var n := 0;
    n += xs[0].len() as i32 + xs[1].len() as i32 + xs.len() as i32;
    n += x.len() as i32;
    n += arr[0].len() as i32 + arr[1].len() as i32;
    n += tup.0.len() as i32 + tup.1;
    n += match opt { Some(s) => s.len() as i32, None => 0 };
    n += lab.text.len() as i32 + pair.a.len() as i32 + pair.n;
    n += big[1].text.len() as i32 + labels[0].text.len() as i32;
    n += match some_label { Some(l) => l.text.len() as i32, None => 0 };
    n += take(g()) + take(r(false)) + tl(gl2());
    n += word.len() as i32;
    let t2 := gp2();
    let k := gk2();
    n += t2.0.len() as i32 + t2.1;
    n += match k { Kind::Word(w) => w.len() as i32, Kind::Num(m) => m };
    let picked := if n > 0 { g() } else { h() };
    n + picked.len() as i32
}
"#;

#[test]
fn heap_string_call_results_work_in_every_value_position() {
    // xs: 4 + 4 + 2 = 10; x = 4 + 4 = 8; arr 8; tup 4 + 1; opt 4; lab 4;
    // pair 4 + 7; big 4; labels 4; some_label 4; calls 4 + 4 + 4; dup 8;
    // t2 4 + 2; k 4; picked 4.
    assert_eq!(Fixture::new().result(CALL_RESULTS), "Result: i32(96)");
}

#[test]
fn call_result_forms_in_a_function_tail_and_return() {
    let source = r#"fn g() -> string { let s := "ab".concat("cd"); s }
fn tail() -> string { g() }
fn early(c: bool) -> string { if c { return g(); } let local := g(); local }
fn deep() -> string { tail() }
fn main() -> i32 {
    let a := tail();
    let b := early(true);
    let c := early(false);
    let d := deep();
    (a.len() + b.len() + c.len() + d.len()) as i32
}
"#;
    assert_eq!(Fixture::new().result(source), "Result: i32(16)");
}

const STRESS_ITERATIONS: u32 = 4_096;
const STRESS_BYTES: u32 = 4_096;

fn call_result_stress(clear: &str) -> String {
    let text = "x".repeat(STRESS_BYTES as usize);
    format!(
        r#"use alloc::List;
type Label {{ text: string }}
type Q {{ v: u32 }}
extend Q {{
    fn eat(borrow self, s: string, early: bool) -> u32 {{
        if early {{ return 1; }}
        self.v + s.len() as u32
    }}
    fn eat_label(borrow self, l: Label, early: bool) -> u32 {{
        if early {{ return 2; }}
        l.text.len() as u32
    }}
}}
fn big() -> string {{ let s := "{text}".concat(""); s }}
fn pass() -> string {{ big() }}
fn pass2(early: bool) -> string {{ if early {{ return big(); }} pass() }}
fn label() -> Label {{ Label {{ text: big() }} }}
fn label2() -> Label {{ label() }}
fn main() -> u32 {{
    var i: u32 = 0;
    var total: u32 = 0;
    var xs: List<string> = [];
    let q := Q {{ v: 1 }};
    loop {{
        if i == {STRESS_ITERATIONS} {{ break; }}
        let early := i % 2 == 0;
        total += q.eat(pass2(early), early);
        total += q.eat_label(label2(), early);
        xs.push(pass());
        xs.push(big());
        let a := [pass(), big()];
        let t := (pass(), 1);
        var x := big();
        x = pass();
        x.push_str(pass());
        let some: string? = Some(pass());
        total += match some {{ Some(text) => text.len() as u32 - {STRESS_BYTES}, None => 1 }};
        total += a[0].len() as u32 + t.0.len() as u32 + x.len() as u32 + xs.len() as u32;
        {clear}
        i += 1;
    }}
    total
}}
"#
    )
}

#[test]
fn staged_call_results_and_method_arguments_release_exactly_under_the_cap() {
    let (_f, output) = run_capped(&call_result_stress("xs.clear();"));
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "capped run failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut expected: u32 = 0;
    for i in 0..STRESS_ITERATIONS {
        expected += if i % 2 == 0 {
            3
        } else {
            1 + STRESS_BYTES + STRESS_BYTES
        };
        expected += 4 * STRESS_BYTES + 2;
    }
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).trim(),
        format!("Result: i32({expected})")
    );
}

#[test]
fn mutation_check_keeping_pushed_call_results_exhausts_the_capped_memory() {
    // Without `xs.clear()` the staged results stay alive in the List, so the
    // same program must trap: the cap above really measures the cleanup.
    let (_f, kept) = run_capped(&call_result_stress(""));
    assert!(!kept.status.success(), "{kept:?}");
    assert!(
        String::from_utf8_lossy(&kept.stderr).contains("guest heap allocation failed"),
        "{}",
        String::from_utf8_lossy(&kept.stderr)
    );
}

// ---- integer literals ----

#[test]
fn radix_literals_and_separators_at_every_width() {
    // Each row: a typed `let`, the literal and the decimal it must equal.
    let rows: &[(&str, &str, &str)] = &[
        ("u8", "0xFF", "255"),
        ("u8", "0XfF", "255"),
        ("u8", "0b1111_1111", "255"),
        ("u8", "0o377", "255"),
        ("u8", "1_0", "10"),
        ("i8", "0x7F", "127"),
        ("i8", "-0x80", "-128"),
        ("i8", "-0b1000_0000", "-128"),
        ("i8", "-0o200", "-128"),
        ("u16", "0xFFFF", "65535"),
        ("u16", "0b1111_1111_1111_1111", "65535"),
        ("u16", "0o177_777", "65535"),
        ("i16", "0x7FFF", "32767"),
        ("i16", "-0x8000", "-32768"),
        ("u32", "0xFFFF_FFFF", "4294967295"),
        ("u32", "0o37_777_777_777", "4294967295"),
        ("u32", "4_294_967_295", "4294967295"),
        ("i32", "0x7FFF_FFFF", "2147483647"),
        ("i32", "-0x8000_0000", "-2147483648"),
        (
            "i32",
            "-0b1000_0000_0000_0000_0000_0000_0000_0000",
            "-2147483648",
        ),
        ("u64", "0xFFFF_FFFF_FFFF_FFFF", "18446744073709551615"),
        (
            "u64",
            "0o1_777_777_777_777_777_777_777",
            "18446744073709551615",
        ),
        ("i64", "0x7FFF_FFFF_FFFF_FFFF", "9223372036854775807"),
        ("i64", "-0x8000_0000_0000_0000", "-9223372036854775808"),
        ("u32", "0x0", "0"),
        ("u32", "0b0", "0"),
        ("u32", "0x00_00", "0"),
        ("u32", "1__000", "1000"),
        ("u32", "0xDEAD__BEEF", "3735928559"),
    ];
    let mut body = String::new();
    for (index, (ty, literal, decimal)) in rows.iter().enumerate() {
        body.push_str(&format!(
            "    let v{index}: {ty} = {literal};\n    let w{index}: {ty} = {decimal};\n    \
             if v{index} != w{index} {{ return {}; }}\n",
            index + 1
        ));
    }
    let source = format!("fn main() -> i32 {{\n{body}    0\n}}\n");
    assert_eq!(Fixture::new().result(&source), "Result: i32(0)");
}

#[test]
fn literals_in_floats_consts_patterns_and_untyped_contexts() {
    let source = r#"const MASK: u32 = 0xFF_FF;
const BITS: u8 = 0b1010_0101;
const OCT: i32 = 0o17;
const SHIFTED: u32 = 0x1 << 0b100;
const ARRAY_LEN: u32 = 0b11;
const SUM: u64 = 0xFFFF_FFFF + 1_000;
fn pick(x: u8) -> i32 {
    match x { 0xFF => 1, 0b1 => 2, 0o10 => 3, 1_0 => 4, 0xA | 0xB | 0xC => 5, _ => 0 }
}
fn signed(x: i16) -> i32 { match x { -0x8000 => 1, 0x7FFF => 2, -0b1 => 3, _ => 0 } }
fn main() -> i32 {
    var t := 0;
    if MASK == 65535 { t += 1; }
    if BITS == 165 { t += 1; }
    if OCT == 15 { t += 1; }
    if SHIFTED == 16 { t += 1; }
    if SUM == 4294968295 { t += 1; }
    let arr: array<u8, ARRAY_LEN> = [0xA, 0xB, 0xC];
    t += arr[2] as i32 - 11;
    let rep: array<u8, 0b10> = [0x2; 0b10];
    t += rep[1] as i32;
    t += pick(255) + pick(1) * 10 + pick(8) * 100 + pick(10) * 1000 + pick(0xB) * 10000;
    t += signed(-32768) + signed(32767) * 10 + signed(-1) * 100;
    let f := 1_000.5_0;
    let g := 1e1_0;
    let h := 2_5e-1_0;
    if f > 1000.49 && f < 1000.51 { t += 1; }
    if g > 9.9e9 && g < 1.1e10 { t += 1; }
    if h > 0.0 && h < 1.0e-8 { t += 1; }
    let widened: u64 = 0xFFFF_FFFF_FFFF_FFFF;
    if widened == 18446744073709551615 { t += 1; }
    t += 0x10 + 0b10 + 0o10 + 1_0;
    t
}
"#;
    // 5 const flags, the array element (12 - 11), `rep`, the pattern rows, the signed
    // rows, 3 float flags, `widened` and 16 + 2 + 8 + 10.
    let expected = 5 + 1 + 2 + (1 + 20 + 300 + 4000 + 50000) + (1 + 20 + 300) + 3 + 1 + 36;
    assert_eq!(
        Fixture::new().result(source),
        format!("Result: i32({expected})")
    );
}

#[test]
fn malformed_numeric_literals_are_lexer_errors() {
    let f = Fixture::new();
    for (literal, text) in [
        ("0x", "expected hexadecimal digits after `0x`"),
        ("0b", "expected binary digits after `0b`"),
        ("0o", "expected octal digits after `0o`"),
        ("0x_1", "not allowed directly after `0x`"),
        ("0b_1", "not allowed directly after `0b`"),
        ("0xG", "invalid digit 'G' in hexadecimal literal"),
        ("0b12", "invalid digit '2' in binary literal"),
        ("0o8", "invalid digit '8' in octal literal"),
        ("0xFF_u8", "invalid digit 'u' in hexadecimal literal"),
        ("0x1_", "must be followed by a digit"),
        ("1_", "must be followed by a digit"),
        ("1_000_", "must be followed by a digit"),
        ("1.5_", "must be followed by a digit"),
        ("1e5_", "must be followed by a digit"),
        ("1e_5", "expected exponent digits"),
        (
            "0x1_0000_0000_0000_0000_0000_0000_0000_0000",
            "hexadecimal literal is too large",
        ),
    ] {
        f.rejects(
            &format!("fn main() -> i32 {{ let x := {literal}; 0 }}\n"),
            "SE001",
            text,
        );
    }
}

#[test]
fn radix_literals_keep_the_contextual_range_checks() {
    let f = Fixture::new();
    for (ty, literal) in [
        ("u8", "0x100"),
        ("u8", "0b1_0000_0000"),
        ("i8", "0x80"),
        ("i8", "-0x81"),
        ("u16", "0o200_000"),
        ("i32", "0x8000_0000"),
        ("u32", "0x1_0000_0000"),
        ("i64", "0x8000_0000_0000_0000"),
        ("u64", "0x1_0000_0000_0000_0000"),
    ] {
        let stderr = f.rejects(
            &format!("fn main() -> i32 {{ let x: {ty} = {literal}; 0 }}\n"),
            "TE008",
            "integer literal does not fit",
        );
        assert!(stderr.contains(ty), "{ty} {literal}: {stderr}");
    }
}

// ---- misplaced `Self` ----

#[test]
fn a_misplaced_self_reports_only_se002() {
    let f = Fixture::new();
    for source in [
        "type Cell { next: Self }\nfn main() -> i32 { 0 }\n",
        "const C: Self = 1;\nfn main() -> i32 { 0 }\n",
        "fn id(x: Self) -> i32 { 0 }\nfn main() -> i32 { 0 }\n",
    ] {
        let stderr = f.rejects(source, "SE002", "only available inside an `extend` block");
        assert!(!stderr.contains("NE003"), "{source}\n{stderr}");
        assert!(
            !stderr.contains("unknown type 'Self'"),
            "{source}\n{stderr}"
        );
        // A constant's type is checked separately (TE017), so only the
        // declaration and parameter forms are exactly one diagnostic.
        if !source.starts_with("const") {
            assert_eq!(stderr.matches("error[").count(), 1, "{source}\n{stderr}");
        }
    }
    // An ordinary unknown type is still NE003.
    f.rejects(
        "fn id(x: Missing) -> i32 { 0 }\nfn main() -> i32 { 0 }\n",
        "NE003",
        "unknown type 'Missing'",
    );
}
