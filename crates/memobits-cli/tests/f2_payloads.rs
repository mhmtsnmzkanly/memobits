//! F2: heap payload composition. `Ok(Some(heap))`, `Ok(list)`, struct literals
//! inside `Ok(..)`/`Some(..)`/user variants, `Some(list)`, enum List payloads,
//! `string ! E` and List call results in every value position, Lists in
//! struct, tuple and array storage, tuples holding String-owning enums,
//! unbound String payloads in mixed variants, literal patterns on a
//! `string ! E` payload, and range diagnostics that echo the literal as
//! written.
//!
//! Every runtime check runs from source and from the standalone Wasm artifact
//! (same result, empty stderr). The stress programs run under a Wasm memory
//! capped to the initial size plus one page: a block that a composition or an
//! early return leaves behind makes them trap, and the mutated programs that
//! keep the values prove the cap bites.
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
            "memobits-f2-payloads-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let fixture = Self(path);
        fixture.write(
            "project.toml",
            "[package]\nname='f2'\nentry='app::main'\n[build]\nstack_size=4096\n",
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

// ---- compositions ----

/// `Ok(Some(heap))`, `Ok(list)`, a struct literal inside `Ok(..)` / `Some(..)`
/// / a user variant, `Some(list)`, an enum with a List payload and a heap
/// `Ok(x)` inside `if` branches. Hand-computed total 53.
const PAYLOADS: &str = r#"use alloc::List;
type Label { text: string }
type Pair { name: string, n: i32 }
type E [ Many(List<i32>), Named(Pair), Nothing ]
fn g() -> string { let s := "ab".concat("cd"); s }
fn gl() -> Label { Label { text: g() } }
fn ml(n: i32) -> List<i32> {
    var l: List<i32> = [];
    var i := 0;
    loop { if i == n { break; } l.push(i); i += 1; }
    l
}
fn a1() -> (Label?) ! Error { Ok(Some(gl())) }
fn a2() -> List<i32> ! Error { Ok(ml(3)) }
fn a3() -> Label ! Error { Ok(Label { text: g() }) }
fn a4() -> List<i32>? { Some(ml(5)) }
fn a5(k: i32) -> E {
    if k == 0 { E::Many(ml(7)) } else if k == 1 { E::Named(Pair { name: g(), n: 9 }) } else { E::Nothing }
}
fn a6(c: bool) -> Label ! Error { if c { Ok(gl()) } else { Err(Error { code: 5 }) } }
fn a7() -> Pair? { Some(Pair { name: g(), n: 2 }) }
fn a8() -> (List<i32>?) ! Error { Ok(Some(ml(2))) }
fn main() -> i32 {
    var t := 0;
    t += match a1() { Ok(Some(l)) => l.text.len() as i32, Ok(None) => 100, Err(_) => 101 };
    t += match a2() { Ok(l) => l.len() as i32, Err(_) => 100 };
    t += match a3() { Ok(l) => l.text.len() as i32, Err(_) => 100 };
    t += match a4() { Some(l) => l.len() as i32, None => 100 };
    t += match a5(0) { E::Many(l) => l.len() as i32, E::Named(p) => 100, E::Nothing => 101 };
    t += match a5(1) { E::Many(l) => 100, E::Named(p) => p.name.len() as i32 + p.n, E::Nothing => 101 };
    t += match a5(2) { E::Many(l) => 100, E::Named(p) => 101, E::Nothing => 0 };
    t += match a6(true) { Ok(l) => l.text.len() as i32, Err(e) => 100 };
    t += match a6(false) { Ok(l) => 100, Err(e) => e.code as i32 };
    t += match a7() { Some(p) => p.name.len() as i32 + p.n, None => 100 };
    t += match a8() { Ok(Some(l)) => l.len() as i32, Ok(None) => 100, Err(_) => 101 };
    t
}
"#;

#[test]
fn heap_payloads_compose_inside_results_options_and_variants() {
    assert_eq!(Fixture::new().result(PAYLOADS), "Result: i32(53)");
}

/// `string ! E` call results beyond the immediate consuming match, plus
/// literal patterns on the `Ok` payload. Hand-computed total 268.
const STRING_RESULTS: &str = r#"use alloc::List;
type H { r: string ! Error, n: i32 }
fn g() -> string { let s := "ab".concat("cd"); s }
fn f(n: i32) -> string ! Error { if n > 0 { Ok(g()) } else { Err(Error { code: 3 }) } }
fn eat(r: string ! Error) -> i32 { match r { Ok(s) => s.len() as i32, Err(e) => 100 + e.code as i32 } }
fn pass(n: i32) -> string ! Error { f(n) }
fn pass2(n: i32) -> string ! Error { let r := f(n); r }
fn fwd(n: i32) -> string ! Error {
    let s := try f(n) else e { return Err(e); };
    let t := s.concat("!");
    Ok(t)
}
fn lit(n: i32) -> i32 { match f(n) { Ok("abcd") => 1, Ok(_) => 2, Err(_) => 3 } }
fn lit_or(n: i32) -> i32 { match f(n) { Ok("zz" | "abcd") => 4, Ok(_) => 5, Err(e) => e.code as i32 } }
fn main() -> i32 {
    var t := 0;
    t += eat(f(1));
    t += eat(f(0));
    t += eat(pass(1));
    t += eat(pass2(1));
    t += eat(fwd(1));
    t += eat(fwd(0));
    let r := f(1);
    t += eat(r);
    let h := H { r: f(1), n: 2 };
    t += match h.r { Ok(s) => s.len() as i32 + h.n, Err(_) => 100 };
    let tup := (f(1), 5);
    t += match tup { (Ok(s), n) => s.len() as i32 + n, (Err(_), _) => 100 };
    var xs: List<string ! Error> = [];
    xs.push(f(1));
    xs.push(f(0));
    t += match xs[0] { Ok(s) => s.len() as i32, Err(_) => 100 };
    t += match xs[1] { Ok(_) => 100, Err(e) => e.code as i32 };
    let arr := [f(1), f(0)];
    t += match arr[0] { Ok(s) => s.len() as i32, Err(_) => 100 };
    let o: (string ! Error)? = Some(f(1));
    t += match o { Some(Ok(s)) => s.len() as i32, Some(Err(_)) => 100, None => 101 };
    t += lit(1) + lit(0);
    t += lit_or(1) + lit_or(0);
    t
}
"#;

#[test]
fn string_results_work_beyond_the_immediate_match_with_literal_patterns() {
    assert_eq!(Fixture::new().result(STRING_RESULTS), "Result: i32(268)");
}

/// List call results in every value position. Hand-computed total 39.
const LIST_RESULTS: &str = r#"use alloc::List;
type S { l: List<i32>, n: i32 }
fn ml(n: i32) -> List<i32> {
    var l: List<i32> = [];
    var i := 0;
    loop { if i == n { break; } l.push(i); i += 1; }
    l
}
fn t1() -> List<i32> { ml(3) }
fn t2(c: bool) -> List<i32> { if c { return ml(4); } t1() }
fn eat(l: List<i32>) -> i32 { l.len() as i32 }
fn main() -> i32 {
    var t := 0;
    let a := t2(true);
    let b := t2(false);
    t += a.len() as i32 + b.len() as i32;
    t += eat(t1());
    t += ml(5).len() as i32;
    var outer: List<List<i32>> = [];
    outer.push(ml(2));
    outer.push(t1());
    t += outer[1].len() as i32 + outer.len() as i32;
    var l := ml(1);
    l = t2(true);
    t += l.len() as i32;
    let s := S { l: ml(6), n: 1 };
    t += s.l.len() as i32 + s.n;
    let tup := (ml(2), t1());
    t += tup.0.len() as i32 + tup.1.len() as i32;
    let arr: array<List<i32>, 2> = [ml(1), t1()];
    t += arr[1].len() as i32;
    ml(9);
    t
}
"#;

#[test]
fn list_call_results_work_in_every_value_position() {
    assert_eq!(Fixture::new().result(LIST_RESULTS), "Result: i32(39)");
}

/// Lists in struct fields, tuples and arrays: construction, element and field
/// places, `replace`, `swap`, nested owners, iteration. Total 104.
const LIST_STORAGE: &str = r#"use alloc::List;
type S { l: List<i32>, n: i32 }
type T { a: S, names: List<string> }
fn ml(n: i32) -> List<i32> {
    var l: List<i32> = [];
    var i := 0;
    loop { if i == n { break; } l.push(i); i += 1; }
    l
}
fn mks(n: i32) -> S { S { l: ml(n), n: n } }
fn word() -> string { let s := "ab".concat("cd"); s }
fn count(s: S) -> i32 { s.l.len() as i32 + s.n }
fn main() -> i32 {
    var t := 0;
    var s := mks(3);
    s.l.push(10);
    s.l.push(11);
    t += s.l.len() as i32;
    let old := replace(s.l, ml(2));
    t += old.len() as i32 + s.l.len() as i32;
    var a: array<List<i32>, 2> = [ml(1), ml(4)];
    swap(a[0], a[1]);
    a[0].push(1);
    t += a[0].len() as i32 + a[1].len() as i32;
    a[1] = ml(7);
    t += a[1].len() as i32;
    var tup := (ml(2), 9);
    tup.0.push(1);
    t += tup.0.len() as i32 + tup.1;
    var names: List<string> = [];
    names.push(word());
    names.push(word());
    let nest := T { a: mks(2), names: names };
    t += nest.a.l.len() as i32 + nest.names.len() as i32 + nest.names[0].len() as i32;
    var c := 0;
    loop x in s.l { c += x as i32; }
    t += c;
    t += count(mks(4));
    s.l[0] = 50;
    t += s.l[0] as i32;
    t
}
"#;

#[test]
fn lists_live_in_struct_fields_tuples_and_arrays() {
    assert_eq!(Fixture::new().result(LIST_STORAGE), "Result: i32(104)");
}

/// Tuples that hold String-owning enums: built from a call, moved into a call,
/// returned, kept in arrays, matched in place and by value. Total 40.
const TUPLE_ENUMS: &str = r#"type Kind [ Word(string), Num(i32) ]
fn g() -> string { let s := "ab".concat("cd"); s }
fn gk() -> Kind { Kind::Word(g()) }
fn ret() -> (Kind, i32) { (gk(), 7) }
fn take(t: (Kind, i32)) -> i32 { match t { (Kind::Word(s), n) => s.len() as i32 + n, (Kind::Num(n), m) => n + m } }
fn main() -> i32 {
    var t := 0;
    let a := (gk(), 1);
    t += match a { (Kind::Word(s), n) => s.len() as i32 + n, (Kind::Num(n), _) => n };
    t += match ret() { (Kind::Word(s), n) => s.len() as i32 + n, (Kind::Num(n), _) => n };
    let k := gk();
    let b := (k, 2);
    t += take(b);
    t += take((Kind::Num(3), 4));
    let arr := [(gk(), 1), (Kind::Num(3), 2)];
    t += match arr[0] { (Kind::Word(s), n) => s.len() as i32 + n, (Kind::Num(n), _) => n };
    t += match arr[1] { (Kind::Word(_), _) => 100, (Kind::Num(n), m) => n * m };
    t
}
"#;

#[test]
fn tuples_hold_string_owning_enums() {
    assert_eq!(Fixture::new().result(TUPLE_ENUMS), "Result: i32(40)");
}

/// A variant that mixes String and other payloads, with the String unbound.
const MIXED_VARIANTS: &str = r#"type K [ Two(string, string), One(string, i32), Zero ]
fn g() -> string { let s := "ab".concat("cd"); s }
fn mkk(n: i32) -> K {
    if n == 0 { K::Zero } else if n == 1 { K::One(g(), 5) } else { K::Two(g(), g()) }
}
fn main() -> i32 {
    let a := match mkk(2) { K::Two(_, b) => b.len() as i32, K::One(_, n) => n, K::Zero => 0 };
    let b := match mkk(2) { K::Two(a, _) => a.len() as i32, _ => 0 };
    let c := match mkk(1) { K::One(s, _) => s.len() as i32, _ => 0 };
    let d := match mkk(2) { K::Two(_, _) => 1, _ => 0 };
    let e := match mkk(1) { K::One(_, n) => n, _ => 0 };
    a * 10000 + b * 1000 + c * 100 + d * 10 + e
}
"#;

#[test]
fn unbound_string_payloads_in_mixed_variants_are_released() {
    assert_eq!(Fixture::new().result(MIXED_VARIANTS), "Result: i32(44415)");
}

// ---- capped-memory stress ----

const STRESS_ITERATIONS: u32 = 4_096;
const STRESS_BYTES: u32 = 2_048;
const STRESS_LIST: u32 = 64;

/// Every new composition per iteration, half of the iterations leaving early
/// with all of them still owned. `{keep}` retains a heap value in a List that
/// `{clear}` empties again: the clean program clears it, the mutation does not.
fn stress_program(keep: &str, clear: &str) -> String {
    let text = "x".repeat(STRESS_BYTES as usize);
    format!(
        r#"use alloc::List;
type Label {{ text: string }}
type K [ Two(string, string), One(string, u32), Zero ]
type E [ Many(List<u32>), Named(Label), Nothing ]
type Holder {{ l: List<u32>, name: string }}
fn big() -> string {{ let s := "{text}".concat(""); s }}
fn gl() -> Label {{ Label {{ text: big() }} }}
fn ml() -> List<u32> {{
    var l: List<u32> = [];
    var i: u32 = 0;
    loop {{ if i == {STRESS_LIST} {{ break; }} l.push(i); i += 1; }}
    l
}}
fn mkk(n: u32) -> K {{
    if n == 0 {{ K::Zero }} else if n == 1 {{ K::One(big(), 5) }} else {{ K::Two(big(), big()) }}
}}
fn f(ok: bool) -> string ! Error {{ if ok {{ Ok(big()) }} else {{ Err(Error {{ code: 3 }}) }} }}
fn pass() -> string ! Error {{ f(true) }}
fn a1() -> (Label?) ! Error {{ Ok(Some(gl())) }}
fn a2() -> List<u32> ! Error {{ Ok(ml()) }}
fn a3() -> Label ! Error {{ Ok(Label {{ text: big() }}) }}
fn a4() -> List<u32>? {{ Some(ml()) }}
fn a5(k: u32) -> E {{
    if k == 0 {{ E::Many(ml()) }} else if k == 1 {{ E::Named(Label {{ text: big() }}) }} else {{ E::Nothing }}
}}
fn ret_list() -> List<u32> {{ ml() }}
fn once(i: u32, early: bool, keep: share List<E>, kept: share List<string ! Error>) -> u32 {{
    let a := a1();
    let b := a2();
    let c := a3();
    let d := a4();
    let e := a5(i % 3);
    let r := pass();
    let h := Holder {{ l: ret_list(), name: big() }};
    var arr: array<List<u32>, 2> = [ml(), ret_list()];
    let one: u32 = 1;
    let t := (mkk(1), one);
    let n := match mkk(2) {{ K::Two(_, b) => b.len() as u32, K::One(_, n) => n, K::Zero => 0 }};
    {keep}
    if early {{ return 1; }}
    var total: u32 = n;
    total += match a {{ Ok(Some(l)) => l.text.len() as u32, Ok(None) => 0, Err(_) => 0 }};
    total += match b {{ Ok(l) => l.len() as u32, Err(_) => 0 }};
    total += match c {{ Ok(l) => l.text.len() as u32, Err(_) => 0 }};
    total += match d {{ Some(l) => l.len() as u32, None => 0 }};
    total += match e {{ E::Many(l) => l.len() as u32, E::Named(l) => l.text.len() as u32, E::Nothing => 0 }};
    total += match r {{ Ok(s) => s.len() as u32, Err(_) => 0 }};
    total += h.l.len() as u32 + h.name.len() as u32;
    total += arr[0].len() as u32 + arr[1].len() as u32;
    total += match t {{ (K::One(s, _), m) => s.len() as u32 + m, (_, _) => 0 }};
    total
}}
fn main() -> u32 {{
    var i: u32 = 0;
    var total: u32 = 0;
    var keep: List<E> = [];
    var kept: List<string ! Error> = [];
    loop {{
        if i == {STRESS_ITERATIONS} {{ break; }}
        total += once(i, i % 2 == 0, keep.share(), kept.share());
        {clear}
        i += 1;
    }}
    total
}}
"#
    )
}

fn stress_expected() -> u32 {
    let mut total: u32 = 0;
    for i in 0..STRESS_ITERATIONS {
        total += if i % 2 == 0 {
            1
        } else {
            let e = match i % 3 {
                0 => STRESS_LIST,
                1 => STRESS_BYTES,
                _ => 0,
            };
            // n, Ok(Some(label)), list, label, list, e, string, holder, arrays, tuple.
            STRESS_BYTES
                + STRESS_BYTES
                + STRESS_LIST
                + STRESS_BYTES
                + STRESS_LIST
                + e
                + STRESS_BYTES
                + (STRESS_LIST + STRESS_BYTES)
                + 2 * STRESS_LIST
                + STRESS_BYTES
                + 1
        };
    }
    total
}

#[test]
fn heap_payload_compositions_release_exactly_under_the_cap() {
    let (_f, output) = run_capped(&stress_program("", ""));
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "capped run failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).trim(),
        format!("Result: i32({})", stress_expected())
    );
}

#[test]
fn mutation_check_keeping_payloads_exhausts_the_capped_memory() {
    // The same program, but each iteration also moves a list-carrying variant
    // and a heap `string ! E` into a List that is never emptied (a release
    // removed from the clean program): the cap must trap, so the clean run
    // above really measures the cleanup.
    let keep = "keep.push(E::Many(ml())); kept.push(pass());";
    let (_f, kept) = run_capped(&stress_program(keep, ""));
    assert!(!kept.status.success(), "{kept:?}");
    assert!(
        String::from_utf8_lossy(&kept.stderr).contains("guest heap allocation failed"),
        "{}",
        String::from_utf8_lossy(&kept.stderr)
    );
    // With the clear restored the same shape runs clean.
    let (_f, cleared) = run_capped(&stress_program(keep, "keep.clear(); kept.clear();"));
    assert!(
        cleared.status.success() && cleared.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&cleared.stderr)
    );
}

/// Unbound and partially bound String payloads, List storage that is replaced
/// and swapped, and `string ! E` values stored in fields and Lists: all under
/// the cap with early returns.
fn storage_stress(extra: &str) -> String {
    let text = "x".repeat(STRESS_BYTES as usize);
    format!(
        r#"use alloc::List;
type S {{ l: List<u32>, n: u32 }}
type R {{ r: string ! Error, n: u32 }}
type K [ Two(string, string), One(string, u32), Zero ]
fn big() -> string {{ let s := "{text}".concat(""); s }}
fn ml() -> List<u32> {{
    var l: List<u32> = [];
    var i: u32 = 0;
    loop {{ if i == {STRESS_LIST} {{ break; }} l.push(i); i += 1; }}
    l
}}
fn f() -> string ! Error {{ Ok(big()) }}
fn mkk(n: u32) -> K {{
    if n == 0 {{ K::Zero }} else if n == 1 {{ K::One(big(), 5) }} else {{ K::Two(big(), big()) }}
}}
fn once(early: bool) -> u32 {{
    var s := S {{ l: ml(), n: 1 }};
    s.l = ml();
    let old := replace(s.l, ml());
    var a: array<List<u32>, 2> = [ml(), ml()];
    swap(a[0], a[1]);
    a[1] = ml();
    let r := R {{ r: f(), n: 2 }};
    let three: u32 = 3;
    let tup := (f(), three);
    var rs: List<string ! Error> = [];
    rs.push(f());
    rs.push(f());
    {extra}
    if early {{ return 1; }}
    let m1: u32 = match mkk(2) {{ K::Two(_, _) => 1, _ => 0 }};
    let m2: u32 = match mkk(1) {{ K::One(_, n) => n, _ => 0 }};
    let m: u32 = m1 + m2;
    let v := match r.r {{ Ok(s) => s.len() as u32, Err(_) => 0 }};
    let w := match rs[1] {{ Ok(s) => s.len() as u32, Err(_) => 0 }};
    s.l.len() as u32 + old.len() as u32 + a[0].len() as u32 + m + v + w + r.n
}}
fn main() -> u32 {{
    var i: u32 = 0;
    var total: u32 = 0;
    loop {{
        if i == {STRESS_ITERATIONS} {{ break; }}
        total += once(i % 2 == 0);
        i += 1;
    }}
    total
}}
"#
    )
}

#[test]
fn storage_compositions_release_exactly_under_the_cap() {
    let (_f, output) = run_capped(&storage_stress(""));
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "capped run failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut expected: u32 = 0;
    for i in 0..STRESS_ITERATIONS {
        expected += if i % 2 == 0 {
            1
        } else {
            3 * STRESS_LIST + 1 + 5 + STRESS_BYTES + STRESS_BYTES + 2
        };
    }
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).trim(),
        format!("Result: i32({expected})")
    );
}

// ---- guards and literals inside String-owning tuples ----

/// Guards of owned matches see Strings inside String-owning tuples that sit in
/// enum payloads (and bind the whole tuple), literals test inside them, and a
/// failed guard leaves the owner for the later arms. Total 11275 + 13 + 12.
const GUARDS: &str = r#"type P [ Pair((string, i32)), Nope ]
type Lb { s: string, n: i32 }
type Q [ Box(Lb), Empty ]
fn g() -> string { let s := "ab".concat("cd"); s }
fn mk2() -> P { P::Pair((g(), 3)) }
fn main() -> i32 {
    let a := match mk2() {
        P::Pair((s, n)) if s.len() > 9 => n,
        P::Pair((s, n)) if n > 5 => 7,
        P::Pair(("abcd", n)) if n == 3 => 11,
        P::Pair(_) => 0,
        P::Nope => 9,
    };
    let b := match (mk2(), 4) {
        (P::Pair((s, n)), m) if m > 5 => 1,
        (P::Pair((s, n)), m) if s.len() == 4 && n == m - 1 => 2,
        (_, _) => 3,
    };
    let q := Q::Box(Lb { s: g(), n: 5 });
    let c := match q {
        Q::Box(b) if b.n > 9 => 1,
        Q::Box(b) if b.s.len() == 4 => b.n + 20,
        Q::Box(_) => 3,
        Q::Empty => 4,
    };
    let d := match mk2() { P::Pair(t) if t.1 > 2 => 50, P::Pair(_) => 0, P::Nope => 9 };
    let e := match mk2() { P::Pair(("abcd", n)) => n + 10, P::Pair(_) => 0, P::Nope => 9 };
    let f := match mk2() { P::Pair(("zzzz", n)) => 1, P::Pair((_, n)) => n + 9, P::Nope => 9 };
    a * 1000 + b * 100 + c + d + e + f
}
"#;

#[test]
fn guards_and_literals_see_strings_inside_tuples_in_payloads() {
    // 11 * 1000 + 2 * 100 + 25 + 50 + 13 + 12.
    assert_eq!(Fixture::new().result(GUARDS), "Result: i32(11300)");
}

fn guard_stress() -> String {
    let text = "x".repeat(STRESS_BYTES as usize);
    format!(
        r#"type P [ Pair((string, u32)), Nope ]
fn big() -> string {{ let s := "{text}".concat(""); s }}
fn mk2() -> P {{ P::Pair((big(), 3)) }}
fn once(k: u32) -> u32 {{
    let a: u32 = match mk2() {{
        P::Pair((s, n)) if s.len() > 99999 => n,
        P::Pair((s, n)) if n > 5 => 7,
        P::Pair((s, n)) if n == k => 11,
        P::Pair(_) => 1,
        P::Nope => 9,
    }};
    if k % 2 == 0 {{ return a; }}
    let four: u32 = 4;
    let b: u32 = match (mk2(), four) {{
        (P::Pair((s, n)), m) if m > 5 => 1,
        (P::Pair((s, n)), m) if s.len() == {STRESS_BYTES} && n == m - 1 => 2,
        (_, _) => 3,
    }};
    a + b
}}
fn main() -> u32 {{
    var i: u32 = 0;
    var total: u32 = 0;
    loop {{
        if i == {STRESS_ITERATIONS} {{ break; }}
        total += once(i % 4);
        i += 1;
    }}
    total
}}
"#
    )
}

#[test]
fn guarded_arms_release_exactly_under_the_cap() {
    let (_f, output) = run_capped(&guard_stress());
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "capped run failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    // k = 0: 1; k = 1: 1 + 2; k = 2: 1; k = 3: 11 + 2.
    let expected = (STRESS_ITERATIONS / 4) * (1 + 3 + 1 + 13);
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).trim(),
        format!("Result: i32({expected})")
    );
}

// ---- diagnostics ----

#[test]
fn range_diagnostics_echo_the_literal_as_written() {
    let f = Fixture::new();
    let main = |body: &str| format!("fn main() -> i32 {{ {body} }}\n");
    f.rejects(
        &main("let a := [1, 2]; a[0x10]"),
        "TE008",
        "constant array index 0x10 is out of bounds for length 2",
    );
    f.rejects(
        &main("let a := [1, 2]; a[1_6]"),
        "TE008",
        "constant array index 1_6 is out of bounds",
    );
    f.rejects(
        &main("let x: u8 = 1; match x { 0x1FF => 1, _ => 2 }"),
        "TE030",
        "integer pattern `0x1FF` does not fit u8",
    );
    f.rejects(
        &main("let x: u8 = 1; match x { 0b1_0000_0000 => 1, _ => 2 }"),
        "TE030",
        "integer pattern `0b1_0000_0000` does not fit u8",
    );
    f.rejects(
        &main("let x: i8 = 1; match x { -0x81 => 1, _ => 2 }"),
        "TE030",
        "integer pattern `-0x81` does not fit i8",
    );
    // A decimal literal is echoed unchanged, and checks still use the value.
    f.rejects(
        &main("let a := [1, 2]; a[3]"),
        "TE008",
        "constant array index 3 is out of bounds",
    );
    f.rejects(
        &main("let x: u8 = 1; match x { 300 => 1, _ => 2 }"),
        "TE030",
        "integer pattern `300` does not fit u8",
    );
    assert_eq!(
        Fixture::new().result(
            "fn main() -> i32 { let x: u8 = 255; let a := [10, 20]; let i := match x { 0xFF => a[0x1], _ => 0 }; i }\n"
        ),
        "Result: i32(20)"
    );
}

#[test]
fn moves_out_of_list_storage_stay_rejected() {
    let f = Fixture::new();
    let prelude = "use alloc::List;\ntype S { l: List<i32>, n: i32 }\nfn ml() -> List<i32> { var l: List<i32> = []; l.push(1); l }\n";
    f.rejects(
        &format!(
            "{prelude}fn main() -> i32 {{ let s := S {{ l: ml(), n: 1 }}; let l := s.l; 0 }}\n"
        ),
        "TE022",
        "cannot be moved out by field access",
    );
    f.rejects(
        &format!("{prelude}fn main() -> i32 {{ let a: array<List<i32>, 1> = [ml()]; let l := a[0]; 0 }}\n"),
        "TE022",
        "cannot be moved out by indexing",
    );
    f.rejects(
        &format!(
            "{prelude}fn main() -> i32 {{ let s := S {{ l: ml(), n: 1 }}; s.l.push(2); 0 }}\n"
        ),
        "TE017",
        "push() requires a mutable List local",
    );
}

#[test]
fn structs_mixing_a_string_with_an_owning_enum_field_keep_a_clear_gate() {
    // A nominal struct is transported by value only while every field is a
    // String, a List, a primitive or a nested admitted owner. An enum field
    // that owns heap storage stays outside the shared transport rule; such a
    // struct can still be built, matched in place and released in a scope.
    let f = Fixture::new();
    let prelude = "type Kind [ Word(string), Num(i32) ]\ntype M { name: string, k: Kind }\n\
        fn g() -> string { let s := \"ab\".concat(\"cd\"); s }\n";
    f.rejects(
        &format!(
            "{prelude}fn take(m: M) -> i32 {{ 0 }}\nfn main() -> i32 {{ let m := M {{ name: g(), k: Kind::Num(1) }}; take(m) }}\n"
        ),
        "TE017",
        "a field that is an enum or tuple is not admitted yet",
    );
}
