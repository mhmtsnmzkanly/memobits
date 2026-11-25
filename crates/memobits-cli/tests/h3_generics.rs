//! H3: generics.
//!
//! Several type and const parameters, several bounds per parameter with one
//! evidence per bound, borrowed/shared generic parameters, generic parameters
//! inside compound and function types, higher-order helpers, associated
//! projections through several bounds, generic functions as values, owners
//! through generic code under capped memory, cross-module evidence forwarding
//! and the diagnostics. Every positive program runs from source and as a
//! standalone Wasm artifact.
//! runs from source and as a standalone Wasm artifact.
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
        Self::with(&[("main", source)], "")
    }

    fn with(modules: &[(&str, &str)], extra_manifest: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-h3-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            format!("[package]\nname='h3'\nentry='main::main'\n{extra_manifest}"),
        )
        .unwrap();
        for (name, source) in modules {
            fs::write(path.join(format!("src/{name}.mb")), source).unwrap();
        }
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

/// Compile `source` and return stderr; `check` must fail with `code` and the
/// message must contain `needle`.
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
    let build = f.run(&["build", "--output", "h3.wasm"]);
    assert!(build.status.success(), "{label}: {}", text(&build.stderr));
    let wasm = f.run(&["run", "h3.wasm"]);
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

// ---------------------------------------------------------------------------
// Several parameters, several bounds, evidence per bound

#[test]
fn several_type_and_const_parameters_with_several_bounds() {
    single(
        r#"interface Score { fn score(borrow self) -> i32; }
interface Weight { fn weight(borrow self) -> i32; }
interface Tag { fn tag(borrow self) -> i32; }
type Cat { n: i32 }
type Dog { n: i32 }
extend Cat of Score { fn score(borrow self) -> i32 { self.n } }
extend Cat of Weight { fn weight(borrow self) -> i32 { self.n * 10 } }
extend Dog of Score { fn score(borrow self) -> i32 { self.n + 100 } }
extend Dog of Tag { fn tag(borrow self) -> i32 { 1000 } }
extend Cat of Tag { fn tag(borrow self) -> i32 { 2000 } }

// Two type parameters, one const parameter, three bounds on two parameters.
fn mix<T, U, const N: u32>(a: T, items: borrow array<U, N>, k: i32) -> i32
    where T: Score + Weight, U: Tag {
    a.score() of Score + a.weight() of Weight + items[0].borrow().tag() of Tag + k
}
// Forwarding keeps each bound's evidence.
fn relay<A, B, const N: u32>(a: A, items: borrow array<B, N>) -> i32
    where A: Score + Weight, B: Tag {
    mix(a, items, 1)
}
// The same concrete type under two parameters selects each bound separately.
fn both<T, U>(x: T, y: U) -> i32 where T: Score, U: Score + Tag {
    x.score() of Score + y.score() of Score + y.tag() of Tag
}
fn main() -> i32 {
    let dogs: array<Dog, 2> = [Dog { n: 1 }, Dog { n: 2 }];
    let cats: array<Cat, 1> = [Cat { n: 3 }];
    let one := relay(Cat { n: 4 }, dogs.borrow());
    let two := relay(Cat { n: 5 }, cats.borrow());
    let three := both(Cat { n: 1 }, Dog { n: 2 });
    one + two + three
}
test fn mix_selects_each_bound() {
    let dogs: array<Dog, 2> = [Dog { n: 1 }, Dog { n: 2 }];
    assert(mix(Cat { n: 4 }, dogs.borrow(), 0) == 4 + 40 + 1000);
    assert(both(Cat { n: 1 }, Cat { n: 1 }) == 1 + 1 + 2000);
}
"#,
        1,
        // one = (4 + 40 + 1000 + 1) = 1045; two = (5 + 50 + 2000 + 1) = 2056;
        // three = 1 + 102 + 1000 = 1103
        1045 + 2056 + 1103,
        "multi parameter",
    );
}

#[test]
fn specialization_keys_include_types_consts_and_evidence() {
    let f = Fixture::with(
        &[
            (
                "common",
                r#"pub interface Pick { fn pick(borrow self) -> u32; }
pub type Item { pub value: i32 }
pub fn run<T, U>(a: T, b: U) -> u32 where T: Pick, U: Pick {
    a.pick() of Pick * 10 + b.pick() of Pick
}
pub fn forward<T, U>(a: T, b: U) -> u32 where T: Pick, U: Pick { run(a, b) }
pub fn width<T, const N: u32>(items: array<T, N>) -> u32 { N_OF }
"#,
            ),
            (
                "left",
                r#"use common;
extend common::Item of common::Pick { fn pick(borrow self) -> u32 { 1 } }
pub fn go() -> u32 { common::forward(common::Item { value: 0 }, common::Item { value: 0 }) }
"#,
            ),
            (
                "right",
                r#"use common;
extend common::Item of common::Pick { fn pick(borrow self) -> u32 { 2 } }
pub fn go() -> u32 { common::forward(common::Item { value: 0 }, common::Item { value: 0 }) }
"#,
            ),
            (
                "main",
                r#"use left;
use right;
fn main() -> u32 { left::go() * 100 + right::go() }
"#,
            ),
        ],
        "",
    );
    // `width` needs no const value expression: drop it to keep the module simple.
    let common = fs::read_to_string(f.0.join("src/common.mb")).unwrap();
    fs::write(
        f.0.join("src/common.mb"),
        common.replace(
            "pub fn width<T, const N: u32>(items: array<T, N>) -> u32 { N_OF }\n",
            "",
        ),
    )
    .unwrap();
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{}", text(&source.stderr));
    // left: 1 * 10 + 1 = 11; right: 2 * 10 + 2 = 22
    assert_eq!(text(&source.stdout), "Result: u32(1122)\n");
    assert!(source.stderr.is_empty());
    let build = f.run(&["build", "--output", "keys.wasm"]);
    assert!(build.status.success(), "{}", text(&build.stderr));
    let wasm = f.run(&["run", "keys.wasm"]);
    assert!(wasm.status.success() && wasm.stderr.is_empty());
    assert_eq!(text(&wasm.stdout), "Result: i32(1122)\n");
}

#[test]
fn const_arguments_distinguish_specializations() {
    single(
        r#"fn first<T, const N: u32>(items: array<T, N>) -> T { items[0] }
fn pair<T, U, const N: u32>(items: array<T, N>, other: array<U, N>) -> (T, U) {
    (items[0], other[0])
}
fn main() -> i32 {
    let a: array<i32, 1> = [1];
    let b: array<i32, 2> = [10, 11];
    let c: array<bool, 2> = [true, false];
    let b2: array<i32, 2> = [10, 11];
    let p := pair(b, c);
    let (p0, p1) := p;
    first(a) + first(b2) + p0 + (if p1 { 100 } else { 0 })
}
"#,
        0,
        1 + 10 + 10 + 100,
        "const keys",
    );
}

#[test]
fn several_parameters_on_types_and_their_methods() {
    single(
        r#"type P<A, B, const N: u32> { a: A, b: B, arr: array<A, N> } extend {
    fn first(borrow self) -> A { self.a }
    fn second(borrow self) -> B { self.b }
    fn swapped(self) -> P<B, A, N> { P<B, A, N> { a: self.b, b: self.a, arr: [self.b, self.b] } }
}
fn second_of(q: P<bool, i32, 2>) -> i32 { q.second() }
fn main() -> i32 {
    let p := P<i32, bool, 2> { a: 5, b: true, arr: [1, 2] };
    let q := p.swapped();
    let flag := q.first();
    second_of(q) + (if flag { 10 } else { 0 })
}
"#,
        0,
        15,
        "type methods",
    );
}

// ---------------------------------------------------------------------------
// Borrowed and shared parameters, compound types, function types

#[test]
fn borrowed_shared_and_compound_generic_parameters() {
    single(
        r#"use alloc::List;
type Item { text: string }
fn size_of<T>(x: borrow T) -> i32 { 1 }
fn store<T>(x: share array<T, 2>, v: T) { x[0] = v; }
fn pair_of<A, B>(a: A, b: B) -> (A, B) { (a, b) }
fn first_of<A, B>(p: (A, B)) -> A { let (a, _) := p; a }
fn wrap<T>(x: T) -> T? { Some(x) }
fn okay<T, E>(x: T) -> T ! E { Ok(x) }
fn unwrap_or<T>(o: T?, fallback: T) -> T { match o { Some(v) => v, None => fallback } }
fn pick<T, E>(r: T ! E, fallback: T) -> T { match r { Ok(v) => v, Err(_) => fallback } }
fn keep<T>(xs: List<T>) -> List<T> { xs }
fn passthru<T>(t: T) -> T { t }
fn twice<T>(x: T, f: fn(T) -> T) -> T { f(f(x)) }
fn compose<A, B, C>(f: fn(A) -> B, g: fn(B) -> C, x: A) -> C { g(f(x)) }
fn inc(x: i32) -> i32 { x + 1 }
fn to_bool(x: i32) -> bool { x > 3 }
fn text_len(s: borrow string) -> u32 { s.len() }
fn main() -> i32 {
    let base := "hi".concat("yo");
    let s := passthru(base);
    let label := "abc".concat("d");
    let item0 := Item { text: label };
    let item := passthru(item0);
    let view := item.text.borrow();
    var arr: array<i32, 2> = [1, 2];
    store(arr.share(), 9);
    let p := pair_of(3, true);
    let w: i32? = wrap(4);
    let o: i32 ! Error = okay(5);
    var l: List<u32> = [];
    l.push(7);
    let l2 := keep(l);
    let bumped: fn(i32) -> i32 = passthru;
    let joined: fn(i32, i32) -> (i32, i32) = pair_of;
    let made := joined(2, 3);
    let (joined_first, _) := made;
    let checked := compose(inc, to_bool, 3);
    size_of(s.borrow()) + arr[0] + first_of(p) + unwrap_or(w, 0) + pick(o, 0)
        + twice(1, inc) + bumped(1) + (text_len(view) as i32)
        + (if checked { 100 } else { 0 }) + (joined_first) + (l2.len() as i32)
}
"#,
        0,
        // 1 + 9 + 3 + 4 + 5 + 3 + 1 + 4 + 100 + 2 + 1
        133,
        "compound parameters",
    );
}

#[test]
fn generic_higher_order_helpers_over_arrays_and_lists() {
    single(
        r#"use alloc::List;
fn apply<T, U>(x: T, f: borrow fn(T) -> U) -> U { f(x) }
fn fold_list<A>(xs: borrow List<u32>, init: A, f: borrow fn(A, u32) -> A) -> A {
    var acc := init;
    var i: u32 = 0;
    loop {
        match xs.get(i) {
            Some(x) => { acc = f(acc, x); },
            None => { break; },
        }
        i += 1;
    }
    acc
}
fn map_into<T, U, const N: u32>(src: array<T, N>, dst: share array<U, N>, f: borrow fn(T) -> U) {
    var i: u32 = 0;
    loop x in src { dst[i] = f(x); i += 1; }
}
fn each(xs: borrow List<u32>, f: share fn(u32)) {
    var i: u32 = 0;
    loop {
        match xs.get(i) {
            Some(x) => { f(x); },
            None => { break; },
        }
        i += 1;
    }
}
fn fold_array<T, A>(xs: array<T, 3>, init: A, f: borrow fn(A, T) -> A) -> A {
    var acc := init;
    loop x in xs { acc = f(acc, x); }
    acc
}
fn square(x: i32) -> i32 { x * x }
fn main() -> i32 {
    var l: List<u32> = [];
    l.push(1); l.push(2); l.push(3);
    let offset: u32 = 10;
    let sum: u32 = fold_list(l.borrow(), 0, fn(a, x) => a + x + offset);
    var seen: u32 = 0;
    each(l.borrow(), fn(x) { seen += x; });
    let doubled := apply(21, fn(x) => x * 2);
    let squared := apply(6, square);
    let flag := apply(7, fn(x) => x > 3);
    var mapped: array<i32, 3> = [0, 0, 0];
    map_into([1, 2, 3], mapped.share(), fn(x) => x + offset as i32);
    let total := fold_array([1, 2, 3], 0, fn(a, x) => a + x) + mapped[2];
    let as_text := fold_array([1, 2, 3], false, fn(a, x) => a || x == 2);
    (sum as i32) + (seen as i32) + doubled + squared + (if flag { 1000 } else { 0 })
        + total + (if as_text { 10000 } else { 0 })
}
"#,
        0,
        // sum = 36, seen = 6, doubled = 42, squared = 36, flag 1000, total 6, 10000
        36 + 6 + 42 + 36 + 1000 + 6 + 13 + 10000,
        "higher order",
    );
}

// ---------------------------------------------------------------------------
// Associated projections

#[test]
fn projections_through_several_bounds() {
    single(
        r#"use core::ops::Add;
use core::ops::Sub;
type V { x: i32 }
extend V of Add { type Rhs = V; type Output = V; fn add(self, rhs: V) -> V { V { x: self.x + rhs.x } } }
extend V of Sub { type Rhs = i32; type Output = i32; fn sub(self, rhs: i32) -> i32 { self.x - rhs } }
interface Make { type Output; fn make(borrow self) -> i32; }
extend V of Make { type Output = bool; fn make(borrow self) -> i32 { self.x } }

// `Output` is defined by Add, Sub and Make: the written type names the bound.
fn sum<T>(left: T, right: T::Add::Rhs) -> T::Add::Output where T: Add + Sub + Make {
    left + right
}
fn diff<T>(left: T, right: T::Sub::Rhs) -> T::Sub::Output where T: Add + Sub {
    left - right
}
// Only one bound defines `Rhs` that is not shared: the short form works.
fn only_make<T>(x: T) -> T::Make::Output where T: Make { true }
fn main() -> i32 {
    let s := sum(V { x: 1 }, V { x: 2 });
    let d := diff(V { x: 10 }, 4);
    let m := only_make(V { x: 0 });
    s.x + d + (if m { 100 } else { 0 })
}
"#,
        0,
        3 + 6 + 100,
        "projections",
    );
}

// ---------------------------------------------------------------------------
// Generic functions as values

#[test]
fn generic_functions_as_values_with_several_parameters() {
    single(
        r#"interface Score { fn score(borrow self) -> i32; }
type Cat { n: i32 }
extend Cat of Score { fn score(borrow self) -> i32 { self.n } }
fn pair_of<A, B>(a: A, b: B) -> (A, B) { (a, b) }
fn first_of<A, B>(a: A, b: B) -> A { a }
fn scored<T, U>(a: T, b: U) -> i32 where T: Score, U: Score { a.score() of Score + b.score() of Score }
fn apply2<A, B, R>(f: fn(A, B) -> R, a: A, b: B) -> R { f(a, b) }
fn main() -> i32 {
    let f: fn(i32, bool) -> (i32, bool) = pair_of;
    let g: fn(i32, bool) -> i32 = first_of;
    let h: fn(Cat, Cat) -> i32 = scored;
    let r := apply2(first_of, 5, true);
    let s := apply2(scored, Cat { n: 1 }, Cat { n: 2 });
    let made := f(1, true);
    let (made0, _) := made;
    made0 + g(10, false) + h(Cat { n: 3 }, Cat { n: 4 }) + r + s
}
"#,
        0,
        1 + 10 + 7 + 5 + 3,
        "generic values",
    );
}

// ---------------------------------------------------------------------------
// Owners through generic code under capped memory

#[test]
fn owners_through_generic_code_release_exactly_under_capped_memory() {
    let text_value = "x".repeat(TEXT_BYTES);
    let source = r#"use alloc::List;
type Label { text: string, n: u32 }
type Outer { inner: Label, k: u32 }
interface Size { fn size(borrow self) -> u32; }
extend Label of Size { fn size(borrow self) -> u32 { self.n + self.text.len() } }
extend Outer of Size { fn size(borrow self) -> u32 { self.k + self.inner.text.len() } }
fn pass<T>(x: T) -> T { x }
fn relay<T>(x: T) -> T { pass(x) }
fn consume<T>(x: T, f: fn(T) -> u32) -> u32 { f(x) }
fn measure<T>(x: T) -> u32 where T: Size { x.size() of Size }
fn forward_measure<T>(x: T) -> u32 where T: Size { measure(x) }
fn view<T>(x: borrow T, f: borrow fn(borrow T) -> u32) -> u32 { f(x) }
fn maybe<T>(x: T) -> T? { Some(x) }
fn both<A, B>(a: A, b: B, f: fn(A, B) -> u32) -> u32 { f(a, b) }
fn text_len(s: string) -> u32 { s.len() }
fn peek(s: borrow string) -> u32 { s.len() }
fn sum_two(a: string, b: Label) -> u32 { a.len() + b.n }
fn round() -> u32 {
    let a := "TEXT".concat("");
    let a1 := relay(a);
    let r1 := a1.len();
    let b := "TEXT".concat("");
    let r2 := consume(b, text_len);
    let c := "TEXT".concat("");
    let r3 := view(c.borrow(), peek);
    let d := "TEXT".concat("");
    let r4 := match maybe(d) { Some(v) => v.len(), None => 0 };
    let e := "TEXT".concat("");
    let r5 := forward_measure(Label { text: e, n: 3 });
    let f := "TEXT".concat("");
    let r6 := forward_measure(relay(Outer { inner: Label { text: f, n: 2 }, k: 5 }));
    let g := "TEXT".concat("");
    let h := "TEXT".concat("");
    let r7 := both(g, Label { text: h, n: 6 }, sum_two);
    var l: List<u32> = [];
    l.push(1);
    let l2 := pass(l);
    r1 + r2 + r3 + r4 + r5 + r6 + r7 + l2.len()
}
fn main() -> u32 {
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {
        if iteration == ITERATIONS { break; }
        total += round();
        iteration += 1;
    }
    total
}
"#
    .replace("TEXT", &text_value)
    .replace("ITERATIONS", &ITERATIONS.to_string());
    let f = Fixture::new(&source);
    fs::write(
        f.0.join("project.toml"),
        "[package]\nname='h3'\nentry='main::main'\n[build]\nstack_size=4096\n",
    )
    .unwrap();
    let t = TEXT_BYTES as u64;
    let per_round = t // relay
        + t // consume
        + t // view
        + t // maybe
        + (3 + t) // Label size
        + (5 + t) // Outer size
        + (6 + t) // both
        + 1; // list
    let expected = per_round * u64::from(ITERATIONS);
    let source_run = f.run(&["run"]);
    assert!(
        source_run.status.success() && source_run.stderr.is_empty(),
        "source run: {}",
        text(&source_run.stderr)
    );
    assert_eq!(
        text(&source_run.stdout),
        format!("Result: u32({expected})\n")
    );
    let build = f.run(&["build", "--output", "owners.wasm"]);
    assert!(build.status.success(), "{}", text(&build.stderr));
    let wasm = f.run(&["run", "owners.wasm"]);
    assert!(wasm.status.success(), "wasm run: {}", text(&wasm.stderr));
    assert_eq!(text(&wasm.stdout), format!("Result: i32({expected})\n"));
    let path = f.0.join("owners.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&path).unwrap());
    fs::write(&path, capped).unwrap();
    let wasm = f.run(&["run", "owners.wasm"]);
    assert!(
        wasm.status.success(),
        "capped Wasm run failed: {}",
        text(&wasm.stderr)
    );
    assert_eq!(text(&wasm.stdout), format!("Result: i32({expected})\n"));
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(&path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

// ---------------------------------------------------------------------------
// Cross-module evidence forwarding

#[test]
fn evidence_forwards_across_modules_per_bound() {
    let f = Fixture::with(
        &[
            (
                "common",
                r#"pub interface Left { fn left(borrow self) -> i32; }
pub interface Right { fn right(borrow self) -> i32; }
pub type Item { pub value: i32 }
pub fn inspect<T, U>(a: T, b: U) -> i32 where T: Left + Right, U: Left {
    a.left() of Left * 100 + a.right() of Right * 10 + b.left() of Left
}
pub fn relay<A, B>(a: A, b: B) -> i32 where A: Left + Right, B: Left { inspect(a, b) }
"#,
            ),
            (
                "one",
                r#"use common;
extend common::Item of common::Left { fn left(borrow self) -> i32 { 1 } }
extend common::Item of common::Right { fn right(borrow self) -> i32 { 2 } }
pub fn run() -> i32 {
    common::relay(common::Item { value: 0 }, common::Item { value: 0 })
}
"#,
            ),
            (
                "two",
                r#"use common;
extend common::Item of common::Left { fn left(borrow self) -> i32 { 3 } }
extend common::Item of common::Right { fn right(borrow self) -> i32 { 4 } }
pub fn run() -> i32 {
    common::relay(common::Item { value: 0 }, common::Item { value: 0 })
}
"#,
            ),
            (
                "main",
                "use one;\nuse two;\nfn main() -> i32 { one::run() + two::run() }\n",
            ),
        ],
        "",
    );
    // one: 1 * 100 + 2 * 10 + 1 = 121; two: 3 * 100 + 4 * 10 + 3 = 343
    verify(&f, 0, 121 + 343, "cross module");
}

// ---------------------------------------------------------------------------
// Negative cases

const HEADER: &str = r#"interface A { fn fetch(borrow self) -> i32; type Output; }
interface B { fn fetch(borrow self) -> i32; type Output; }
type X { v: i32 }
type Y { v: i32 }
extend X of A { type Output = i32; fn fetch(borrow self) -> i32 { self.v } }
extend X of B { type Output = bool; fn fetch(borrow self) -> i32 { self.v } }
extend Y of A { type Output = i32; fn fetch(borrow self) -> i32 { self.v } }
"#;

fn rejects_with_header(body: &str, code: &str, needle: &str) {
    rejects(&format!("{HEADER}{body}"), code, needle);
}

#[test]
fn missing_evidence_names_the_failing_bound() {
    rejects_with_header(
        "fn f<T, U>(x: T, y: U) -> i32 where T: A + B, U: A { 1 }\nfn main() -> i32 { f(Y { v: 1 }, Y { v: 2 }) }\n",
        "TE007",
        "no visible implementation of 'main::B' for Y satisfies generic bound 'T: main::B'",
    );
    rejects_with_header(
        "fn f<T, U>(x: T, y: U) -> i32 where T: A, U: B { 1 }\nfn main() -> i32 { f(X { v: 1 }, Y { v: 2 }) }\n",
        "TE007",
        "bound 'U: main::B'",
    );
}

#[test]
fn ambiguous_evidence_and_ambiguous_methods_are_reported() {
    rejects(
        r#"interface A { fn a(borrow self) -> i32; }
type X { v: i32 }
extend X of A { fn a(borrow self) -> i32 { 1 } }
extend X of A { fn a(borrow self) -> i32 { 2 } }
fn f<T>(x: T) -> i32 where T: A { x.a() of A }
fn main() -> i32 { f(X { v: 1 }) }
"#,
        "TE007",
        "ambiguous generic evidence for bound 'T: main::A'",
    );
    rejects_with_header(
        "fn f<T>(x: T) -> i32 where T: A + B { x.fetch() }\nfn main() -> i32 { f(X { v: 1 }) }\n",
        "TE024",
        "method 'fetch' is provided by the bounds 'T: main::A' and 'T: main::B'",
    );
}

#[test]
fn ambiguous_and_nested_projections_are_reported() {
    rejects_with_header(
        "fn f<T>(x: T) -> T::Output where T: A + B { x.fetch() of A }\nfn main() -> i32 { f(X { v: 1 }) }\n",
        "TE008",
        "associated type 'Output' of 'T' is ambiguous",
    );
    rejects_with_header(
        "fn f<T>(x: T) -> T::A::Output::Deeper where T: A + B { 1 }\nfn main() -> i32 { 0 }\n",
        "NE008",
        "nested associated type projection",
    );
    rejects_with_header(
        "fn f<T>(x: T) -> T::Output::Deeper where T: A { 1 }\nfn main() -> i32 { f(Y { v: 1 }) }\n",
        "TE008",
        "'Output' is not an interface bound of 'T'",
    );
}

#[test]
fn inference_and_declaration_errors() {
    rejects(
        "fn f<T, U>(x: T) -> i32 { 1 }\nfn main() -> i32 { f(1) }\n",
        "TE002",
        "cannot infer the type argument 'U' of generic function 'f'",
    );
    rejects(
        "fn f<T, const N: u32>() -> i32 { 1 }\nfn main() -> i32 { f() }\n",
        "TE002",
        "cannot infer the type argument 'T'",
    );
    rejects(
        "fn f<T>(a: T, b: T) -> T { a }\nfn main() -> i32 { f(1, true) }\n",
        "TE002",
        "expected i32, found bool",
    );
    rejects(
        "fn f<T, U>(a: T, g: fn(T) -> U) -> U { g(a) }\nfn main() -> i32 { f(1, fn(x) => x > 0) }\n",
        "TE002",
        "expected i32, found bool",
    );
    rejects(
        "fn f<T>(a: T) -> T { a }\nfn main() -> i32 { f(1, 2) }\n",
        "TE010",
        "expected 1 arguments, found 2",
    );
    rejects(
        "interface A { fn a(borrow self) -> i32; }\nfn f<T>(a: T) -> T where U: A { a }\nfn main() -> i32 { 0 }\n",
        "TE007",
        "names 'U', which is not a type parameter of 'f'",
    );
    rejects(
        "fn f<const N: i32>(a: i32) -> i32 { a }\nfn main() -> i32 { 0 }\n",
        "TE007",
        "const parameter 'N' must have type u32",
    );
    rejects(
        "fn f<T, T>(a: T) -> T { a }\nfn main() -> i32 { 0 }\n",
        "TE007",
        "declared more than once",
    );
    rejects(
        "fn f<T>(g: fn(T) -> T) -> i32 { 1 }\nfn main() -> i32 { f(fn(x) => x) }\n",
        "TE002",
        "cannot infer the parameter types of this function literal",
    );
    rejects(
        "fn id<T>(x: T) -> T { x }\nfn main() -> i32 { let f := id; 0 }\n",
        "TE002",
        "cannot be used as a value without an expected function type",
    );
    rejects(
        "fn pair_of<A, B>(a: A, b: B) -> (A, B) { (a, b) }\nfn main() -> i32 { let f: fn(i32) -> i32 = pair_of; 0 }\n",
        "TE010",
        "takes 2 arguments",
    );
}

#[test]
fn wrong_arity_and_kind_of_type_arguments() {
    rejects(
        "type P<A, B> { a: A, b: B }\nfn main() -> i32 { let p: P<i32> = P<i32> { a: 1 }; 0 }\n",
        "TE002",
        "type 'P' requires 2 generic arguments",
    );
    rejects(
        "type P<A, const N: u32> { a: A }\nfn main() -> i32 { let p: P<i32, i32> = P<i32, i32> { a: 1 }; 0 }\n",
        "TE002",
        "generic argument for 'N' has the wrong kind",
    );
}

#[test]
fn specialization_limit_and_conflicting_consts() {
    rejects(
        "type Wrap<T> { v: T }\nfn grow<T>(x: T) -> i32 { grow(Wrap<T> { v: x }) }\nfn main() -> i32 { grow(1) }\n",
        "TE007",
        "generic specialization limit exceeded (maximum 256 distinct functions)",
    );
    rejects(
        "fn same<T, const N: u32>(a: array<T, N>, b: array<T, N>) -> T { a[0] }\nfn main() -> i32 { let one: array<i32, 1> = [1]; let two: array<i32, 2> = [2, 3]; same(one, two) }\n",
        "TE002",
        "expected array<i32, 1>, found array<i32, 2>",
    );
}
