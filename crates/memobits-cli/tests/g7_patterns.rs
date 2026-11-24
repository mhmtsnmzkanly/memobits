//! G7: literal, constant, or- and guarded patterns end to end.
//!
//! Every runtime check runs from source and from the standalone Wasm
//! artifact (same result, empty stderr). The owned-guard stress runs under a
//! Wasm memory capped to the initial size plus one page, so any block that a
//! failed guard, an or-pattern leaf or an early return leaves behind makes it
//! trap; a mutated program that keeps the bound payload proves the cap bites.
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
            "memobits-g7-patterns-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let fixture = Self(path);
        fixture.write(
            "project.toml",
            "[package]\nname='g7'\nentry='app::main'\n[build]\nstack_size=4096\n",
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

const LITERAL_KINDS: &str = r#"
fn int_kinds(a: i8, b: u8, c: i16, d: u16, e: i32, f: u32, g: i64, h: u64) -> u32 {
    var n: u32 = 0;
    n += match a { -128 => 1, 127 => 2, -1 => 4, _ => 0 };
    n += match b { 0 => 8, 255 => 16, _ => 0 };
    n += match c { -32768 => 32, 32767 => 64, _ => 0 };
    n += match d { 65535 => 128, _ => 0 };
    n += match e { -2147483648 => 256, 2147483647 => 512, _ => 0 };
    n += match f { 4294967295 => 1024, _ => 0 };
    n += match g { -9223372036854775808 => 2048, 9223372036854775807 => 4096, _ => 0 };
    n += match h { 18446744073709551615 => 8192, _ => 0 };
    n
}
fn kinds(flag: bool, ch: char, word: string) -> i32 {
    let a := match flag { true => 1, false => 2 };
    let b := match ch { 'a' => 10, '\n' => 20, '😀' => 30, _ => 40 };
    let c := match word { "" => 100, "é" => 200, "hello" => 300, _ => 400 };
    a + b + c
}
fn main() -> i32 {
    let ints := int_kinds(-128, 255, 32767, 65535, -2147483648, 4294967295, 9223372036854775807, 18446744073709551615)
        + int_kinds(127, 0, -32768, 1, 2147483647, 0, -9223372036854775808, 5);
    let text := kinds(true, 'a', "") + kinds(false, '😀', "é") + kinds(true, '\n', "hello") + kinds(false, 'z', "nope");
    ints as i32 + text
}
"#;

const NESTED_LITERALS: &str = r#"
type Wrap [ Num(i32), Word(string), Both(i32, bool), Neither ]
fn outcome(r: i32? ! Error) -> i32 {
    match r {
        Ok(Some(7)) => 1,
        Ok(Some(-1)) => 2,
        Ok(Some(_)) => 3,
        Ok(None) => 4,
        Err(_) => 5,
    }
}
fn pair(t: (i32, bool)) -> i32 {
    match t {
        (0, true) => 10,
        (0, false) => 20,
        (1, _) => 30,
        (_, true) => 40,
        (_, false) => 50,
    }
}
fn words(s: string?) -> i32 {
    match s {
        Some("x") => 100,
        Some("") => 200,
        Some(_) => 300,
        None => 400,
    }
}
fn wrapped(w: Wrap) -> i32 {
    match w {
        Wrap::Num(5) => 1,
        Wrap::Num(n) => n,
        Wrap::Word("static") => 2,
        Wrap::Word("heap") => 3,
        Wrap::Word(s) => s.len() as i32,
        Wrap::Both(0, true) => 4,
        Wrap::Both(_, _) => 5,
        Wrap::Neither => 6,
    }
}
fn nested_tuple(t: ((i32, char), u8?)) -> i32 {
    match t {
        ((1, 'a'), Some(3)) => 1,
        ((1, 'a'), _) => 2,
        ((_, 'b'), None) => 3,
        _ => 4,
    }
}
fn main() -> i32 {
    let a: i32? ! Error = Ok(Some(7));
    let b: i32? ! Error = Ok(Some(-1));
    let c: i32? ! Error = Ok(Some(8));
    let d: i32? ! Error = Ok(None);
    let e: i32? ! Error = Err(Error { code: 1 });
    let mut_out := outcome(a) + outcome(b) * 10 + outcome(c) * 100 + outcome(d) * 1000 + outcome(e) * 10000;
    let tuples := pair((0, true)) + pair((0, false)) + pair((1, true)) + pair((9, true)) + pair((9, false));
    let w1: string? = Some("x");
    let heap := "ab".concat("");
    let w2: string? = Some(heap);
    let w3: string? = None;
    let w4: string? = Some("");
    let opts := words(w1) + words(w2) + words(w3) + words(w4);
    let h := "he".concat("ap");
    let wraps := wrapped(Wrap::Num(5)) + wrapped(Wrap::Num(9)) + wrapped(Wrap::Word("static")) + wrapped(Wrap::Word(h))
        + wrapped(Wrap::Word("abcd")) + wrapped(Wrap::Both(0, true)) + wrapped(Wrap::Both(1, true)) + wrapped(Wrap::Neither);
    let n1: ((i32, char), u8?) = ((1, 'a'), Some(3));
    let n2: ((i32, char), u8?) = ((1, 'a'), None);
    let n3: ((i32, char), u8?) = ((2, 'b'), None);
    let n4: ((i32, char), u8?) = ((2, 'c'), None);
    let deep := nested_tuple(n1) + nested_tuple(n2) + nested_tuple(n3) + nested_tuple(n4);
    mut_out + tuples + opts + wraps + deep
}
"#;

const OR_PATTERNS: &str = r#"
type Shape [ Circle(i32), Square(i32), Tri(i32, i32), Dot ]
type Msg [ A(string), B(string), C ]
fn size(s: Shape) -> i32 {
    match s {
        Shape::Circle(n) | Shape::Square(n) => n,
        Shape::Tri(a, 0) | Shape::Tri(0, a) => a,
        Shape::Tri(a, b) => a + b,
        Shape::Dot => 0,
    }
}
fn pairs(t: (i32?, i32?)) -> i32 {
    match t {
        (Some(x), None) | (None, Some(x)) => x,
        (Some(a), Some(b)) => a * b,
        (None, None) => -1,
    }
}
fn inner(o: i32?) -> i32 {
    match o {
        Some(1 | 2 | 3) => 1,
        Some(4 | 5) => 2,
        Some(_) => 3,
        None => 4,
    }
}
fn grouped(t: (i32, char)) -> i32 {
    match t {
        (1 | 2, 'a' | 'b') => 1,
        ((3 | 4), _) => 2,
        (_, _) => 3,
    }
}
fn both(b: bool, c: bool) -> i32 {
    match (b, c) {
        (true, true) | (false, false) => 1,
        (true | false, _) => 2,
    }
}
fn text(m: Msg) -> u32 {
    match m {
        Msg::A(s) | Msg::B(s) => s.len(),
        Msg::C => 0,
    }
}
fn main() -> i32 {
    let shapes := size(Shape::Circle(3)) + size(Shape::Square(4)) + size(Shape::Tri(5, 0)) + size(Shape::Tri(0, 6))
        + size(Shape::Tri(1, 2)) + size(Shape::Dot);
    let pair_sum := pairs((Some(2), None)) + pairs((None, Some(3))) + pairs((Some(4), Some(5))) + pairs((None, None));
    let inners := inner(Some(2)) + inner(Some(5)) + inner(Some(9)) + inner(None);
    let h := "abc".concat("");
    let h2 := "de".concat("");
    let texts := text(Msg::A(h)) + text(Msg::B(h2)) + text(Msg::C);
    shapes + pair_sum * 100 + inners * 10000 + both(true, true) * 1000000 + both(false, true) * 100000 + texts as i32 + grouped((1, 'b')) * 10000000 + grouped((4, 'z')) * 20000000 + grouped((9, 'a')) * 30000000
}
"#;

const GUARDS: &str = r#"
type Shape [ Circle(i32), Named(string), Empty ]
fn order(n: i32, m: i32) -> i32 {
    match (n, m) {
        (a, b) if a > b => 1,
        (a, _) if a < 0 => 2,
        (0, _) => 3,
        (a, b) if 10 / a == b => 4,
        (_, b) if b == 7 => 5,
        _ => 6,
    }
}
fn shape(s: Shape, limit: i32) -> i32 {
    match s {
        Shape::Circle(r) if r > limit => r,
        Shape::Circle(1 | 2) => 100,
        Shape::Circle(r) if r < 0 => -r,
        Shape::Circle(_) => 101,
        Shape::Named("abc") => 200,
        Shape::Named(n) if n.len() > 3 => n.len() as i32 + 300,
        Shape::Named(_) => 202,
        Shape::Empty => 0,
    }
}
fn borrowed(s: borrow string, flag: bool) -> i32 {
    match s {
        "yes" if flag => 1,
        "yes" => 2,
        t if t.len() > 3 && flag => 3,
        t if t.len() > 3 => 4,
        _ => 5,
    }
}
fn short_circuit(n: i32) -> i32 {
    match n {
        x if x > 0 && 100 / x > 10 => 1,
        x if x < 0 || x == 0 => 2,
        _ => 3,
    }
}
fn main() -> i32 {
    let o := order(5, 3) + order(-1, 3) * 10 + order(0, 3) * 100 + order(2, 5) * 1000 + order(3, 7) * 10000 + order(3, 9) * 100000;
    let h := "abcdef".concat("");
    let s := shape(Shape::Circle(50), 10) + shape(Shape::Circle(2), 10) + shape(Shape::Circle(-4), 10) + shape(Shape::Circle(7), 10)
        + shape(Shape::Named("abc"), 0) + shape(Shape::Named(h), 0) + shape(Shape::Named("xy"), 0) + shape(Shape::Empty, 0);
    let yes := "yes";
    let hello := "hel".concat("lo");
    let a1 := "a";
    let b := borrowed(yes.borrow(), true) + borrowed(yes.borrow(), false) * 10 + borrowed(hello.borrow(), true) * 100
        + borrowed(hello.borrow(), false) * 1000 + borrowed(a1.borrow(), true) * 10000 + hello.len() as i32;
    let c := short_circuit(5) + short_circuit(50) * 10 + short_circuit(-3) * 100 + short_circuit(0) * 1000;
    o + s + b + c
}
"#;

const CONST_MAIN: &str = r#"
use limits::{LIMIT as CAP, NAME};
const LOCAL: u8 = 7;
const FLAG: bool = true;
const GREETING: string = "hi";
const star: char = '*';
const count: u32 = 3;
type Pick [ Known(i32), Other ]
fn scalar(n: i32, s: string, b: u8) -> i32 {
    let a := match n { CAP => 1, limits::LOW => 5, _ => 2 };
    let w := match s { NAME => 10, GREETING => 30, _ => 20 };
    let c := match FLAG { FLAG => 100, _ => 200 };
    let d := match b { LOCAL => 1000, _ => 2000 };
    a + w + c + d
}
fn nested(o: i32?, t: (char, string)) -> i32 {
    let a := match o { Some(CAP) => 1, Some(limits::LOW) | None => 2, Some(_) => 3 };
    let b := match t { (star, GREETING) => 10, (star, _) => 20, _ => 30 };
    a + b
}
fn shadow(CAP: i32) -> i32 {
    match CAP { 5 => 1, _ => 2 }
}
fn picked(p: Pick) -> i32 {
    match p { Pick::Known(CAP) => 1, Pick::Known(_) => 2, Pick::Other => 3 }
}
fn main() -> i32 {
    let arr := [7; count];
    let total := scalar(5, "bob", 7) + scalar(0, "hi", 1) + scalar(-3, "x", 1);
    let n := nested(Some(5), ('*', "hi")) + nested(None, ('*', "zz")) + nested(Some(1), ('q', "hi"));
    total + n + shadow(5) + picked(Pick::Known(5)) + picked(Pick::Other) + arr[2] as i32
}
"#;

const CONST_LIMITS: &str = r#"
pub const LIMIT: i32 = 5;
pub const LOW: i32 = -3;
pub const NAME: string = "bob";
"#;

const STRESS_TEMPLATE: &str = r#"
type Msg [ Text(string), Nil ]
fn judge(m: Msg, early: bool, limit: u32) -> u32 {
    if early { return 1; }
    match m {
        Msg::Text("ab") | Msg::Text("cd") => 7,
        Msg::Text(s) if s.len() > limit => s.len(),
        Msg::Text(_) => 9,
        Msg::Nil => 11,
    }
}
fn pair(t: (string, string), early: bool) -> u32 {
    if early { return 2; }
    match t {
        (a, b) if a.len() == b.len() => a.len() + b.len(),
        (a, _) => a.len(),
    }
}
fn maybe(o: string?, early: bool, limit: u32) -> u32 {
    if early { return 3; }
    match o {
        Some("ab") => 1,
        Some(s) if s.len() > limit => s.len(),
        Some(_) => 2,
        None => 5,
    }
}
fn pack(text: string, kind: u32) -> string? ! Error {
    if kind == 2 { return Err(Error { code: 4 }); }
    if kind == 1 { return Ok(None); }
    let some: string? = Some(text);
    let result: string? ! Error = Ok(some);
    result
}
fn nested(r: string? ! Error, early: bool) -> u32 {
    if early { return 4; }
    match r {
        Ok(Some(s)) if s.len() > 4000 => 1,
        Ok(Some(s)) => s.len(),
        Ok(None) => 7,
        Err(e) if e.code == 4 => 8,
        Err(e) => e.code,
    }
}
fn main() -> u32 {
    var i: u32 = 0;
    var total: u32 = 0;
    loop {
        if i == ITERATIONS { break; }
        let early := i % 2 == 0;
        let kind := (i / 2) % 4;
        let a := "TEXT".concat("");
        let b := "ab".concat("");
        let c := "TEXT".concat("");
        if kind == 0 {
            total += judge(Msg::Text(a), early, 4000);
            total += judge(Msg::Text(b), early, 4000);
        } else if kind == 1 {
            total += pair((a, b), early);
            let b2 := "cd".concat("");
            total += pair((b2, c), early);
        } else if kind == 2 {
            total += maybe(Some(a), early, 4000);
            total += maybe(Some(b), early, 4000);
            let none: string? = None;
            total += maybe(none, early, 4000);
        } else {
            let r1 := pack(a, 0);
            total += nested(r1, early);
            let r2 := pack(b, 0);
            total += nested(r2, early);
            let r3 := pack(c, 1);
            total += nested(r3, early);
            let z := "zz".concat("");
            let r4 := pack(z, 2);
            total += nested(r4, early);
        }
        i += 1;
    }
    total
}
"#;

#[test]
fn literal_patterns_of_every_kind_run_from_source_and_wasm() {
    // Integer widths (including both extremes of each signed type), bool,
    // char and string literals; 16,379 + 1,106.
    assert_eq!(Fixture::new().result(LITERAL_KINDS), "Result: i32(17485)");
}

#[test]
fn literals_nest_in_variants_tuples_and_static_or_heap_strings() {
    assert_eq!(Fixture::new().result(NESTED_LITERALS), "Result: i32(55515)");
}

#[test]
fn string_scrutinees_are_compared_in_place_and_not_moved() {
    // `heap` keeps its storage after matching; the match compares bytes.
    assert_eq!(
        Fixture::new().result(
            r#"
fn len_after(s: string) -> u32 {
    let tag: u32 = match s { "abc" => 1, "abd" => 2, "" => 3, _ => 4 };
    tag + s.len()
}
fn main() -> u32 {
    let heap := "ab".concat("c");
    let other := "abcd".concat("");
    let empty := "".concat("");
    len_after(heap) + len_after(other) * 10 + len_after(empty) * 100
}
"#
        ),
        // heap: 1 + 3; other: (4 + 4) * 10; empty: (3 + 0) * 100
        "Result: u32(384)"
    );
}

#[test]
fn or_patterns_bind_the_same_names_at_any_depth() {
    assert_eq!(Fixture::new().result(OR_PATTERNS), "Result: i32(141302426)");
}

#[test]
fn guards_fall_through_and_see_the_bindings() {
    // Includes a guard that would trap (division by zero) if it ran for an
    // arm whose pattern did not match.
    assert_eq!(Fixture::new().result(GUARDS), "Result: i32(711841)");
}

#[test]
fn constants_are_patterns_and_repeat_counts_take_any_const_name() {
    let f = Fixture::new();
    f.write("src/limits.mb", CONST_LIMITS);
    assert_eq!(f.result(CONST_MAIN), "Result: i32(5446)");
}

#[test]
fn a_variant_of_the_matched_enum_wins_over_a_constant_of_the_same_name() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            r#"
type Pick [ Low, High ]
const High: i32 = 1;
fn f(p: Pick) -> i32 { match p { Low => 10, High => 20 } }
fn g(n: i32) -> i32 { match n { High => 1, _ => 2 } }
fn main() -> i32 { f(Pick::Low) + f(Pick::High) + g(1) * 100 + g(5) * 1000 }
"#
        ),
        "Result: i32(2130)"
    );
}

#[test]
fn guarded_arms_do_not_count_for_exhaustiveness() {
    let f = Fixture::new();
    let text = f.rejects(
        "fn main() -> i32 { match true { true => 1, false if 1 > 2 => 2 } }",
        "TE031",
        "missing `false`",
    );
    assert!(text.contains("`if` guard do not count"), "{text}");
    f.rejects(
        "fn main() -> i32 { match Some(1) { Some(n) if n > 0 => n, None => 0 } }",
        "TE031",
        "missing `Some(_)`",
    );
    // With an unguarded fallback the same arms are exhaustive.
    f.write(
        "src/app.mb",
        "fn main() -> i32 { match Some(1) { Some(n) if n > 0 => n, Some(_) => 5, None => 0 } }",
    );
    assert!(f.run(&["check"]).status.success());
}

#[test]
fn literal_domains_are_infinite_except_bool() {
    let f = Fixture::new();
    f.rejects(
        "fn main() -> i32 { match 3 { 1 => 1, 2 => 2 } }",
        "TE031",
        "add a `_` arm or a binding arm",
    );
    f.rejects(
        "fn main() -> i32 { match 'a' { 'a' => 1, 'b' => 2 } }",
        "TE031",
        "add a `_` arm",
    );
    f.rejects(
        "fn main() -> i32 { match \"a\" { \"a\" => 1 } }",
        "TE031",
        "add a `_` arm",
    );
    f.rejects(
        "fn main() -> i32 { match (true, 1) { (true, 1) => 1, (false, _) => 2, (true, 2) => 3 } }",
        "TE031",
        "missing `(true, _)`",
    );
    f.rejects(
        "fn main() -> i32 { match true { true => 1 } }",
        "TE031",
        "missing `false`",
    );
    // `true` and `false` cover bool; a binding covers any literal domain.
    for source in [
        "fn main() -> i32 { match true { true => 1, false => 2 } }",
        "fn main() -> i32 { match 3 { 1 => 1, n => n } }",
        "fn main() -> i32 { match (true, 1) { (true, 1) => 1, (true, _) => 3, (false, _) => 2 } }",
    ] {
        f.write("src/app.mb", source);
        let check = f.run(&["check"]);
        assert!(
            check.status.success(),
            "{source}: {}",
            String::from_utf8_lossy(&check.stderr)
        );
    }
}

#[test]
fn unreachable_arms_are_rejected() {
    let f = Fixture::new();
    f.rejects(
        "fn main() -> i32 { match 3 { 1 => 1, 1 => 3, _ => 2 } }",
        "TE032",
        "pattern `1` is already matched",
    );
    f.rejects(
        "fn main() -> i32 { match 3 { _ => 1, 1 => 3 } }",
        "TE032",
        "earlier `_` arm",
    );
    f.rejects(
        "fn main() -> i32 { match 3 { n => 1, 1 => 3 } }",
        "TE032",
        "earlier `_` arm",
    );
    f.rejects(
        "fn main() -> i32 { match true { true => 1, false => 2, true => 3 } }",
        "TE032",
        "already matched",
    );
    f.rejects(
        "fn main() -> i32 { match 3 { 1 | 2 => 1, 2 => 3, _ => 2 } }",
        "TE032",
        "pattern `2`",
    );
    f.rejects(
        "fn main() -> i32 { match 3 { _ => 1, x if x > 0 => 2 } }",
        "TE032",
        "earlier `_` arm",
    );
    // A guarded earlier arm does not make a later arm unreachable.
    f.write(
        "src/app.mb",
        "fn main() -> i32 { match 3 { x if x > 5 => 1, 3 => 2, _ => 3 } }",
    );
    assert!(f.run(&["check"]).status.success());
}

#[test]
fn literal_and_constant_patterns_must_have_the_scrutinee_type() {
    let f = Fixture::new();
    f.rejects(
        "fn main() -> i32 { match 3 { \"a\" => 1, _ => 2 } }",
        "TE030",
        "string literal",
    );
    f.rejects(
        "fn main() -> i32 { match true { 1 => 1, _ => 2 } }",
        "TE030",
        "is an integer, but the value being matched has type 'bool'",
    );
    f.rejects(
        "fn main() -> i32 { match 'a' { \"a\" => 1, _ => 2 } }",
        "TE030",
        "type 'char'",
    );
    f.rejects(
        "fn main() -> i32 { match 1.5 { 1 => 1, _ => 2 } }",
        "TE030",
        "type 'f64'",
    );
    f.rejects(
        "fn main() -> i32 { let x: u8 = 3; match x { 300 => 1, _ => 2 } }",
        "TE030",
        "does not fit u8",
    );
    f.rejects(
        "fn main() -> i32 { let x: u8 = 3; match x { -1 => 1, _ => 2 } }",
        "TE030",
        "does not fit u8",
    );
    f.rejects(
        "const K: u8 = 3;\nfn main() -> i32 { let x: i32 = 3; match x { K => 1, _ => 2 } }",
        "TE030",
        "type 'i32'",
    );
    f.rejects(
        "const K: f64 = 1.5;\nfn main() -> i32 { match 1.5 { K => 1, _ => 2 } }",
        "TE017",
        "cannot be used as patterns",
    );
    f.rejects(
        "fn main() -> i32 { match 1.5 { 1.5 => 1, _ => 2 } }",
        "SE002",
        "floating-point literals cannot be used as patterns",
    );
    f.rejects(
        "fn main() -> i32 { match \"a\" { \"{x}\" => 1, _ => 2 } }",
        "SE002",
        "placeholders",
    );
}

#[test]
fn or_pattern_alternatives_must_agree_on_names_and_types() {
    let f = Fixture::new();
    f.rejects(
        "type E [ A(i32), B(i32) ]\nfn main() -> i32 { let e := E::A(1); match e { E::A(x) | E::B(_) => 1 } }",
        "TE030",
        "must bind the same names",
    );
    f.rejects(
        "type E [ A(i32), B(string), C ]\nfn main() -> i32 { let e := E::A(1); match e { E::A(x) | E::B(x) => 1, E::C => 2 } }",
        "TE030",
        "same type",
    );
    f.rejects(
        "fn main() -> i32 { match (1, 2) { (a, 1) | (1, a) | (b, 3) => 1, _ => 2 } }",
        "TE030",
        "must bind the same names",
    );
    f.rejects(
        "fn main() -> i32 { match (1, 2) { (a, a) | (a, 3) => 1, _ => 2 } }",
        "TE030",
        "more than once",
    );
}

#[test]
fn guards_must_be_bool_and_see_only_their_arms_bindings() {
    let f = Fixture::new();
    f.rejects(
        "fn main() -> i32 { match 3 { x if x + 1 => 1, _ => 2 } }",
        "TE002",
        "expected bool",
    );
    f.rejects(
        "fn main() -> i32 { match 3 { 1 if q > 0 => 1, _ => 2 } }",
        "NE001",
        "unknown name 'q'",
    );
    f.rejects(
        "fn main() -> i32 { match Some(3) { Some(a) => a, None if a > 0 => 1, None => 2 } }",
        "NE001",
        "unknown name 'a'",
    );
}

#[test]
fn unsupported_shapes_are_reported_not_miscompiled() {
    let f = Fixture::new();
    // A guard only borrows its bindings; an aggregate that owns Strings
    // cannot be borrowed into a local yet.
    f.rejects(
        "type Msg [ Pair((string, u32)), Nil ]\nfn f(m: Msg) -> u32 { match m { Msg::Pair((s, n)) if n > 2 => n, Msg::Pair((s, _)) => s.len(), Msg::Nil => 3 } }\nfn main() -> i32 { 0 }",
        "TE017",
        "a guard in an owned `match` cannot see",
    );
    f.rejects(
        "type Msg [ Pair((string, u32)), Nil ]\nfn f(m: Msg) -> u32 { match m { Msg::Pair((\"a\", n)) => n, Msg::Pair((s, _)) => s.len(), Msg::Nil => 3 } }\nfn main() -> i32 { 0 }",
        "TE017",
        "a literal inside a tuple that owns Strings",
    );
    // A whole enum or tuple is not taken by a lone binding.
    f.rejects(
        "fn main() -> i32 { match Some(1) { other => 1 } }",
        "TE030",
        "cannot take a whole enum or tuple",
    );
}

#[test]
fn repeat_counts_name_constants_of_any_spelling() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "const size: u32 = 4;\nconst Wide: u32 = 2;\nfn main() -> i32 { let a := [3; size]; let b := [1; Wide]; a[3] + b[1] }"
        ),
        "Result: i32(4)"
    );
    f.rejects(
        "fn main() -> i32 { let a := [1; n]; a[0] }",
        "NE001",
        "unknown constant 'n'",
    );
    f.rejects(
        "const n: i32 = 3;\nfn main() -> i32 { let a := [1; n]; a[0] }",
        "TE017",
        "must be a u32 constant",
    );
}

// ---- owned matches with guards under a capped Wasm memory ----

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

const ITERATIONS: u32 = 4_096;
const TEXT_BYTES: u32 = 4_096;

#[test]
fn owned_guards_release_every_payload_exactly_once_under_the_cap() {
    let text = "x".repeat(TEXT_BYTES as usize);
    let source = STRESS_TEMPLATE
        .replace("ITERATIONS", &ITERATIONS.to_string())
        .replace("TEXT", &text);
    // Per iteration (even i returns early from every call): see the program.
    let mut expected: u32 = 0;
    for i in 0..ITERATIONS {
        let early = i % 2 == 0;
        let kind = (i / 2) % 4;
        expected += match (early, kind) {
            (true, 0) => 2,
            (true, 1) => 4,
            (true, 2) => 9,
            (true, _) => 16,
            // Text(a) passes the length guard, Text("ab") hits the literal.
            (false, 0) => TEXT_BYTES + 7,
            // The length guard fails for both pairs, so the second arm runs.
            (false, 1) => TEXT_BYTES + 2,
            (false, 2) => TEXT_BYTES + 1 + 5,
            // Guarded `Ok(Some(s))` fails, falls to `Ok(Some(s))`; `Err` guard.
            (false, _) => 1 + 2 + 7 + 8,
        };
    }
    let (_f, output) = run_capped(&source);
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "capped run failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).trim(),
        format!("Result: i32({expected})")
    );
}

#[test]
fn mutation_check_keeping_the_bound_payload_exhausts_the_capped_memory() {
    // The same owned guarded match, once releasing the payload when the arm
    // ends and once moving it into a List that lives on. The cap must accept
    // the first and trap on the second, so a leak cannot go unnoticed.
    let text = "x".repeat(TEXT_BYTES as usize);
    let program = |arm: &str| {
        format!(
            r#"use alloc::List;
type Msg [ Text(string), Nil ]
fn main() -> u32 {{
    var keep: List<string> = [];
    var i: u32 = 0;
    var total: u32 = 0;
    loop {{
        if i == {ITERATIONS} {{ break; }}
        let a := "{text}".concat("");
        let m := Msg::Text(a);
        total += match m {{
            Msg::Text("ab") => 7,
            Msg::Text(s) if s.len() > 4000 => {arm},
            Msg::Text(_) => 9,
            Msg::Nil => 11,
        }};
        i += 1;
    }}
    total + keep.len()
}}
"#
        )
    };
    let expected = ITERATIONS * TEXT_BYTES;
    let (_f, released) = run_capped(&program("{ let n := s.len(); n }"));
    assert!(
        released.status.success() && released.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&released.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&released.stdout).trim(),
        format!("Result: i32({expected})")
    );
    let (_f, kept) = run_capped(&program("{ let n := s.len(); keep.push(s); n }"));
    assert!(!kept.status.success(), "{kept:?}");
    assert!(
        String::from_utf8_lossy(&kept.stderr).contains("guest heap allocation failed"),
        "{}",
        String::from_utf8_lossy(&kept.stderr)
    );
}

#[test]
fn or_patterns_with_owned_payloads_and_guards_release_exactly_once_under_the_cap() {
    let text = "x".repeat(TEXT_BYTES as usize);
    let source = format!(
        r#"type Msg [ A(string), B(string), C ]
fn size(m: Msg, early: bool) -> u32 {{
    if early {{ return 1; }}
    match m {{
        Msg::A(s) | Msg::B(s) if s.len() > 4000 => s.len(),
        Msg::A(_) | Msg::B(_) => 2,
        Msg::C => 3,
    }}
}}
fn main() -> u32 {{
    var i: u32 = 0;
    var total: u32 = 0;
    loop {{
        if i == {ITERATIONS} {{ break; }}
        let early := i % 2 == 0;
        let kind := (i / 2) % 3;
        let a := "{text}".concat("");
        let b := "ab".concat("");
        if kind == 0 {{
            total += size(Msg::A(a), early);
        }} else if kind == 1 {{
            total += size(Msg::B(b), early);
        }} else {{
            total += size(Msg::C, early);
        }}
        i += 1;
    }}
    total
}}
"#
    );
    let mut expected: u32 = 0;
    for i in 0..ITERATIONS {
        expected += match (i % 2 == 0, (i / 2) % 3) {
            (true, _) => 1,
            (false, 0) => TEXT_BYTES,
            (false, 1) => 2,
            (false, _) => 3,
        };
    }
    let (_f, output) = run_capped(&source);
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "capped run failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).trim(),
        format!("Result: i32({expected})")
    );
}

#[test]
fn a_heap_string_temporary_scrutinee_is_released_under_the_cap() {
    let text = "x".repeat(TEXT_BYTES as usize);
    let source = format!(
        r#"fn big(n: u32) -> string {{
    let t := "{text}".concat("");
    if n == 0 {{ "zero" }} else {{ t }}
}}
fn main() -> u32 {{
    var i: u32 = 0;
    var total: u32 = 0;
    loop {{
        if i == {ITERATIONS} {{ break; }}
        let k: u32 = match big(i % 3) {{
            "zero" => 1,
            s if s.len() > 4000 => 2,
            _ => 3,
        }};
        total += k;
        i += 1;
    }}
    total
}}
"#
    );
    let expected: u32 = (0..ITERATIONS)
        .map(|i| if i % 3 == 0 { 1 } else { 2 })
        .sum();
    let (_f, output) = run_capped(&source);
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "capped run failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).trim(),
        format!("Result: i32({expected})")
    );
}

#[test]
fn guards_work_with_control_flow_value_sinks_and_borrowed_enums() {
    // `return`/`continue`/`break` in arms and guards, owned string arm
    // values, a `var` scrutinee read again afterwards, and in-place guards
    // over a borrowed enum with String payloads.
    assert_eq!(
        Fixture::new().result(r#"
type Shape [ Circle(i32), Named(string), Empty ]
fn peek(s: borrow Shape) -> i32 {
    match s {
        Shape::Named("a") => 1,
        Shape::Named(n) if n.len() > 3 => 2,
        Shape::Named(_) => 3,
        Shape::Circle(r) if r > 3 => r,
        _ => 0,
    }
}
fn early(n: i32) -> i32 {
    let r := match n {
        x if x < 0 => return 99,
        0 => 1,
        x => x,
    };
    r + 1
}
fn text(n: i32) -> string {
    let base := "ab".concat("c");
    match n {
        0 => base,
        k if k > 5 => "big",
        _ => "small",
    }
}
fn looped() -> i32 {
    var i: i32 = 0;
    var sum: i32 = 0;
    loop {
        if i == 6 { break; }
        i += 1;
        match i {
            2 | 4 => continue,
            x if x == 5 => break,
            _ => {}
        }
        sum += i;
    }
    sum
}
fn main() -> i32 {
    let a := Shape::Named("abcd");
    let b := Shape::Circle(9);
    let t0 := text(0);
    let t9 := text(9);
    peek(a.borrow()) + peek(b.borrow()) * 10 + early(-4) + early(0) * 1000 + t0.len() as i32 + t9.len() as i32 + looped() * 100000
}
"#),
        "Result: i32(402197)"
    );
}
