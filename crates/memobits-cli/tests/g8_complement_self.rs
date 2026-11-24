//! G8: `~` bitwise complement and `Self` inside `extend` blocks.
//!
//! `~` is compared with Rust's `!x` on every integer width over boundary
//! values: a dynamic table (hash folded exactly like the Rust side), `const`
//! items and static folds of constant expressions. `Self` is exercised in each
//! supported position (inherent, trailing and interface extensions; generic,
//! const-generic and enum receivers; cross-module public extensions) from
//! source (`mb test`, `mb run`) and as a standalone Wasm artifact, plus the
//! negative cases.
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
        Self::with(&[("main", source)])
    }

    fn with(modules: &[(&str, &str)]) -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-g8-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            "[package]\nname='g8'\nentry='main::main'\n",
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

/// Compile `source` and return stderr; the build must fail with `code`.
fn rejects(source: &str, code: &str) -> String {
    let f = Fixture::new(source);
    let output = f.run(&["check"]);
    let stderr = text(&output.stderr);
    assert!(!output.status.success(), "accepted:\n{source}");
    assert!(
        stderr.contains(code),
        "expected {code} for:\n{source}\n{stderr}"
    );
    stderr
}

/// `check`, `test` (expected count), source `run` and standalone Wasm `run`,
/// each with empty stderr and `Result: Ok(i32(42))`.
fn verify(f: &Fixture, tests: usize, label: &str) {
    let checked = f.run(&["check"]);
    assert!(
        checked.status.success(),
        "{label}: {}",
        text(&checked.stderr)
    );
    let report = f.run(&["test"]);
    let stdout = text(&report.stdout);
    assert!(
        report.status.success()
            && stdout.contains(&format!("test result: ok. {tests} passed; 0 failed")),
        "{label}: {stdout}{}",
        text(&report.stderr)
    );
    let source_run = f.run(&["run"]);
    assert!(
        source_run.status.success() && source_run.stderr.is_empty(),
        "{label} source run: {}",
        text(&source_run.stderr)
    );
    assert_eq!(text(&source_run.stdout), "Result: Ok(i32(42))\n", "{label}");
    let build = f.run(&["build", "--output", "g8.wasm"]);
    assert!(build.status.success(), "{label}: {}", text(&build.stderr));
    let wasm = f.run(&["run", "g8.wasm"]);
    assert!(
        wasm.status.success() && wasm.stderr.is_empty(),
        "{label} wasm run: {}",
        text(&wasm.stderr)
    );
    assert_eq!(text(&wasm.stdout), "Result: Ok(i32(42))\n", "{label}");
}

// ---------------------------------------------------------------------------
// `~` against Rust's `!x`

trait Int: Copy {
    const NAME: &'static str;
    const BITS: u32;
    const SIGNED: bool;
    fn from_i128(value: i128) -> Self;
    fn to_i128(self) -> i128;
    fn complement(self) -> Self;
    fn and(self, other: Self) -> Self;
    fn or(self, other: Self) -> Self;
    fn xor(self, other: Self) -> Self;
}

macro_rules! int_impl {
    ($t:ty, $name:expr, $signed:expr) => {
        impl Int for $t {
            const NAME: &'static str = $name;
            const BITS: u32 = <$t>::BITS;
            const SIGNED: bool = $signed;
            fn from_i128(value: i128) -> Self {
                value as $t
            }
            fn to_i128(self) -> i128 {
                self as i128
            }
            fn complement(self) -> Self {
                !self
            }
            fn and(self, other: Self) -> Self {
                self & other
            }
            fn or(self, other: Self) -> Self {
                self | other
            }
            fn xor(self, other: Self) -> Self {
                self ^ other
            }
        }
    };
}
int_impl!(i8, "i8", true);
int_impl!(i16, "i16", true);
int_impl!(i32, "i32", true);
int_impl!(i64, "i64", true);
int_impl!(u8, "u8", false);
int_impl!(u16, "u16", false);
int_impl!(u32, "u32", false);
int_impl!(u64, "u64", false);

fn min_of<T: Int>() -> i128 {
    if T::SIGNED {
        -(1i128 << (T::BITS - 1))
    } else {
        0
    }
}

fn max_of<T: Int>() -> i128 {
    if T::SIGNED {
        (1i128 << (T::BITS - 1)) - 1
    } else {
        (1i128 << T::BITS) - 1
    }
}

fn values<T: Int>() -> Vec<T> {
    let (min, max) = (min_of::<T>(), max_of::<T>());
    let mut all = vec![
        0,
        1,
        2,
        3,
        17,
        min,
        min + 1,
        max,
        max - 1,
        max / 2,
        max / 2 + 1,
    ];
    if T::SIGNED {
        all.extend([-1, -2, -3]);
    }
    for power in [T::BITS / 2, T::BITS - 2, T::BITS - 1] {
        all.push(1i128 << power);
    }
    all.retain(|v| (min..=max).contains(v));
    all.sort_unstable();
    all.dedup();
    all.into_iter().map(T::from_i128).collect()
}

fn literal(value: i128) -> String {
    if value < 0 {
        format!("({value})")
    } else {
        value.to_string()
    }
}

fn mix(hash: u64, value: u64) -> u64 {
    (hash ^ value).wrapping_mul(1_099_511_628_211)
}

const SEED: u64 = 14_695_981_039_346_656_037;

fn as_u64<T: Int>(value: T) -> u64 {
    value.to_i128() as u64
}

/// A dynamic table: the complement of every value, folded into a hash with the
/// Rust side's mixing step; also double complement, `~x & x`, `~x | x`,
/// `~x ^ x`, a complement as the left operand of an operator and the cast
/// precedence (`~x as u64` complements first).
fn dynamic_program<T: Int>() -> (String, u64) {
    let ty = T::NAME;
    let vals = values::<T>();
    let list = vals
        .iter()
        .map(|v| literal(v.to_i128()))
        .collect::<Vec<_>>()
        .join(", ");
    let n = vals.len();
    let mut expected = SEED;
    for &x in &vals {
        let c = x.complement();
        for item in [
            as_u64(c),
            as_u64(c.complement()),
            as_u64(c.complement()),
            as_u64(c.and(x)),
            as_u64(c.or(x)),
            as_u64(c.xor(x)),
            as_u64(c),
        ] {
            expected = mix(expected, item);
        }
    }
    let source = format!(
        "fn mix(h: u64, x: u64) -> u64 {{ (h ^ x).wrapping_mul(1099511628211) }}\n\
         fn table() -> u64 {{\n    let a: array<{ty}, {n}> = [{list}];\n    let n: u32 = {n};\n    var h: u64 = {SEED};\n    loop i in 0..n {{\n        let x := a[i];\n        h = mix(h, ~x as u64);\n        h = mix(h, (~~x) as u64);\n        h = mix(h, (~(~x)) as u64);\n        h = mix(h, (~x & x) as u64);\n        h = mix(h, (~x | x) as u64);\n        h = mix(h, (~x ^ x) as u64);\n        var y := x;\n        y = ~y;\n        h = mix(h, y as u64);\n    }}\n    h\n}}\n\
         test fn complement_table() {{ assert(table() == {expected}); }}\n\
         fn main() -> i32 ! Error {{\n    if table() != {expected} {{ return Err(Error {{ code: 1 }}); }}\n    Ok(42)\n}}\n"
    );
    (source, expected)
}

fn check_dynamic<T: Int>() {
    let (source, _) = dynamic_program::<T>();
    verify(&Fixture::new(&source), 1, T::NAME);
}

#[test]
fn complement_matches_rust_for_signed_widths() {
    check_dynamic::<i8>();
    check_dynamic::<i16>();
    check_dynamic::<i32>();
    check_dynamic::<i64>();
}

#[test]
fn complement_matches_rust_for_unsigned_widths() {
    check_dynamic::<u8>();
    check_dynamic::<u16>();
    check_dynamic::<u32>();
    check_dynamic::<u64>();
}

/// Exact narrow-width results at the boundaries, written out by hand.
#[test]
fn complement_boundary_values_are_exact() {
    let source = "\
test fn narrow_signed() {
    let a: i8 = -128;
    let b: i8 = 127;
    let c: i8 = 0;
    let d: i8 = -1;
    assert(~a == 127);
    assert(~b == -128);
    assert(~c == -1);
    assert(~d == 0);
    let e: i16 = -32768;
    assert(~e == 32767);
}
test fn narrow_unsigned() {
    let a: u8 = 0;
    let b: u8 = 255;
    let c: u8 = 1;
    assert(~a == 255);
    assert(~b == 0);
    assert(~c == 254);
    let d: u16 = 0;
    assert(~d == 65535);
}
test fn wide() {
    let a: u32 = 0;
    let b: u64 = 0;
    let c: i64 = -9223372036854775807 - 1;
    assert(~a == 4294967295);
    assert(~b == 18446744073709551615);
    assert(~c == 9223372036854775807);
}
test fn operands() {
    let a: u8 = 5;
    let x: i32 = 7;
    assert(~a + 1 == 251);
    assert(~x == -8);
    assert(-~x == 8);
    assert(!(~x == 0));
    assert(~x & 255 == 248);
    assert(~~a == a);
    assert(~a as u32 == 250);
    assert((~a) as u32 == 250);
}
fn main() -> i32 { 42 }
";
    let f = Fixture::new(source);
    let report = f.run(&["test"]);
    let stdout = text(&report.stdout);
    assert!(
        report.status.success() && stdout.contains("test result: ok. 4 passed; 0 failed"),
        "{stdout}{}",
        text(&report.stderr)
    );
}

// ---------------------------------------------------------------------------
// Constant parity

fn const_values<T: Int>() -> Vec<T> {
    let (min, max) = (min_of::<T>(), max_of::<T>());
    let mut all = vec![0, 1, 3, min, min + 1, max, max - 1, max / 2 + 1];
    if T::SIGNED {
        all.extend([-1, -3]);
    }
    all.retain(|v| (min..=max).contains(v));
    all.sort_unstable();
    all.dedup();
    all.into_iter().map(T::from_i128).collect()
}

/// `const` items use the resolver's evaluator, which must agree with Rust and
/// with the runtime result of the same operation.
fn check_const_items<T: Int>() {
    let ty = T::NAME;
    let mut source = String::new();
    let mut asserts = String::new();
    for (index, x) in const_values::<T>().into_iter().enumerate() {
        let a = literal(x.to_i128());
        source.push_str(&format!(
            "const C{index}: {ty} = ~{a};\nconst D{index}: {ty} = ~~{a};\nconst E{index}: {ty} = ~{a} ^ {a};\n"
        ));
        asserts.push_str(&format!(
            "    assert(C{index} == {});\n    assert(D{index} == {a});\n    assert(E{index} == {});\n    let v{index}: {ty} = {a};\n    assert(C{index} == ~v{index});\n",
            literal(x.complement().to_i128()),
            literal(x.complement().xor(x).to_i128()),
        ));
    }
    source.push_str(&format!("test fn consts() {{\n{asserts}}}\n"));
    source.push_str("fn main() -> i32 { 42 }\n");
    let f = Fixture::new(&source);
    let report = f.run(&["test"]);
    let stdout = text(&report.stdout);
    assert!(
        report.status.success() && stdout.contains(" 0 failed"),
        "{ty}: {stdout}{}",
        text(&report.stderr)
    );
}

#[test]
fn const_items_match_rust_for_every_width() {
    check_const_items::<i8>();
    check_const_items::<i16>();
    check_const_items::<i32>();
    check_const_items::<i64>();
    check_const_items::<u8>();
    check_const_items::<u16>();
    check_const_items::<u32>();
    check_const_items::<u64>();
}

/// Static folding: `1 / ((~x) - R)` is a division by zero (LE002) exactly when
/// the fold of `~x` equals the Rust result `R`; the off-by-one twin stays
/// silent.
fn check_fold<T: Int>() {
    let ty = T::NAME;
    let (mut equal, mut different) = (String::new(), String::new());
    let mut count = 0;
    for x in const_values::<T>() {
        let a = literal(x.to_i128());
        for expression in [format!("~{a}"), format!("~~{a}")] {
            let result = if expression.starts_with("~~") {
                x
            } else {
                x.complement()
            };
            let r = result.to_i128();
            equal.push_str(&format!(
                "    let e{count}: {ty} = 1 / (({expression}) - {});\n",
                literal(r)
            ));
            let shifted = if r < max_of::<T>() { r + 1 } else { r - 1 };
            different.push_str(&if shifted > r {
                format!(
                    "    let d{count}: {ty} = 1 / ({} - ({expression}));\n",
                    literal(shifted)
                )
            } else {
                format!(
                    "    let d{count}: {ty} = 1 / (({expression}) - {});\n",
                    literal(shifted)
                )
            });
            count += 1;
        }
    }
    let wrap = |lines: &str| format!("fn chunk() {{\n{lines}}}\nfn main() -> i32 {{ 42 }}\n");
    let silent = Fixture::new(&wrap(&different));
    let output = silent.run(&["check"]);
    assert!(
        output.status.success(),
        "{ty}: a static fold of `~` disagrees with Rust: {}",
        text(&output.stderr)
            .lines()
            .take(6)
            .collect::<Vec<_>>()
            .join("\n")
    );
    let folded = Fixture::new(&wrap(&equal));
    let output = folded.run(&["check"]);
    let stderr = text(&output.stderr);
    assert!(!output.status.success(), "{ty}: nothing folded");
    let hits = stderr.matches("LE002").count();
    assert_eq!(
        hits,
        count,
        "{ty}: only {hits} of {count} folds matched Rust:\n{}",
        stderr.lines().take(6).collect::<Vec<_>>().join("\n")
    );
}

#[test]
fn static_folds_match_rust_for_every_width() {
    check_fold::<i8>();
    check_fold::<i16>();
    check_fold::<i32>();
    check_fold::<i64>();
    check_fold::<u8>();
    check_fold::<u16>();
    check_fold::<u32>();
    check_fold::<u64>();
}

#[test]
fn untyped_literal_complement_defaults_to_u32_like_bitwise_operators() {
    let source = "\
const ALL: u32 = ~0;
const WIDE: u64 = ~0;
test fn literals() {
    let a := ~0;
    let b: i32 = ~0;
    let c: u8 = ~0;
    let d: i64 = ~5;
    assert(a == 4294967295);
    assert(b == -1);
    assert(c == 255);
    assert(d == -6);
    assert(ALL == 4294967295);
    assert(WIDE == 18446744073709551615);
}
fn main() -> i32 { 42 }
";
    let f = Fixture::new(source);
    let report = f.run(&["test"]);
    assert!(
        report.status.success() && text(&report.stdout).contains(" 0 failed"),
        "{}{}",
        text(&report.stdout),
        text(&report.stderr)
    );
}

#[test]
fn complement_rejects_non_integers_and_keeps_nominal_types_primitive_only() {
    for (source, code, message) in [
        (
            "fn main() -> i32 { let a: bool = true; let c := ~a; 0 }",
            "TE007",
            "`~` requires an integer, found bool",
        ),
        (
            "fn main() -> i32 { let a: f64 = 1.0; let c := ~a; 0 }",
            "TE007",
            "`~` requires an integer, found f64",
        ),
        (
            "fn main() -> i32 { let a: f32 = 1.0; let c := ~a; 0 }",
            "TE007",
            "`~` requires an integer, found f32",
        ),
        (
            "fn main() -> i32 { let a: char = 'x'; let c := ~a; 0 }",
            "TE007",
            "`~` requires an integer",
        ),
        (
            "fn main() -> i32 { let c := ~1.5; 0 }",
            "TE007",
            "`~` requires an integer",
        ),
        (
            "type Cell { v: i32 } fn main() -> i32 { let a := Cell { v: 1 }; let c := ~a; 0 }",
            "TE007",
            "`~` requires an integer, found Cell",
        ),
        (
            "fn main() -> i32 { let a: u8 = 1; let c: u16 = ~a; 0 }",
            "TE002",
            "expected u16, found u8",
        ),
        (
            "const BAD: bool = ~true;\nfn main() -> i32 { 0 }",
            "TE007",
            "`~` requires an integer",
        ),
        (
            "const BAD: f64 = ~1.5;\nfn main() -> i32 { 0 }",
            "TE007",
            "`~` requires an integer",
        ),
    ] {
        let stderr = rejects(&format!("{source}\n"), code);
        assert!(
            stderr.contains(message),
            "{source}\nexpected `{message}`:\n{stderr}"
        );
    }
    // No `core::ops::Not`-style interface exists, so an `extend ... of Not`
    // cannot make `~` apply to a nominal type.
    rejects(
        "use core::ops::Not; type Cell { v: i32 } fn main() -> i32 { 0 }",
        "ME",
    );
}

// ---------------------------------------------------------------------------
// `Self`

const SELF_SOURCE: &str = "\
use shapes;
use shapes::Cell;
use shapes::Tag;
use core::ops::Add;
use core::ops::Neg;

// Inherent extension: result, `let` annotation, struct literal.
type Point { x: i32, y: i32 }
extend Point {
    fn moved(self, dx: i32) -> Self {
        let next: Self = Self { x: self.x + dx, y: self.y };
        next
    }
}

// Trailing extend on a generic nominal type: `Self` is `Pair<T>`.
type Pair<T> { a: T, b: T } extend {
    fn swap(self) -> Self { Self { a: self.b, b: self.a } }
    fn first(borrow self) -> T { self.a }
}

// Const-generic receiver: `Self` is `Lane<N>`.
type Lane<const N: u32> { width: i32 } extend {
    fn widen(self) -> Self {
        let wide: Self = Self { width: self.width * 2 };
        wide
    }
    fn size(borrow self) -> i32 { self.width }
}

// An extension of one instantiation: `Self` is `Pair<i32>`.
extend Pair<i32> {
    fn total(self) -> Self { Self { a: self.a + self.b, b: 0 } }
}

// Enums: `Self::Variant` in expressions and patterns.
type Color [Red, Green, Blue] extend {
    fn next(self) -> Self {
        match self {
            Self::Red => Self::Green,
            Self::Green => Self::Blue,
            Self::Blue => Self::Red,
        }
    }
    fn code(borrow self) -> i32 { match self { Self::Red => 1, Self::Green => 2, Self::Blue => 3 } }
}

// A generic enum with a payload variant.
type Slot<T> [Empty, Full(T)] extend {
    fn keep(self) -> Self {
        match self { Self::Empty => Self::Empty, Self::Full(v) => Self::Full(v) }
    }
    fn fill_or(self, fallback: T) -> Self {
        match self { Self::Empty => Self::Full(fallback), Self::Full(v) => Self::Full(v) }
    }
}

// `extend T of Interface`: `Self` in the associated type, operands and result.
type Money { cents: i32 }
extend Money of Add {
    type Rhs = Self;
    type Output = Self;
    fn add(self, rhs: Self) -> Self { Self { cents: self.cents + rhs.cents } }
}
extend Money of Neg {
    type Output = Self;
    fn neg(self) -> Self { Self { cents: 0 - self.cents } }
}
pub interface Describe { fn describe(borrow self) -> i32; }
extend Money of Describe {
    fn describe(borrow self) -> i32 {
        let copy: Self = Self { cents: self.cents };
        copy.cents
    }
}

test fn inherent_extension() {
    let p := Point { x: 1, y: 5 };
    let q := p.moved(2);
    assert(q.x == 3);
    assert(q.y == 5);
}
test fn generic_trailing_extension() {
    let p := Pair<i32> { a: 1, b: 2 };
    let q := p.swap();
    assert(q.first() == 2);
    let w := Pair<bool> { a: true, b: false };
    let v := w.swap();
    assert(!v.first());
}
test fn const_generic_receiver() {
    let lane := Lane<4> { width: 3 };
    let wide := lane.widen();
    let wider := wide.widen();
    assert(wider.size() == 12);
}
test fn instantiated_extension() {
    let p := Pair<i32> { a: 20, b: 22 };
    let t := p.total();
    assert(t.a == 42);
}
test fn enum_variants() {
    let c := Color::Red;
    let d := c.next();
    assert(d.code() == 2);
    let e := d.next();
    assert(e.code() == 3);
    let f := e.next();
    assert(f.code() == 1);
}
test fn generic_enum_variants() {
    let empty: Slot<i32> = Slot::Empty;
    let filled := empty.fill_or(9);
    let kept := filled.keep();
    assert(match kept { Slot::Full(v) => v == 9, Slot::Empty => false });
}
test fn interface_extensions() {
    let a := Money { cents: 40 };
    let b := Money { cents: 2 };
    let sum := a + b;
    let described := (sum.describe() of Describe).copy();
    assert(described == 42);
    let neg := -sum;
    assert(neg.cents == -42);
}
test fn cross_module_public_extensions() {
    let cell := Cell { value: 41 };
    let bumped := cell.bump();
    assert(bumped.value == 42);
    let tag := Tag::A;
    let other := tag.other();
    assert(match other { Tag::B => true, Tag::A => false });
}

fn main() -> i32 ! Error {
    let p := Point { x: 40, y: 0 };
    let q := p.moved(2);
    let cell := Cell { value: q.x - 1 };
    let bumped := cell.bump();
    Ok(bumped.value)
}
";

const SHAPES: &str = "\
pub type Cell { pub value: i32 }
pub type Tag [A, B]
pub extend Cell {
    pub fn bump(self) -> Self { Self { value: self.value + 1 } }
}
pub extend Tag {
    pub fn other(self) -> Self {
        match self { Self::A => Self::B, Self::B => Self::A }
    }
}
";

#[test]
fn self_names_the_extended_type_in_every_position() {
    let f = Fixture::with(&[("main", SELF_SOURCE), ("shapes", SHAPES)]);
    verify(&f, 8, "self");
}

#[test]
fn self_in_generic_and_enum_receivers_matches_the_written_type() {
    // The same programs written with the explicit type names behave
    // identically: `Self` is only a name for them.
    let explicit = SELF_SOURCE
        .replace(
            "fn moved(self, dx: i32) -> Self",
            "fn moved(self, dx: i32) -> Point",
        )
        .replace("let next: Self = Self {", "let next: Point = Point {")
        .replace(
            "fn swap(self) -> Self { Self {",
            "fn swap(self) -> Pair<T> { Pair<T> {",
        )
        .replace("fn widen(self) -> Self {", "fn widen(self) -> Lane<N> {")
        .replace("let wide: Self = Self {", "let wide: Lane<N> = Lane<N> {");
    let f = Fixture::with(&[("main", &explicit), ("shapes", SHAPES)]);
    verify(&f, 8, "explicit");
}

#[test]
fn self_outside_extend_blocks_is_an_error() {
    for (source, message) in [
        (
            "fn f(x: Self) {} fn main() -> i32 { 0 }",
            "only available inside an `extend` block",
        ),
        (
            "fn f() -> Self { 0 } fn main() -> i32 { 0 }",
            "only available inside an `extend` block",
        ),
        (
            "fn main() -> i32 { let x: Self = 1; 0 }",
            "only available inside an `extend` block",
        ),
        (
            "type Cell { v: i32 } fn main() -> i32 { let c := Self { v: 1 }; 0 }",
            "only available inside an `extend` block",
        ),
        (
            "type Tag [A, B] fn main() -> i32 { let t := Self::A; 0 }",
            "only available inside an `extend` block",
        ),
        (
            "type Cell { next: Self } fn main() -> i32 { 0 }",
            "only available inside an `extend` block",
        ),
        (
            "const C: Self = 1; fn main() -> i32 { 0 }",
            "only available inside an `extend` block",
        ),
    ] {
        let stderr = rejects(source, "SE002");
        assert!(
            stderr.contains(message),
            "{source}\nexpected `{message}`:\n{stderr}"
        );
    }
}

#[test]
fn self_in_interface_declarations_is_not_supported_yet() {
    let source = "\
type Cell { v: i32 }
interface Dup { fn dup(borrow self) -> Self; }
extend Cell of Dup { fn dup(borrow self) -> Cell { Cell { v: self.v } } }
fn main() -> i32 { 0 }
";
    let stderr = rejects(source, "SE002");
    assert!(
        stderr.contains("`Self` in interface declarations is not supported yet"),
        "{stderr}"
    );
    let parameter =
        "interface Eq2 { fn same(borrow self, other: Self) -> bool; }\nfn main() -> i32 { 0 }\n";
    let stderr = rejects(parameter, "SE002");
    assert!(stderr.contains("not supported yet"), "{stderr}");
}

#[test]
fn self_misuse_inside_extend_blocks_is_rejected() {
    for (body, message) in [
        (
            "fn k(self) -> Self { let a := Self; self }",
            "`Self` names a type, not a value",
        ),
        (
            "fn k(self) -> Self<i32> { self }",
            "`Self` takes no type arguments",
        ),
        (
            "fn k(self) -> Self::Inner { self }",
            "`Self::...` is not a type",
        ),
    ] {
        let source =
            format!("type Cell {{ v: i32 }}\nextend Cell {{ {body} }}\nfn main() -> i32 {{ 0 }}\n");
        let stderr = rejects(&source, "SE002");
        assert!(
            stderr.contains(message),
            "{source}\nexpected `{message}`:\n{stderr}"
        );
    }
    // A variant that does not exist is still reported by name resolution.
    let source =
        "type Tag [A, B] extend { fn k(self) -> Self { Self::Missing } }\nfn main() -> i32 { 0 }\n";
    let f = Fixture::new(source);
    let output = f.run(&["check"]);
    assert!(!output.status.success(), "accepted:\n{source}");
}
