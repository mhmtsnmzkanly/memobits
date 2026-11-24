//! G5: module-level constants `const NAME: T = expr;`.
//!
//! Runtime checks run from source and from the standalone Wasm artifact.
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
            "memobits-g5-const-{}-{}",
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

fn project(f: &Fixture, build: &str, source: &str) {
    let build = if build.is_empty() {
        String::new()
    } else {
        format!("[build]\n{build}\n")
    };
    f.write(
        "project.toml",
        &format!("[package]\nname='g5'\nentry='main::main'\n{build}"),
    );
    f.write("src/main.mb", source);
}

const OK: &str = "Result: i32(42)\n";

/// Run from source and from the standalone artifact; both must print
/// `Result: i32(42)` and nothing on stderr.
fn run_source_and_wasm(f: &Fixture) {
    let source = f.run(&["run"]);
    assert!(
        source.status.success() && source.stderr.is_empty(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&source.stdout), OK);
    let build = f.run(&["build", "--output", "g5.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&["run", "g5.wasm"]);
    assert!(
        wasm.status.success() && wasm.stderr.is_empty(),
        "Wasm failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&wasm.stdout), OK);
}

/// `mb check` must fail with `code` and mention `text`; returns stderr.
fn rejects(f: &Fixture, source: &str, code: &str, text: &str) -> String {
    f.write("src/main.mb", source);
    let check = f.run(&["check"]);
    assert!(!check.status.success(), "expected {code} for:\n{source}");
    let stderr = String::from_utf8_lossy(&check.stderr).into_owned();
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

fn runs(f: &Fixture, source: &str) {
    project(f, "", source);
    run_source_and_wasm(f);
}

#[test]
fn every_const_type_works_from_source_and_wasm() {
    let f = Fixture::new();
    runs(
        &f,
        r#"
const I8_MIN: i8 = -128;
const I8_MAX: i8 = 127;
const I16_MIN: i16 = -32768;
const I16_MAX: i16 = 32767;
const I32_MIN: i32 = -2147483648;
const I32_MAX: i32 = 2147483647;
const I64_MIN: i64 = -9223372036854775808;
const I64_MAX: i64 = 9223372036854775807;
const U8_MAX: u8 = 255;
const U16_MAX: u16 = 65535;
const U32_MAX: u32 = 4294967295;
const U64_MAX: u64 = 18446744073709551615;
const HALF: f32 = 0.5;
const THIRD: f32 = 1.0 / 3.0;
const PI: f64 = 3.141592653589793;
const BIG_F: f64 = 1.0e300;
const NEG_F: f64 = -2.5;
const YES: bool = true;
const NO: bool = false;
const LETTER: char = 'x';
const SNOWMAN: char = '☃';
const TEXT: string = "hello";
const EMPTY: string = "";
const UNICODE: string = "héllo ☃";

fn main() -> i32 {
    assert(I8_MIN == -128);
    assert(I8_MAX == 127);
    assert(I16_MIN == -32768);
    assert(I16_MAX == 32767);
    assert(I32_MIN == -2147483648);
    assert(I32_MAX == 2147483647);
    assert(I64_MIN == -9223372036854775808);
    assert(I64_MAX == 9223372036854775807);
    assert(U8_MAX == 255);
    assert(U16_MAX == 65535);
    assert(U32_MAX == 4294967295);
    assert(U64_MAX == 18446744073709551615);
    assert(HALF == 0.5);
    let third: f32 = 1.0 / 3.0;
    assert(THIRD == third);
    assert(PI == 3.141592653589793);
    assert(BIG_F == 1.0e300);
    assert(NEG_F == -2.5);
    assert(YES);
    assert(!NO);
    assert(LETTER == 'x');
    assert(SNOWMAN == '☃');
    assert(TEXT.len() == 5);
    assert(EMPTY.len() == 0);
    assert(UNICODE.len() == 10);
    // The value keeps its declared type: a binding without annotation
    // takes the const's type, not the literal default.
    let wide := U64_MAX;
    assert(wide / 2 == 9223372036854775807);
    let small := U8_MAX;
    assert(small == 255);
    let single := HALF;
    assert(single + single == 1.0);
    42
}
"#,
    );
}

#[test]
fn const_expressions_use_checked_arithmetic_casts_and_operators() {
    let f = Fixture::new();
    runs(
        &f,
        r#"
const A: u32 = 6 * 7;
const B: u32 = A - 2;
const C: u32 = (A + B) / 4 % 7;
const D: i32 = -A_I + 3;
const A_I: i32 = 10;
const E: i32 = -(2 + 3) * 4;
const F: u8 = 300 as u8;
const G: i8 = 200 as u8 as i8;
const H: u32 = -1 as u32;
const I: u64 = 2147483647 as u64 * 8;
const J: f32 = 7 as f32 / 2 as f32;
const K: i32 = 2.9 as i32 + (-2.9) as i32;
const L: u8 = 300.5 as u8;
const M: u32 = (1 << 4) | 3;
const N: u32 = 240 >> 4;
const O: u32 = 12 & 10 ^ 3;
const P: bool = A > B || B >= A;
const Q: bool = A == 42 && !(B != 40);
const R: bool = 'a' == 'a' && 'a' != 'b';
const S: bool = true == true;
const T: i64 = 9223372036854775807 - 1;
const U: i32 = -2147483647 - 1;
const V: i32 = U % -1;
const W: f64 = 1.0 / 0.0;
const X: bool = 0.0 / 0.0 == 0.0 / 0.0;
const Y: f32 = 16777216.0 + 1.0;

fn main() -> i32 {
    assert(A == 42);
    assert(B == 40);
    assert(C == 20 % 7);
    assert(D == -7);
    assert(E == -20);
    assert(F == 44);
    assert(G == -56);
    assert(H == 4294967295);
    assert(I == 17179869176);
    assert(J == 3.5);
    assert(K == 0);
    assert(L == 255);
    assert(M == 19);
    assert(N == 15);
    assert(O == 12 & 10 ^ 3);
    assert(P);
    assert(Q);
    assert(R);
    assert(S);
    assert(T == 9223372036854775806);
    assert(U == -2147483648);
    assert(V == 0);
    assert(W > 1.0e308);
    assert(!X);
    assert(Y == 16777216.0);
    42
}
"#,
    );
}

#[test]
fn constants_cross_modules_and_may_appear_in_any_order() {
    let f = Fixture::new();
    f.write(
        "src/geometry.mb",
        "use limits::{SIDES, SCALE as FACTOR};\n\
         pub const PERIMETER: u32 = SIDES * FACTOR * UNIT;\n\
         pub const UNIT: u32 = 5;\n\
         const PRIVATE_ONE: u32 = 1;\n\
         pub const DERIVED: u32 = PRIVATE_ONE + 1;\n",
    );
    f.write(
        "src/limits.mb",
        "pub const SIDES: u32 = 4;\npub const SCALE: u32 = 3;\npub const NAME: string = \"limits\";\n",
    );
    project(
        &f,
        "",
        r#"use geometry::{PERIMETER, DERIVED as TWO};
use geometry;
use limits;

const FIRST: u32 = SECOND + 1;
const SECOND: u32 = PERIMETER - limits::SIDES * 15 + geometry::UNIT * 0 + 1;
pub const LABEL: string = limits::NAME;

fn main() -> i32 {
    assert(PERIMETER == 60);
    assert(TWO == 2);
    assert(geometry::UNIT == 5);
    assert(limits::SIDES == 4);
    assert(SECOND == 1);
    assert(FIRST == 2);
    assert(LABEL.len() == 6);
    42
}
"#,
    );
    run_source_and_wasm(&f);
    // Private constants stay private; unknown members are diagnosed.
    rejects(
        &f,
        "use geometry::PRIVATE_ONE;\nfn main() -> i32 { 0 }\n",
        "ME007",
        "definition 'geometry::PRIVATE_ONE' is private",
    );
    rejects(
        &f,
        "use geometry;\nfn main() -> i32 { let x := geometry::PRIVATE_ONE; 0 }\n",
        "ME007",
        "definition 'geometry::PRIVATE_ONE' is private",
    );
    rejects(
        &f,
        "use geometry::MISSING;\nfn main() -> i32 { 0 }\n",
        "ME006",
        "geometry::MISSING",
    );
    // A const is not a type and not an entry point.
    rejects(
        &f,
        "use limits::SIDES;\nfn f(x: SIDES) {}\nfn main() -> i32 { 0 }\n",
        "ME008",
        "is not a type",
    );
}

#[test]
fn array_lengths_const_arguments_repeat_counts_and_range_bounds_use_constants() {
    let f = Fixture::new();
    runs(
        &f,
        r#"
const SIZE: u32 = 4;
const WIDE: u32 = SIZE * 2;
const LIMIT: u8 = 5;

type Lane<const N: u32> { width: i32 }
type Grid { cells: array<array<u8, SIZE>, 2> }

fn sum(items: array<u32, SIZE>) -> u32 {
    var total: u32 = 0;
    loop i in 0..SIZE {
        total += items[i];
    }
    total
}
fn echo<T, const N: u32>(value: array<T, N>) -> array<T, N> { value }
fn make() -> array<u8, WIDE> { [7; WIDE] }

fn main() -> i32 {
    let summed: array<u32, SIZE> = [1, 2, 3, 4];
    assert(sum(summed) == 10);
    let sent: array<u32, SIZE> = [5, 6, 7, 8];
    let echoed := echo(sent);
    assert(echoed[0] == 5);
    let items: array<u32, SIZE> = [1, 2, 3, 4];
    let zeros: array<u32, SIZE> = [0; SIZE];
    assert(zeros[3] == 0);
    let both := make();
    assert(both[7] == 7);
    let lane: Lane<SIZE> = Lane<SIZE> { width: 9 };
    assert(lane.width == 9);
    let grid := Grid { cells: [[0; SIZE]; 2] };
    assert(grid.cells[1][3] == 0);
    // Inclusive and half-open ranges accept constants on either side.
    var count: u32 = 0;
    loop i in 0..=SIZE { count += 1; }
    assert(count == 5);
    var visited: u8 = 0;
    loop j in LIMIT..LIMIT + 3 { visited += j; }
    assert(visited == 5 + 6 + 7);
    // A constant index is checked statically, like a literal index.
    let last := items[SIZE - 1];
    assert(last == 4);
    42
}
"#,
    );
    rejects(
        &f,
        "const SIZE: u32 = 4;\nfn main() -> i32 { let a: array<u8, SIZE> = [1, 2, 3, 4]; a[SIZE] as i32 }\n",
        "TE008",
        "constant array index 4 is out of bounds for length 4",
    );
    rejects(
        &f,
        "const SIZE: u8 = 4;\nfn f(a: array<u8, SIZE>) {}\nfn main() -> i32 { 0 }\n",
        "TE017",
        "an array length or const argument must be a u32 constant",
    );
    rejects(
        &f,
        "fn main() -> i32 { let a := [0; MISSING]; 0 }\n",
        "NE001",
        "unknown constant 'MISSING'",
    );
    rejects(
        &f,
        "const SIZE: u8 = 4;\nfn main() -> i32 { let a := [0; SIZE]; 0 }\n",
        "TE017",
        "an array repeat count must be a u32 constant",
    );
}

#[test]
fn interpolation_reads_constants_as_identifiers() {
    let f = Fixture::new();
    runs(
        &f,
        r#"
const COUNT: u32 = 12;
const NEGATIVE: i64 = -9;
const ON: bool = true;
const MARK: char = '#';
const NAME: string = "box";

fn at(s: borrow string, i: u32, want: u8) -> bool {
    match s.byte_at(i) { Some(b) => b == want, None => false }
}

fn main() -> i32 {
    let local: u32 = 5;
    let s := "{NAME}:{COUNT}:{NEGATIVE}:{ON}:{MARK}:{local}";
    assert(s.len() == "box:12:-9:true:#:5".len());
    let t := "{NAME}{NAME}";
    assert(t.len() == 6);
    assert(at(t.borrow(), 3, 98));
    let braces := "{{{COUNT}}}";
    assert(braces.len() == 4);
    assert(at(braces.borrow(), 1, 49));
    assert(at(s.borrow(), 4, 49));
    42
}
"#,
    );
    // Floating-point values are not interpolated yet, for constants as well.
    rejects(
        &f,
        "const RATE: f64 = 1.5;\nfn main() -> i32 { let s := \"{RATE}\"; 0 }\n",
        "TE017",
        "floating-point values in string interpolation",
    );
}

#[test]
fn local_names_shadow_constants() {
    let f = Fixture::new();
    runs(
        &f,
        r#"
const LIMIT: u32 = 100;
const NAME: string = "const";

fn param(LIMIT: u32) -> u32 { LIMIT + 1 }
fn shadow() -> u32 {
    let LIMIT: u32 = 7;
    LIMIT
}
fn inner() -> u32 {
    let value := { let LIMIT: u32 = 3; LIMIT };
    value + LIMIT
}
fn looped() -> u32 {
    var total: u32 = 0;
    let end: u32 = 3;
    loop LIMIT in 0..end { total += LIMIT; }
    total + LIMIT
}
fn tuple() -> u32 {
    let pair: (u32, u32) = (1, 2);
    let (LIMIT, other) := pair;
    LIMIT + other
}

fn main() -> i32 {
    assert(param(1) == 2);
    assert(shadow() == 7);
    assert(inner() == 103);
    assert(looped() == 103);
    assert(tuple() == 3);
    let NAME := "local";
    assert(NAME.len() == 5);
    assert(LIMIT == 100);
    42
}
"#,
    );
}

#[test]
fn string_constants_are_static_literals_without_the_alloc_layer() {
    let f = Fixture::new();
    project(
        &f,
        "alloc = false",
        r#"
const GREETING: string = "hello";
const SUFFIX: string = GREETING;
const COUNT: u32 = 5;

fn main() -> i32 {
    // Interpolating only constants folds to a static literal, so it needs no
    // allocator.
    let s := "{GREETING}-{COUNT}";
    if GREETING.len() == 5 && SUFFIX.len() == 5 && s.len() == 7 { 42 } else { 1 }
}
"#,
    );
    run_source_and_wasm(&f);
    let wasm = fs::read(f.0.join("g5.wasm")).unwrap();
    let memory = wasmparser::Parser::new(0)
        .parse_all(&wasm)
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("literal data needs a memory")
        .unwrap();
    assert_eq!(memory.maximum, Some(memory.initial), "no heap growth");
}

#[test]
fn const_errors_use_exact_codes() {
    let f = Fixture::new();
    project(&f, "", "fn main() {}\n");
    // Overflow, division by zero and shift counts keep the LE codes and the
    // wording of statically known expressions.
    for source in [
        "const A: u8 = 255 + 1;",
        "const A: u32 = 4294967295 * 2;",
        "const A: i32 = -2147483647 - 2;",
        "const N: i8 = -128;\nconst A: i8 = -N;",
        "const B: i8 = 127;\nconst A: i8 = B + 1;",
        "const B: u64 = 18446744073709551615;\nconst A: u64 = B + 1;",
        "const A: i32 = -2147483648 / -1;",
        "const A: u32 = 0 - 1;",
    ] {
        rejects(
            &f,
            &format!("{source}\nfn main() {{}}\n"),
            "LE001",
            "integer overflow in statically known expression",
        );
    }
    for source in [
        "const A: u32 = 1 / 0;",
        "const A: u32 = 5 % 0;",
        "const Z: u32 = 0;\nconst A: u32 = 5 / Z;",
        "const A: i32 = 1 / (3 - 3);",
    ] {
        rejects(
            &f,
            &format!("{source}\nfn main() {{}}\n"),
            "LE002",
            "division or remainder by zero",
        );
    }
    for source in [
        "const A: u32 = 1 << 32;",
        "const N: u32 = 40;\nconst A: u32 = 1 >> N;",
    ] {
        rejects(
            &f,
            &format!("{source}\nfn main() {{}}\n"),
            "LE003",
            "u32 shift count must be less than 32",
        );
    }
    // Errors are reported even for a constant nothing uses.
    rejects(
        &f,
        "const UNUSED: u8 = 255 + 1 - 1;\nfn main() {}\n",
        "LE001",
        "integer overflow",
    );
    // Literals must fit the declared type.
    rejects(
        &f,
        "const A: u8 = 256;\nfn main() {}\n",
        "TE008",
        "integer literal does not fit u8",
    );
    rejects(
        &f,
        "const A: u32 = -1;\nfn main() {}\n",
        "TE002",
        "expected u32, found i32",
    );
    // The value type must match the declared type; there is no coercion.
    rejects(
        &f,
        "const A: u32 = true;\nfn main() {}\n",
        "TE002",
        "expected u32, found bool",
    );
    rejects(
        &f,
        "const A: f64 = 1;\nfn main() {}\n",
        "TE002",
        "expected f64, found i32",
    );
    rejects(
        &f,
        "const A: bool = 1;\nfn main() {}\n",
        "TE002",
        "expected bool, found i32",
    );
    rejects(
        &f,
        "const A: string = 'c';\nfn main() {}\n",
        "TE002",
        "expected string, found char",
    );
    rejects(
        &f,
        "const A: u8 = 1;\nconst B: u32 = A;\nfn main() {}\n",
        "TE002",
        "expected u32, found u8",
    );
    rejects(
        &f,
        "const A: u8 = 1;\nconst B: u32 = A + 1000;\nfn main() {}\n",
        "TE008",
        "integer literal does not fit u8",
    );
    // The type annotation is required and must be a simple scalar type.
    rejects(
        &f,
        "const A = 5;\nfn main() {}\n",
        "SE002",
        "needs a type annotation",
    );
    for ty in ["Foo", "array<u8, 2>", "u8?", "String", "i32 ! Error"] {
        rejects(
            &f,
            &format!("const A: {ty} = 5;\nfn main() {{}}\n"),
            "TE017",
            "a const type must be an integer type, f32, f64, bool, char or string",
        );
    }
}

#[test]
fn cycles_name_the_constants_involved() {
    let f = Fixture::new();
    project(&f, "", "fn main() {}\n");
    let stderr = rejects(
        &f,
        "const A: u32 = A;\nfn main() {}\n",
        "LE004",
        "constant cycle: A -> A",
    );
    assert!(stderr.contains("src/main.mb:1:"), "{stderr}");
    rejects(
        &f,
        "const A: u32 = B;\nconst B: u32 = C + 1;\nconst C: u32 = A * 2;\nfn main() {}\n",
        "LE004",
        "constant cycle: A -> B -> C -> A",
    );
    // A cycle through two modules names the modules.
    f.write("src/other.mb", "use main::A;\npub const B: u32 = A + 1;\n");
    let stderr = rejects(
        &f,
        "use other::B;\npub const A: u32 = B;\nfn main() {}\n",
        "LE004",
        "constant cycle:",
    );
    assert!(stderr.contains("other::B"), "{stderr}");
    assert!(stderr.contains("main::A"), "{stderr}");
    // A cycle is reported once and does not hide later independent errors.
    let stderr = rejects(
        &f,
        "const A: u32 = B;\nconst B: u32 = A;\nconst C: u8 = 255 + 1;\nfn main() {}\n",
        "LE004",
        "constant cycle: A -> B -> A",
    );
    assert_eq!(stderr.matches("error[LE004]").count(), 1, "{stderr}");
    assert!(stderr.contains("error[LE001]"), "{stderr}");
    // Dependencies that are not cycles are fine, in any order.
    project(
        &f,
        "",
        "const C: u32 = B + A;\nconst B: u32 = A * 2;\nconst A: u32 = 4;\nfn main() -> i32 { if C == 12 { 42 } else { 1 } }\n",
    );
    run_source_and_wasm(&f);
}

#[test]
fn non_constant_initializers_are_rejected() {
    let f = Fixture::new();
    project(&f, "", "fn main() {}\n");
    for (source, text) in [
        (
            "fn f() -> u32 { 1 }\nconst A: u32 = f();",
            "a call is not allowed in a const initializer",
        ),
        (
            "fn f() -> u32 { 1 }\nconst A: u32 = f;",
            "`f` is not a constant",
        ),
        (
            "type Color [ Red, Green ]\nconst A: u32 = Color::Red;",
            "`Color::Red` is not a constant",
        ),
        (
            "const A: u32 = if true { 1 } else { 2 };",
            "a block, `if` or `match` is not allowed",
        ),
        (
            "const A: u32 = { 1 };",
            "a block, `if` or `match` is not allowed",
        ),
        (
            "const A: string = \"x\".concat(\"y\");",
            "a call is not allowed",
        ),
        (
            "const N: u32 = 3;\nconst A: string = \"n={N}\";",
            "string interpolation is not allowed in a const initializer",
        ),
        (
            "const A: u32 = [1, 2][0];",
            "this expression is not allowed",
        ),
    ] {
        rejects(&f, &format!("{source}\nfn main() {{}}\n"), "LE005", text);
    }
    // A name that does not exist at all is an ordinary unknown name.
    rejects(
        &f,
        "const A: u32 = missing;\nfn main() {}\n",
        "NE001",
        "unknown name 'missing'",
    );
    // Locals do not exist at module level; a function parameter name is
    // unknown in an initializer.
    rejects(
        &f,
        "fn f(x: u32) -> u32 { x }\nconst A: u32 = x;\nfn main() {}\n",
        "NE001",
        "unknown name 'x'",
    );
}

#[test]
fn constants_follow_the_value_namespace_and_are_read_only() {
    let f = Fixture::new();
    project(&f, "", "fn main() {}\n");
    // A const and a function, type or second const share one namespace.
    for source in [
        "const A: u32 = 1;\nfn A() {}",
        "fn A() {}\nconst A: u32 = 1;",
        "const A: u32 = 1;\ntype A { x: u32 }",
        "const A: u32 = 1;\nconst A: u32 = 2;",
    ] {
        rejects(
            &f,
            &format!("{source}\nfn main() {{}}\n"),
            "ME005",
            "duplicate module binding 'A'",
        );
    }
    // An import cannot reuse a local const name either.
    f.write("src/other.mb", "pub const A: u32 = 1;\n");
    rejects(
        &f,
        "use other::A;\nconst A: u32 = 2;\nfn main() {}\n",
        "ME005",
        "duplicate module binding 'A'",
    );
    // Assignment, compound assignment and mutation through a place.
    for body in ["A = 2;", "A += 1;", "A[0] = 1;"] {
        rejects(
            &f,
            &format!("const A: u32 = 1;\nfn main() {{ {body} }}\n"),
            "TE004",
            "cannot assign to constant 'A'",
        );
    }
    // A constant is not callable or a type.
    f.write("src/other.mb", "");
    rejects(
        &f,
        "const A: u32 = 1;\nfn main() { let x := A(); }\n",
        "TE011",
        "expression is not callable",
    );
    // A pattern identifier that names a constant is a constant pattern (G7);
    // its type must be the matched type.
    rejects(
        &f,
        "const ZERO: u32 = 0;\nfn main() -> i32 { match 1 { ZERO => 1, _ => 2 } }\n",
        "TE030",
        "type 'i32'",
    );
}

#[test]
fn constants_inline_their_values_in_tests_and_standalone_analysis() {
    let f = Fixture::new();
    project(
        &f,
        "",
        r#"
const BASE: u32 = 40;
const OFFSET: u32 = 2;

fn total() -> u32 { BASE + OFFSET }
fn main() -> i32 { total() as i32 }

test fn base_is_forty() {
    assert(BASE == 40);
    assert(total() == 42);
}
test fn constants_have_their_type() {
    let narrow: u8 = 255;
    const_check(narrow);
}
fn const_check(value: u8) { assert(value == 255); }
"#,
    );
    let test = f.run(&["test"]);
    assert!(
        test.status.success() && test.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&test.stderr)
    );
    let text = String::from_utf8_lossy(&test.stdout);
    assert!(text.contains("2 passed"), "{text}");
    let check = f.run(&["check"]);
    assert!(
        check.status.success(),
        "{}",
        String::from_utf8_lossy(&check.stderr)
    );
    // The standalone analysis commands fold constants of a single file too.
    f.write(
        "single.mb",
        "const N: u32 = 4;\nfn f(a: array<u8, N>) -> u32 { N }\nfn main() -> i32 { 0 }\n",
    );
    for command in ["analyze", "ownership"] {
        let out = f.run(&[command, "single.mb"]);
        assert!(
            out.status.success(),
            "{command}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    f.write("single.mb", "const N: u8 = 255 + 1;\nfn main() {}\n");
    let out = f.run(&["analyze", "single.mb"]);
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("error[LE001]"));
    // The syntax command only parses.
    let out = f.run(&["syntax", "single.mb"]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn constants_participate_in_static_checks_like_literals() {
    let f = Fixture::new();
    project(&f, "", "fn main() {}\n");
    // A constant operand of a statically known expression overflows at
    // compile time exactly as the literal would.
    rejects(
        &f,
        "const TOP: u8 = 255;\nfn main() -> i32 { let x: u8 = TOP + 1; x as i32 }\n",
        "LE001",
        "integer overflow in statically known expression",
    );
    rejects(
        &f,
        "const ZERO: i32 = 0;\nfn main() -> i32 { 10 / ZERO }\n",
        "LE002",
        "division or remainder by zero",
    );
    rejects(
        &f,
        "const SHIFT: u32 = 33;\nfn main() -> i32 { let x: u32 = 1; (x << SHIFT) as i32 }\n",
        "LE003",
        "u32 shift count must be less than 32",
    );
    // Types still must match at the use site.
    rejects(
        &f,
        "const SMALL: u8 = 1;\nfn main() -> i32 { let x: u32 = 1; (x + SMALL) as i32 }\n",
        "TE002",
        "expected u32, found u8",
    );
    // A literal beside a constant takes the constant's type.
    project(
        &f,
        "",
        "const SMALL: u8 = 200;\nfn main() -> i32 { let x := 1 + SMALL; let y := SMALL - 100; if x == 201 && y == 100 { 42 } else { 1 } }\n",
    );
    run_source_and_wasm(&f);
    // Dynamic overflow with a constant operand still traps at run time.
    project(
        &f,
        "",
        "const TOP: u8 = 255;\nfn bump(n: u8) -> u8 { n + TOP }\nfn main() -> i32 { bump(1) as i32 }\n",
    );
    let out = f.run(&["run"]);
    assert!(!out.status.success());
}
