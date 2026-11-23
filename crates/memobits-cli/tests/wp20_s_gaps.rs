//! WP20 reconciliation closures: small source + standalone Wasm tests and exact
//! diagnostics for I1, G1, G2, OP1 and D1 acceptance clauses.

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
            "memobits-wp20-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let fixture = Self(path);
        fixture.write(
            "project.toml",
            "[package]\nname='wp20'\nentry='main::main'\n",
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

    /// Runs the project from source and as a standalone Wasm artifact and
    /// returns the (identical) stdout.
    fn both(&self, expected: &str) {
        let source = self.run(&["run"]);
        assert!(source.status.success(), "source: {source:?}");
        assert_eq!(String::from_utf8_lossy(&source.stdout), expected);
        let build = self.run(&["build", "--output", "out.wasm"]);
        assert!(build.status.success(), "build: {build:?}");
        let wasm = self.run(&["run", "out.wasm"]);
        assert!(wasm.status.success(), "wasm: {wasm:?}");
        assert!(wasm.stderr.is_empty(), "wasm stderr: {wasm:?}");
        assert_eq!(wasm.stdout, source.stdout);
    }

    /// Asserts that analysis fails with the diagnostic `code` and returns stderr.
    fn rejects(&self, code: &str) -> String {
        let output = self.run(&["analyze-project"]);
        assert!(!output.status.success(), "{output:?}");
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert!(stderr.contains(code), "expected {code}: {stderr}");
        stderr
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const DRAW_TYPES: &str = "pub type Point { pub x: i32 }\n\
    pub interface Draw { fn draw(borrow self) -> i32; }\n";
const DRAW_EXTENSION: &str = "use self::main::{Point, Draw}; \
    pub extend Point of Draw { fn draw(borrow self) -> i32 { self.x } } \
    pub fn ping() -> i32 { 0 } pub fn pong() -> i32 { 1 }";
const NO_EXTENSION: &str = "no visible extension implements 'main::Draw::draw' for Point";

// ---- I1 ----

#[test]
fn grouped_selector_chain_runs_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        "type Point { x: i32 }\n\
         interface Draw { fn draw(borrow self) -> Point; }\n\
         interface Inspect { fn inspect(borrow self) -> i32; }\n\
         extend Point of Draw { fn draw(borrow self) -> Point { Point { x: self.x } } }\n\
         extend Point of Inspect { fn inspect(borrow self) -> i32 { self.x } }\n\
         fn main() -> i32 { let p := Point { x: 42 }; (p.draw() of Draw).inspect() of Inspect }",
    );
    f.both("Result: i32(42)\n");
}

#[test]
fn grouped_symbol_import_does_not_activate_an_extension() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        &format!(
            "use self::graphics::{{ping, pong}};\n{DRAW_TYPES}\
             fn main() -> i32 {{ let point := Point {{ x: 42 }}; point.draw() of Draw }}"
        ),
    );
    f.write("src/graphics.mb", DRAW_EXTENSION);
    let stderr = f.rejects("TE007");
    assert!(stderr.contains(NO_EXTENSION), "{stderr}");
}

#[test]
fn transitive_and_prelude_references_do_not_activate_an_interface_extension() {
    let f = Fixture::new();
    f.write("src/graphics.mb", DRAW_EXTENSION);
    f.write("src/bridge.mb", "use graphics; pub fn marker() {}");
    let main = format!(
        "{DRAW_TYPES}fn main() -> i32 {{ let point := Point {{ x: 42 }}; point.draw() of Draw }}"
    );
    // Transitive: main imports bridge, bridge imports the extension module.
    f.write("src/main.mb", &format!("use bridge;\n{main}"));
    let stderr = f.rejects("TE007");
    assert!(stderr.contains(NO_EXTENSION), "{stderr}");

    // Prelude alias to a symbol of the extension module.
    f.write("src/main.mb", &main);
    f.write(
        "project.toml",
        "[package]\nname='wp20'\nentry='main::main'\n[prelude]\nmarker='graphics::ping'\n",
    );
    let stderr = f.rejects("TE007");
    assert!(stderr.contains(NO_EXTENSION), "{stderr}");

    // Positive control: a direct module import activates it.
    f.write(
        "project.toml",
        "[package]\nname='wp20'\nentry='main::main'\n",
    );
    f.write("src/main.mb", &format!("use graphics;\n{main}"));
    f.both("Result: i32(42)\n");
}

// ---- G1 ----

#[test]
fn generic_function_specialization_limit_is_reported() {
    let f = Fixture::new();
    let mut source = String::new();
    for index in 0..257 {
        source.push_str(&format!("type Marker{index} {{}}\n"));
    }
    source.push_str("fn ping<T>(value: T) -> i32 { 1 }\nfn main() {\n");
    for index in 0..257 {
        source.push_str(&format!("ping(Marker{index} {{}});\n"));
    }
    source.push_str("}\n");
    f.write("src/main.mb", &source);
    let stderr = f.rejects("TE007");
    assert!(
        stderr.contains("generic specialization limit exceeded (maximum 256 distinct functions)"),
        "{stderr}"
    );
}

// ---- G2 ----

#[test]
fn wrong_annotated_output_type_is_rejected_directly_and_through_generics() {
    let f = Fixture::new();
    let prelude = "use core::ops::Add; \
        type Left { value: i32 } type Right { value: i32 } \
        type Sum { value: i32 } type Other { value: i32 } \
        extend Left of Add { type Rhs = Right; type Output = Sum; \
            fn add(self, rhs: Right) -> Sum { Sum { value: self.value + rhs.value } } } ";
    f.write(
        "src/main.mb",
        &format!(
            "{prelude}fn main() -> i32 {{ let r: Other = Left {{ value: 1 }} + Right {{ value: 2 }}; r.value }}"
        ),
    );
    let stderr = f.rejects("TE002");
    assert!(stderr.contains("expected Other, found Sum"), "{stderr}");

    f.write(
        "src/main.mb",
        &format!(
            "{prelude}fn go<T>(l: T, r: T::Rhs) -> T::Output where T: Add {{ l + r }} \
             fn main() -> i32 {{ let r: Other = go(Left {{ value: 1 }}, Right {{ value: 2 }}); r.value }}"
        ),
    );
    let stderr = f.rejects("TE002");
    assert!(stderr.contains("expected Other, found Sum"), "{stderr}");

    // Positive control: the declared Output type is accepted.
    f.write(
        "src/main.mb",
        &format!(
            "{prelude}fn go<T>(l: T, r: T::Rhs) -> T::Output where T: Add {{ l + r }} \
             fn main() -> i32 {{ let r: Sum = go(Left {{ value: 40 }}, Right {{ value: 2 }}); r.value }}"
        ),
    );
    f.both("Result: i32(42)\n");
}

// ---- OP1 ----

#[test]
fn mixed_type_primitive_arithmetic_is_not_coerced() {
    let f = Fixture::new();
    for operator in ["+", "-", "*", "/", "%"] {
        f.write(
            "src/main.mb",
            &format!(
                "fn main() -> i32 {{ let a: u32 = 1; let b: i32 = 1; let c := a {operator} b; 0 }}"
            ),
        );
        let stderr = f.rejects("TE002");
        assert!(
            stderr.contains("expected u32, found i32"),
            "{operator}: {stderr}"
        );
    }
}

#[test]
fn signed_shifts_of_every_width_are_rejected() {
    let f = Fixture::new();
    for ty in ["i8", "i16", "i64"] {
        for shift in ["<<", ">>"] {
            f.write(
                "src/main.mb",
                &format!("fn main() -> {ty} {{ let a: {ty} = 1; a {shift} 1 }}"),
            );
            let stderr = f.rejects("TE002");
            assert!(
                stderr.contains(&format!("expected u32, found {ty}")),
                "{ty} {shift}: {stderr}"
            );
        }
        for compound in ["<<=", ">>=", "&=", "|=", "^="] {
            f.write(
                "src/main.mb",
                &format!("fn main() -> {ty} {{ var a: {ty} = 1; a {compound} 1; a }}"),
            );
            let stderr = f.rejects("TE007");
            assert!(
                stderr.contains("primitive bitwise compound assignment currently requires u32"),
                "{ty} {compound}: {stderr}"
            );
        }
    }
}

#[test]
fn unary_plus_not_complement_range_update_and_optional_have_no_overload() {
    let f = Fixture::new();
    let prelude = "use core::ops::Neg; type Cell { value: i32 } \
        interface Pos { fn pos(self) -> Cell; } interface Not { fn not(self) -> Cell; } \
        extend Cell of Pos { fn pos(self) -> Cell { self } } \
        extend Cell of Not { fn not(self) -> Cell { self } } \
        extend Cell of Neg { type Output = Cell; fn neg(self) -> Cell { self } } ";
    let cases = [
        ("+x", "TE007"),
        ("!x", "TE002"),
        ("~x", "SE001"),
        ("x++", "SE002"),
        ("x ?? y", "SE002"),
        ("x..y", "SE002"),
        ("x..=y", "SE002"),
    ];
    for (expression, code) in cases {
        f.write(
            "src/main.mb",
            &format!(
                "{prelude}fn main() {{ let x := Cell {{ value: 1 }}; let y := Cell {{ value: 2 }}; let z := {expression}; }}"
            ),
        );
        let stderr = f.rejects(code);
        match expression {
            "+x" => assert!(
                stderr.contains("unary arithmetic requires a number"),
                "{stderr}"
            ),
            "!x" => assert!(stderr.contains("expected Bool, found Cell"), "{stderr}"),
            _ => {}
        }
    }
    // Positive control: user `-` still selects Neg for the same type.
    f.write(
        "src/main.mb",
        &format!(
            "{prelude}fn main() -> i32 {{ let x := Cell {{ value: 42 }}; let y := -x; y.value }}"
        ),
    );
    f.both("Result: i32(42)\n");
}

#[test]
fn all_five_primitive_u32_compound_operators_match_source_and_wasm() {
    let f = Fixture::new();
    // 4294967295 &= 255 -> 255; |= 3840 -> 4095; ^= 1365 -> 2730;
    // <<= 4 -> 43680; >>= 2 -> 10920; then +2 to land on 10922.
    f.write(
        "src/main.mb",
        "fn main() -> Result<u32, Error> {\n\
            var a: u32 = 4294967295;\n\
            a &= 255; if a != 255 { return Err(Error { code: 1 }); }\n\
            a |= 3840; if a != 4095 { return Err(Error { code: 2 }); }\n\
            a ^= 1365; if a != 2730 { return Err(Error { code: 3 }); }\n\
            a <<= 4; if a != 43680 { return Err(Error { code: 4 }); }\n\
            a >>= 2; if a != 10920 { return Err(Error { code: 5 }); }\n\
            Ok(a + 2)\n\
         }",
    );
    f.both("Result: Ok(u32(10922))\n");
}

// ---- D1 ----

#[test]
fn bodyless_and_empty_nominal_types_run_trailing_methods_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        "type Token; extend { fn kind(borrow self) -> i32 { 1 } }\n\
         type Empty {} extend { fn kind(borrow self) -> i32 { 41 } }\n\
         fn probe(token: borrow Token) -> i32 { token.kind() }\n\
         fn main() -> i32 { let e := Empty {}; e.kind() + 1 }",
    );
    f.both("Result: i32(42)\n");
}

#[test]
fn named_enum_and_struct_reference_payloads_stay_rejected() {
    let f = Fixture::new();
    for source in [
        "type Named [ Held((borrow i32)?), Free ] fn main() {}",
        "type Named { r: (borrow i32)? } fn main() {}",
    ] {
        f.write("src/main.mb", source);
        let stderr = f.rejects("TE017");
        assert!(
            stderr.contains("reference type arguments require embedded-loan tracking"),
            "{source}: {stderr}"
        );
    }
}
