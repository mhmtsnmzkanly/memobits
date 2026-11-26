//! End-to-end enum programs (package B1): source runs and built artifacts,
//! cross-module construction, and the diagnostics users see. These programs
//! never inspect an enum, so they return primitives computed next to the enum
//! traffic; `match` programs live in `match_cli.rs`.
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
            "memobits-enums-cli-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let fixture = Self(path);
        fixture.write(
            "project.toml",
            "[package]\nname='enums'\nentry='app::main'\n",
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
    /// Run a program from source and again from its built artifact; both must agree.
    fn result(&self, source: &str) -> String {
        self.write("src/app.mb", source);
        let from_source = self.run(&["run"]);
        assert!(
            from_source.status.success(),
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
        assert_eq!(from_source.stdout, from_artifact.stdout, "{source}");
        String::from_utf8(from_source.stdout).unwrap().trim().into()
    }
    fn error(&self, source: &str, code: &str) -> String {
        self.write("src/app.mb", source);
        let output = self.run(&["run"]);
        assert_eq!(output.status.code(), Some(1), "{source}");
        assert!(output.stdout.is_empty());
        let text = String::from_utf8(output.stderr).unwrap();
        assert!(text.contains(code), "{source}: {text}");
        text
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const SHAPE: &str = "type P { x: i32, y: i64 }\n\
    type Shape [ Empty, Circle(f64), Rect(i32, i32), Poly(P, array<u8, 3>) ]\n";

#[test]
fn programs_that_build_move_and_pass_enums_run_from_source_and_artifact() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{SHAPE}\
             fn make(n: i32) -> Shape {{ if n > 0 {{ Shape::Rect(n, 2) }} else {{ Shape::Empty }} }}\n\
             fn eat(s: Shape) -> i32 {{ 3 }}\n\
             fn peek(s: borrow Shape) -> i32 {{ 4 }}\n\
             fn poke(s: share Shape) {{ s = Shape::Circle(1.5); }}\n\
             fn main() -> i32 {{\n\
                 var s := Shape::Poly(P {{ x: 1, y: 2 }}, [1, 2, 3]);\n\
                 let a := peek(s.borrow());\n\
                 poke(s.share());\n\
                 let t := make(4);\n\
                 let moved := t;\n\
                 let b := eat(moved);\n\
                 let c := eat(s);\n\
                 a * 100 + b * 10 + c\n\
             }}"
        )),
        "Result: i32(433)"
    );
}

#[test]
fn enum_fields_arrays_repetition_and_joins_run() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{SHAPE}\
             type H {{ n: i32, s: Shape }}\n\
             fn count(h: borrow H) -> i32 {{ h.n }}\n\
             fn first(a: borrow array<Shape, 3>) -> i32 {{ 5 }}\n\
             fn main() -> i32 {{\n\
                 let h := H {{ n: 7, s: Shape::Circle(2.0) }};\n\
                 var grid: array<Shape, 3> = [Shape::Empty; 3];\n\
                 grid[1] = Shape::Rect(1, 2);\n\
                 let pick := if h.n > 3 {{ Shape::Empty }} else {{ Shape::Circle(0.0) }};\n\
                 count(h.borrow()) + first(grid.borrow())\n\
             }}"
        )),
        "Result: i32(12)"
    );
}

#[test]
fn enums_cross_module_boundaries() {
    let f = Fixture::new();
    f.write(
        "src/shapes.mb",
        "pub type Shape [ Empty, Circle(f64), Rect(i32, i32) ]\n\
         pub fn unit() -> Shape { Shape::Empty }\n\
         pub fn square(n: i32) -> Shape { Shape::Rect(n, n) }\n\
         pub fn weigh(s: borrow Shape) -> i32 { 9 }\n",
    );
    assert_eq!(
        f.result(
            "use shapes::Shape;\n\
             use shapes::weigh;\n\
             type Local [ One(Shape), None ]\n\
             fn main() -> i32 {\n\
                 let a := Shape::Circle(1.5);\n\
                 let b := shapes::Shape::Rect(2, 3);\n\
                 let c := shapes::square(4);\n\
                 let d := Local::One(shapes::unit());\n\
                 let e := Local::One(Shape::Empty);\n\
                 weigh(a.borrow()) + weigh(c.borrow()) + weigh(b.borrow())\n\
             }"
        ),
        "Result: i32(27)"
    );
}

#[test]
fn cross_module_construction_diagnostics() {
    let f = Fixture::new();
    f.write(
        "src/shapes.mb",
        "pub type Shape [ Empty, Circle(f64) ]\ntype Hidden [ A, B ]\n",
    );
    let text = f.error(
        "use shapes::Shape;\nfn main() -> i32 { let a := Shape::Missing; 0 }",
        "ME006",
    );
    assert!(text.contains("Missing"), "{text}");
    let text = f.error(
        "fn main() -> i32 { let a := shapes::Hidden::A; 0 }",
        "ME007",
    );
    assert!(text.contains("private"), "{text}");
    let text = f.error(
        "use shapes::Shape;\nfn main() -> i32 { let a := Shape::Circle(true); 0 }",
        "TE002",
    );
    assert!(text.contains("app.mb:2:"), "{text}");
    f.error(
        "use shapes::Shape;\nfn main() -> i32 { let a := Shape::Circle; 0 }",
        "TE028",
    );
}

#[test]
fn construction_diagnostics_point_at_the_source() {
    let f = Fixture::new();
    for (body, code, text) in [
        ("let e := Shape::Triangle;", "NE004", "unknown variant"),
        (
            "let e := Shape::Rect(1);",
            "TE010",
            "expects 2 argument(s), found 1",
        ),
        ("let e := Shape::Rect(1, 2, 3);", "TE010", "expects 2"),
        ("let e := Shape::Circle(true);", "TE002", "expected f64"),
        ("let e := Shape::Empty(1);", "TE028", "has no payload"),
        (
            "let e := Shape::Circle;",
            "TE028",
            "construct it as Shape::Circle(...)",
        ),
        ("let e := Shape::Poly(1, [1, 2, 3]);", "TE002", "expected P"),
        ("Shape::Empty;", "TE017", "owned value"),
    ] {
        let message = f.error(&format!("{SHAPE}fn main() -> i32 {{ {body} 0 }}"), code);
        assert!(message.contains(text), "{body}: {message}");
        assert!(message.contains("app.mb:3:"), "{body}: {message}");
    }
}

#[test]
fn declaration_diagnostics() {
    let f = Fixture::new();
    for (source, code, text) in [
        (
            "type E [] fn main() -> i32 { 0 }",
            "TE027",
            "declares no variants",
        ),
        (
            "type E [ A, A ] fn main() -> i32 { 0 }",
            "NE006",
            "duplicate variant 'A'",
        ),
        (
            "type E [ A(E) ] fn main() -> i32 { 0 }",
            "TE026",
            "recursive enum",
        ),
        (
            "type E [ A(array<E, 2>) ] fn main() -> i32 { 0 }",
            "TE026",
            "recursive enum",
        ),
        (
            "type S { e: E } type E [ A(S) ] fn main() -> i32 { 0 }",
            "TE026",
            "recursive",
        ),
        (
            "type E [ A(Missing) ] fn main() -> i32 { 0 }",
            "NE003",
            "Missing",
        ),
    ] {
        let message = f.error(source, code);
        assert!(message.contains(text), "{source}: {message}");
    }
}

#[test]
fn use_after_move_of_an_enum_is_be001() {
    let f = Fixture::new();
    for body in [
        "let a := Shape::Empty; let b := a; let c := a;",
        "let a := Shape::Empty; eat(a); eat(a);",
        "let a := Shape::Circle(1.0); let h := H { s: a }; let b := a;",
        "let a := Shape::Empty; let xs := [a, Shape::Empty]; eat(a);",
        "let p := P { x: 1, y: 2 }; let a := Shape::Poly(p, [1, 2, 3]); let q := p;",
    ] {
        let text = f.error(
            &format!(
                "{SHAPE}type H {{ s: Shape }}\nfn eat(s: Shape) {{}}\nfn main() -> i32 {{ {body} 0 }}"
            ),
            "BE001",
        );
        assert!(text.contains("unavailable after a move"), "{body}: {text}");
    }
}

#[test]
fn whole_enum_loans_conflict_with_any_access() {
    let f = Fixture::new();
    let decls = format!(
        "{SHAPE}fn peek(s: borrow Shape) {{}}\nfn poke(s: share Shape) {{}}\nfn eat(s: Shape) {{}}\n\
         fn two(a: share Shape, b: share Shape) {{}}\n"
    );
    for (body, text) in [
        (
            "var a := Shape::Empty; let r := a.borrow(); a = Shape::Circle(1.0); peek(r);",
            "cannot assign to `a` while it is borrowed",
        ),
        (
            "var a := Shape::Empty; let r := a.borrow(); eat(a); peek(r);",
            "cannot move `a` while it is borrowed",
        ),
        (
            "var a := Shape::Empty; let r := a.share(); peek(a.borrow()); poke(r);",
            "while it is shared",
        ),
        (
            "var a := Shape::Empty; two(a.share(), a.share());",
            "cannot share `a` while another argument of this call already shares it",
        ),
    ] {
        let message = f.error(&format!("{decls}fn main() -> i32 {{ {body} 0 }}"), "BE005");
        assert!(message.contains(text), "{body}: {message}");
    }
    // Sequential, non-overlapping accesses are fine.
    assert_eq!(
        f.result(&format!(
            "{decls}fn main() -> i32 {{ var a := Shape::Empty; peek(a.borrow()); \
             poke(a.share()); a = Shape::Circle(1.0); eat(a); 6 }}"
        )),
        "Result: i32(6)"
    );
}

#[test]
fn enums_in_exported_signatures_are_rejected_with_le900() {
    let f = Fixture::new();
    for source in [
        "type E [ A, B ] fn main(e: E) -> i32 { 0 }",
        "type E [ A, B ] fn main(e: borrow E) -> i32 { 0 }",
        "type E [ A, B ] fn main(e: share E) -> i32 { 0 }",
        "type E [ A, B ] fn main() -> E { E::A }",
    ] {
        let message = f.error(source, "LE900");
        assert!(message.contains("enums"), "{source}: {message}");
    }
    f.write(
        "project.toml",
        "[package]\nname='enums'\nentry='app::main'\n[export]\nmake='app::make'\n",
    );
    f.write(
        "src/app.mb",
        "pub type E [ A, B(i32) ] pub fn make() -> E { E::B(1) } fn main() -> i32 { 0 }",
    );
    let output = f.run(&["build", "--lib"]);
    assert_eq!(output.status.code(), Some(1));
    let text = String::from_utf8(output.stderr).unwrap();
    assert!(text.contains("LE900") && text.contains("enums"), "{text}");
}

#[test]
fn a_300_variant_enum_runs() {
    let f = Fixture::new();
    let variants = (0..300)
        .map(|i| format!("V{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    assert_eq!(
        f.result(&format!(
            "type Big [ {variants} ]\nfn main() -> i32 {{ let a := Big::V299; let b := Big::V0; 7 }}"
        )),
        "Result: i32(7)"
    );
}

#[test]
fn an_enum_frame_over_the_configured_stack_is_le900() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='enums'\nentry='app::main'\n[build]\nstack_size=4096\n",
    );
    let text = f.error(
        "type Big [ A(array<i64, 1000>), B ]\nfn main() -> i32 { let b := Big::B; 1 }",
        "LE900",
    );
    assert!(text.contains("enum frame layout"), "{text}");
}

#[test]
fn an_enum_value_cannot_be_read_by_field_index_or_operator() {
    let f = Fixture::new();
    for (body, code) in [
        ("let a := Shape::Empty; let n := a.x;", "TE024"),
        ("let a := Shape::Empty; let n := a[0];", "TE007"),
        (
            "let a := Shape::Empty; let b := Shape::Empty; let c := a == b;",
            "TE007",
        ),
    ] {
        f.error(&format!("{SHAPE}fn main() -> i32 {{ {body} 0 }}"), code);
    }
}
