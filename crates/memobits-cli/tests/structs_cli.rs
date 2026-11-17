//! End-to-end struct programs (package A2): source runs, built artifacts and
//! the diagnostics users see for ownership, loans, mutability and exports.
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
            "memobits-structs-cli-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let fixture = Self(path);
        fixture.write(
            "project.toml",
            "[package]\nname='structs'\nentry='app::main'\n",
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

#[test]
fn a_share_parameter_mutates_the_caller_and_a_borrow_parameter_reads_it() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "type Counter { total: i32, steps: u8 }\n\
             fn add(c: share Counter, n: i32) { c.total += n; c.steps += 1; }\n\
             fn show(c: borrow Counter) -> i32 { if c.steps == 2 { c.total * 10 + 2 } else { 0 } }\n\
             fn main() -> i32 {\n\
                 var c := Counter { total: 0, steps: 0 };\n\
                 add(c.share(), 4);\n\
                 add(c.share(), 5);\n\
                 show(c.borrow())\n\
             }"
        ),
        "Result: i32(92)"
    );
}

#[test]
fn owned_parameters_move_the_caller_value() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "type P { x: i32, y: i32 }\n\
             fn consume(var p: P) -> i32 { p.x = p.x + 100; p.x + p.y }\n\
             fn main() -> i32 { let p := P { x: 1, y: 2 }; consume(p) }"
        ),
        "Result: i32(103)"
    );
    let message = f.error(
        "type P { x: i32, y: i32 }\n\
         fn consume(p: P) -> i32 { p.x + 0 }\n\
         fn main() -> i32 { let p := P { x: 1, y: 2 }; let a := consume(p); a + p.y }",
        "BE001",
    );
    assert!(message.contains("app.mb:3:"), "{message}");
}

#[test]
fn a_constructor_function_feeds_a_borrow_taking_function() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "type Rect { w: u8, h: u8, filled: Bool, scale: f32 }\n\
             fn rect(w: u8, h: u8) -> Rect { Rect { w: w, h: h, filled: true, scale: 1.5 } }\n\
             fn area(r: borrow Rect) -> i32 {\n\
                 let a: i32 = if r.filled { 1 } else { 0 };\n\
                 if r.w > r.h { a * 100 } else { a * 7 }\n\
             }\n\
             fn main() -> i32 { let r := rect(3, 4); let wide := rect(9, 1); area(r.borrow()) + area(wide.borrow()) }"
        ),
        "Result: i32(107)"
    );
}

#[test]
fn struct_valued_if_and_recursion_accumulating_in_a_struct() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "type P { x: i32, y: i32 }\n\
             fn pick(c: Bool) -> P { if c { P { x: 1, y: 2 } } else { P { x: 3, y: 4 } } }\n\
             fn main() -> i32 { let a := pick(true); let b := pick(false); a.x * 1000 + a.y * 100 + b.x * 10 + b.y }"
        ),
        "Result: i32(1234)"
    );
    assert_eq!(
        f.result(
            "type Acc { sum: i64, count: u32 }\n\
             fn walk(a: Acc, n: i64) -> Acc {\n\
                 if n == 0 { a } else { walk(Acc { sum: a.sum + n, count: a.count + 1 }, n - 1) }\n\
             }\n\
             fn main() -> i64 { let r := walk(Acc { sum: 0, count: 0 }, 100); r.sum }"
        ),
        "Result: i64(5050)"
    );
}

#[test]
fn mixed_width_fields_through_parameters_and_results() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "type M { a: u8, b: i64, c: f32, d: Bool }\n\
             fn make() -> M { M { a: 200, b: -9, c: 2.5, d: true } }\n\
             fn flip(m: share M) { m.a = 100; m.b *= 3; m.c += 1.0; m.d = false; }\n\
             fn relay(m: M) -> M { m }\n\
             fn main() -> i64 { var m := relay(make()); flip(m.share()); if m.d { 0 } else { m.b } }"
        ),
        "Result: i64(-27)"
    );
}

#[test]
fn field_write_while_borrowed_is_be005_and_let_field_write_is_te004() {
    let f = Fixture::new();
    f.error(
        "type P { x: i32 }\n\
         fn main() -> i32 { var p := P { x: 1 }; let r := p.borrow(); p.x = 2; r.x + 0 }",
        "BE005",
    );
    f.error(
        "type P { x: i32 }\n\
         fn two(a: share P, b: share P) {}\n\
         fn main() { var p := P { x: 1 }; two(p.share(), p.share()); }",
        "BE005",
    );
    let message = f.error(
        "type P { x: i32 }\n\
         fn main() -> i32 { let p := P { x: 1 }; p.x = 2; p.x + 0 }",
        "TE004",
    );
    assert!(message.contains("declare it with var"), "{message}");
    f.error(
        "type P { x: i32 }\n\
         fn f(p: borrow P) { p.x = 2; }\n\
         fn main() {}",
        "TE004",
    );
}

#[test]
fn a_right_hand_side_that_mutates_the_struct_runs_before_the_write() {
    let f = Fixture::new();
    // `p.x = bump(p.share())`: the share ends with the call, then the store lands.
    assert_eq!(
        f.result(
            "type P { x: i32, y: i32 }\n\
             fn bump(p: share P) -> i32 { p.x += 10; p.y += 1; 5 }\n\
             fn main() -> i32 { var p := P { x: 1, y: 100 }; p.x = bump(p.share()); p.x * 1000 + p.y }"
        ),
        "Result: i32(5101)"
    );
}

#[test]
fn private_field_writes_are_rejected_across_modules() {
    let f = Fixture::new();
    f.write(
        "src/geom.mb",
        "pub type Cell { pub open: i32, secret: i32 }\n\
         pub fn cell() -> Cell { Cell { open: 1, secret: 2 } }\n",
    );
    let message = f.error(
        "use geom::cell;\n\
         fn main() -> i32 { var c := cell(); c.open = 3; c.secret = 4; c.open + 0 }",
        "TE025",
    );
    assert!(message.contains("'secret'"), "{message}");
    assert_eq!(
        f.result(
            "use geom::cell;\n\
             fn main() -> i32 { var c := cell(); c.open = 3; c.open + 0 }"
        ),
        "Result: i32(3)"
    );
}

#[test]
fn structs_in_exported_signatures_are_rejected_with_le900() {
    let f = Fixture::new();
    for source in [
        "type P { x: i32 } fn main(p: P) -> i32 { 0 }",
        "type P { x: i32 } fn main(p: borrow P) -> i32 { 0 }",
        "type P { x: i32 } fn main(p: share P) -> i32 { 0 }",
        "type P { x: i32 } fn main() -> P { P { x: 1 } }",
    ] {
        let message = f.error(source, "LE900");
        assert!(message.contains("structs"), "{source}: {message}");
    }
    f.write(
        "project.toml",
        "[package]\nname='structs'\nentry='app::main'\n[export]\nmake='app::make'\n",
    );
    f.write(
        "src/app.mb",
        "pub type P { x: i32 } pub fn make() -> P { P { x: 1 } } fn main() -> i32 { 0 }",
    );
    let output = f.run(&["build", "--lib"]);
    assert_eq!(output.status.code(), Some(1));
    let text = String::from_utf8(output.stderr).unwrap();
    assert!(text.contains("LE900") && text.contains("structs"), "{text}");
}

#[test]
fn still_gated_struct_forms_have_clear_diagnostics() {
    let f = Fixture::new();
    for (source, code, text) in [
        (
            "type P { x: i32 } fn make() -> P { P { x: 1 } } fn main() -> i32 { make().x }",
            "TE017",
            "named local structs only",
        ),
        (
            "type P { x: i32 } fn main() -> i32 { var p := P { x: 1 }; let r := p.x.share(); 0 }",
            "TE017",
            "struct field",
        ),
        (
            "type P { x: i32 } fn main() -> i32 { let p := P { x: 1 }; let q := p.copy(); 0 }",
            "TE017",
            "copy is currently available only for primitive values",
        ),
        (
            "type P { x: i32 } type L { p: P } fn main() -> i32 { 0 }",
            "TE017",
            "struct-typed fields",
        ),
        (
            "type P { x: i32 } fn main() -> i32 { let a := [P { x: 1 }]; 0 }",
            "TE017",
            "executable arrays support",
        ),
    ] {
        let message = f.error(source, code);
        assert!(message.contains(text), "{source}: {message}");
    }
}
