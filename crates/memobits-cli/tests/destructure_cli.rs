//! End-to-end destructuring and field-disjoint loans (package A4): source runs,
//! built artifacts and the diagnostics users see.
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
            "memobits-destructure-cli-{}-{}",
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

const TYPES: &str = "type P { x: i32, y: i32 }\n\
    type Line { a: P, b: P, n: i32 }\n\
    type Grid { cells: array<i32, 3>, k: i32 }\n";

#[test]
fn destructuring_binds_primitives_and_aggregates() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{TYPES}fn main() -> i32 {{\n\
                 let p := P {{ x: 3, y: 4 }};\n\
                 let P {{ x, y: height }} := p;\n\
                 let Line {{ a, b: other, n }} := Line {{ a: P {{ x: 1, y: 2 }}, b: P {{ x: 5, y: 6 }}, n: 7 }};\n\
                 let Grid {{ cells, k }} := Grid {{ cells: [1, 2, 3], k: 9 }};\n\
                 x * height + a.x + other.y + n + cells[2] + k\n\
             }}"
        )),
        // 12 + 1 + 6 + 7 + 3 + 9
        "Result: i32(38)"
    );
}

#[test]
fn destructuring_a_call_result_and_var_bindings() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{TYPES}fn make() -> Line {{ Line {{ a: P {{ x: 1, y: 2 }}, b: P {{ x: 3, y: 4 }}, n: 5 }} }}\n\
             fn main() -> i32 {{\n\
                 var Line {{ a, b, n }} := make();\n\
                 a.x += 10;\n\
                 b = P {{ x: 100, y: 0 }};\n\
                 n *= 2;\n\
                 a.x + b.x + n\n\
             }}"
        )),
        "Result: i32(121)"
    );
}

#[test]
fn using_a_destructured_value_is_a_move_error() {
    let f = Fixture::new();
    for body in [
        "let p := P { x: 1, y: 2 }; let P { x, y } := p; p.x + x",
        "let l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 }, n: 5 }; let Line { a, b, n } := l; let m := l; n",
    ] {
        let message = f.error(&format!("{TYPES}fn main() -> i32 {{ {body} }}"), "BE001");
        assert!(message.contains("app.mb:"), "{message}");
    }
}

#[test]
fn pattern_diagnostics_are_rendered_with_codes() {
    let f = Fixture::new();
    for (body, code, text) in [
        ("let P { x } := P { x: 1, y: 2 }; x", "TE023", "missing: y"),
        ("let P { x, y, z } := P { x: 1, y: 2 }; x", "TE023", "no field 'z'"),
        ("let P { x, x: w, y } := P { x: 1, y: 2 }; x", "TE023", "more than once"),
        ("let P { x, y: x } := P { x: 1, y: 2 }; x", "TE023", "introduced more than once"),
        (
            "let Line { a: P { x, y }, b, n } := Line { a: P { x: 1, y: 2 }, b: P { x: 1, y: 2 }, n: 1 }; n",
            "SE002",
            "nested destructuring",
        ),
        ("let P { x, .. } := P { x: 1, y: 2 }; x", "SE002", "`..`"),
        ("let P { x, y } := P { x: 1, y: 2 }; x = 3; x", "TE004", "immutable binding 'x'"),
    ] {
        let message = f.error(&format!("{TYPES}fn main() -> i32 {{ {body} }}"), code);
        assert!(message.contains(text), "{body}: {message}");
        assert!(message.contains("app.mb:"), "{message}");
    }
}

#[test]
fn destructuring_respects_field_privacy_across_modules() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='structs'\nentry='main::main'\n",
    );
    f.write(
        "src/geom.mb",
        "pub type Point { pub x: i32, pub y: i32 }\n\
         pub type Account { pub id: i32, balance: i32 }\n\
         pub fn account() -> Account { Account { id: 1, balance: 2 } }\n",
    );
    f.write(
        "src/main.mb",
        "use geom::Point; use geom::Account; use geom::account;\n\
         fn main() -> i32 { let geom::Point { x, y } := geom::Point { x: 3, y: 4 }; \
             let Point { x: px, y: py } := Point { x: 5, y: 6 }; x * y + px + py }\n",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert!(String::from_utf8_lossy(&source.stdout).contains("Result: i32(23)"));
    f.write(
        "src/main.mb",
        "use geom::Account; use geom::account;\n\
         fn main() -> i32 { let Account { id, balance } := account(); id }\n",
    );
    let output = f.run(&["run"]);
    assert_eq!(output.status.code(), Some(1));
    let message = String::from_utf8(output.stderr).unwrap();
    assert!(message.contains("TE025"), "{message}");
    assert!(
        message.contains("cannot destructure struct 'Account' outside module 'geom'"),
        "{message}"
    );
}

#[test]
fn disjoint_fields_and_constant_rows_can_be_lent_together() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{TYPES}fn read(p: borrow P) -> i32 {{ p.x * 10 + p.y }}\n\
             fn bump(p: share P) {{ p.x += 1; }}\n\
             fn both(a: share P, b: share P) {{ a.x += b.x; b.y += a.y; }}\n\
             fn rows(a: share array<i32, 3>, b: borrow array<i32, 3>) {{ a[0] += b[2]; }}\n\
             fn main() -> i32 {{\n\
                 var l := Line {{ a: P {{ x: 1, y: 2 }}, b: P {{ x: 3, y: 4 }}, n: 0 }};\n\
                 let r := l.a.borrow();\n\
                 l.b.x = 5;\n\
                 bump(l.b.share());\n\
                 let seen := read(r);\n\
                 both(l.a.share(), l.b.share());\n\
                 var m := [[1, 2, 3], [4, 5, 6]];\n\
                 rows(m[0].share(), m[1].borrow());\n\
                 seen * 1000 + l.a.x * 100 + l.b.y * 10 + m[0][0]\n\
             }}"
        )),
        // seen = 12; both: a.x = 1 + 6 = 7, b.y = 4 + 2 = 6; m[0][0] = 1 + 6 = 7
        "Result: i32(12767)"
    );
}

#[test]
fn overlapping_loans_are_rejected_with_be005() {
    let f = Fixture::new();
    for (body, line) in [
        // The same field, or the whole root, while a field loan is live.
        ("let r := l.a.borrow(); l.a.x = 5; r.x", "l.a.x = 5;"),
        (
            "let r := l.a.borrow(); l = Line { a: P { x: 0, y: 0 }, b: P { x: 0, y: 0 }, n: 0 }; r.x",
            "l = Line",
        ),
        ("let r := l.a.borrow(); let q := l; r.x", "let q := l;"),
        // Two share arguments of one field, or of dynamic rows.
        ("both(l.a.share(), l.a.share()); 0", "both(l.a.share(), l.a.share())"),
        (
            "var m := [[1, 2], [3, 4]]; var i := 0; var j := 1; two(m[i].share(), m[j].share()); 0",
            "two(m[i].share(), m[j].share())",
        ),
        // A dynamic share against a write to a constant element.
        (
            "var m := [[1, 2], [3, 4]]; var i := 1; var r := m[i].share(); m[0][0] = 9; r[0] = 1; 0",
            "m[0][0] = 9",
        ),
    ] {
        let message = f.error(
            &format!(
                "{TYPES}fn both(a: share P, b: share P) {{}}\n\
                 fn two(a: share array<i32, 2>, b: share array<i32, 2>) {{}}\n\
                 fn main() -> i32 {{\n\
                     var l := Line {{ a: P {{ x: 1, y: 2 }}, b: P {{ x: 3, y: 4 }}, n: 0 }};\n\
                     {body}\n\
                 }}"
            ),
            "BE005",
        );
        assert!(message.contains(line), "{body}: {message}");
    }
}

#[test]
fn loans_live_across_loop_back_edges_keep_their_paths() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{TYPES}fn main() -> i32 {{\n\
                 var l := Line {{ a: P {{ x: 1, y: 2 }}, b: P {{ x: 3, y: 4 }}, n: 0 }};\n\
                 let r := l.a.borrow();\n\
                 var i := 0;\n\
                 loop {{ l.b.x += 1; i += 1; if i > 2 {{ break; }} }}\n\
                 r.x * 100 + l.b.x\n\
             }}"
        )),
        "Result: i32(106)"
    );
    f.error(
        &format!(
            "{TYPES}fn main() -> i32 {{\n\
                 var l := Line {{ a: P {{ x: 1, y: 2 }}, b: P {{ x: 3, y: 4 }}, n: 0 }};\n\
                 let r := l.a.borrow();\n\
                 var i := 0;\n\
                 loop {{ l.a.x += 1; i += 1; if i > 2 {{ break; }} }}\n\
                 r.x\n\
             }}"
        ),
        "BE005",
    );
}
