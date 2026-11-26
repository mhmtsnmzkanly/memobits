//! The loan conflict diagnostics users see: what conflicts with what, in
//! source terms, with the place where the live loan began and where it is
//! used again.
use std::{
    fs,
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-loan-diag-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            "[package]\nname='diag'\nentry='app::main'\n",
        )
        .unwrap();
        Self(path)
    }
    /// The rendered diagnostics of a rejected program.
    fn rejected(&self, source: &str) -> String {
        fs::write(self.0.join("src/app.mb"), source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_mb"))
            .current_dir(&self.0)
            .arg("run")
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{source}");
        let text = String::from_utf8(output.stderr).unwrap();
        assert!(!text.contains("Site("), "{text}");
        assert!(!text.contains("Parameter("), "{text}");
        text
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const TYPES: &str = "type A { x: i32 }\ntype L { a: A, b: A }\n";

#[test]
fn write_while_shared_names_both_places_and_the_later_use() {
    let text = Fixture::new().rejected(&format!(
        "{TYPES}fn main() -> i32 {{\n    var l := L {{ a: A {{ x: 1 }}, b: A {{ x: 2 }} }};\n    var r := l.a.share();\n    l.a.x = 9;\n    r.x = 3;\n    0\n}}"
    ));
    assert!(
        text.contains("error[BE005]: cannot write `l.a.x` while it is shared"),
        "{text}"
    );
    assert!(text.contains("app.mb:6:5"), "{text}");
    assert!(text.contains("note: `l.a` was shared here"), "{text}");
    assert!(text.contains("app.mb:5:14"), "{text}");
    assert!(
        text.contains("note: the share is used later here, which keeps it alive"),
        "{text}"
    );
    assert!(text.contains("app.mb:7:5"), "{text}");
    assert_eq!(text.matches("error[").count(), 1, "{text}");
}

#[test]
fn read_while_shared() {
    let text = Fixture::new().rejected(
        "fn main() -> i32 {\n    var a := 1;\n    var r := a.share();\n    let v := a + 1;\n    r = 3;\n    v\n}",
    );
    assert!(
        text.contains("error[BE005]: cannot read `a` while it is shared"),
        "{text}"
    );
    assert!(text.contains("app.mb:4:14"), "{text}");
    assert!(text.contains("note: `a` was shared here"), "{text}");
    assert!(text.contains("app.mb:3:14"), "{text}");
}

#[test]
fn two_shares_in_one_call_are_reported_once() {
    let text = Fixture::new().rejected(&format!(
        "{TYPES}fn two(a: share A, b: share A) {{}}\nfn main() {{\n    var l := L {{ a: A {{ x: 1 }}, b: A {{ x: 2 }} }};\n    two(l.b.share(), l.b.share());\n}}"
    ));
    assert!(
        text.contains(
            "error[BE005]: cannot share `l.b` while another argument of this call already shares it"
        ),
        "{text}"
    );
    assert!(text.contains("app.mb:6:22"), "{text}");
    assert!(text.contains("note: `l.b` is shared here first"), "{text}");
    assert!(text.contains("app.mb:6:9"), "{text}");
    // Deduplicated: one conflict, one diagnostic.
    assert_eq!(text.matches("error[").count(), 1, "{text}");
}

#[test]
fn move_while_borrowed() {
    let text = Fixture::new().rejected(
        "type A { x: i32 }\nfn own(a: A) {}\nfn main() -> i32 {\n    var p := A { x: 1 };\n    let b := p.borrow();\n    own(p);\n    b.x + 0\n}",
    );
    assert!(
        text.contains("error[BE005]: cannot move `p` while it is borrowed"),
        "{text}"
    );
    assert!(text.contains("app.mb:6:9"), "{text}");
    assert!(text.contains("note: `p` was borrowed here"), "{text}");
    assert!(text.contains("app.mb:5:14"), "{text}");
    assert!(
        text.contains("note: the borrow is used later here"),
        "{text}"
    );
    assert!(text.contains("app.mb:7:5"), "{text}");
}

#[test]
fn dynamic_index_overlap_uses_a_placeholder_index() {
    let text = Fixture::new().rejected(
        "fn main() -> i32 {\n    var g := [[1, 2], [3, 4]];\n    var i := 0;\n    var j := 1;\n    var r := g[i].share();\n    g[j][0] = 5;\n    r[0] = 1;\n    0\n}",
    );
    assert!(
        text.contains("error[BE005]: cannot write `g[_][0]` while it is shared"),
        "{text}"
    );
    assert!(text.contains("app.mb:6:5"), "{text}");
    assert!(text.contains("note: `g[_]` was shared here"), "{text}");
    assert!(text.contains("app.mb:5:14"), "{text}");
    assert!(text.contains("app.mb:7:5"), "{text}");
}
