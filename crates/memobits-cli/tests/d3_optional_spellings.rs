//! D3 acceptance tests: removed spellings fail with TE001 replacement guidance,
//! plus the `T?` clauses that needed dedicated evidence (contextual None,
//! matching, type errors).

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
            "memobits-d3-optional-{}-{}",
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

    fn project(&self, source: &str) {
        self.write(
            "project.toml",
            "[package]\nname='d3-optional'\nentry='main::main'\n",
        );
        self.write("src/main.mb", source);
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

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

#[test]
fn removed_spellings_fail_with_te001_replacement_guidance() {
    let f = Fixture::new();
    for (source, guidance) in [
        ("fn f(a: Option<i32>) {} fn main() {}", "write 'T?' instead"),
        (
            "fn f(a: Result<i32, Error>) {} fn main() {}",
            "write 'T ! E' instead",
        ),
        (
            "fn f(a: Attempt<i32, Error>) {} fn main() {}",
            "write 'T ?! E' instead",
        ),
        ("fn f(a: Bool) {} fn main() {}", "write 'bool' instead"),
        ("fn f(a: Char) {} fn main() {}", "write 'char' instead"),
        (
            "fn f(a: Array<u8, 2>) {} fn main() {}",
            "write 'array<T, N>' instead",
        ),
    ] {
        f.project(source);
        for args in [&["check"][..], &["build"][..], &["run"][..]] {
            let output = f.run(args);
            assert_eq!(output.status.code(), Some(1), "{source} {args:?}");
            assert!(output.stdout.is_empty(), "{source} {args:?}");
            let text = stderr(&output);
            assert!(
                text.contains("error[TE001]") && text.contains(guidance),
                "{source} {args:?}: {text}"
            );
            assert!(!text.contains("warning"), "{source} {args:?}: {text}");
        }
    }
}

#[test]
fn postfix_optional_spelling_produces_no_warning() {
    let f = Fixture::new();
    f.project(
        "fn pick(value: i32?) -> i32? { value }\nfn main() -> i32 { let n: i32? = pick(Some(40)); let nested: i32?? = None; match n { Some(v) => v + 2, None => 0 } }\n",
    );
    for args in [&["check"][..], &["run"][..]] {
        let output = f.run(args);
        assert_eq!(
            output.status.code(),
            Some(0),
            "{args:?}: {}",
            stderr(&output)
        );
        assert!(output.stderr.is_empty(), "{args:?}: {}", stderr(&output));
    }
    assert_eq!(stdout(&f.run(&["run"])), "Result: i32(42)\n");
    // Grouped reference spelling is not a legacy spelling either: it keeps its
    // transport gate error and reports no warning.
    f.project("fn take(value: (borrow i32)?) {}\nfn main() {}\n");
    let output = f.run(&["check"]);
    assert_eq!(output.status.code(), Some(1));
    let text = stderr(&output);
    assert!(
        text.contains("TE017") && !text.contains("warning"),
        "{text}"
    );
}

#[test]
fn option_spelling_with_borrow_payloads_and_nesting_is_silent() {
    let f = Fixture::new();
    f.project(
        r#"
        fn read(value: borrow i32) -> i32 { value.copy() }
        type Box { slot: i32? }
        fn main() -> i32 {
            var owner := 40;
            let wrapped: (borrow i32)? = Some(owner.borrow());
            let inner: i32?? = None;
            let seen := match wrapped { Some(view) => read(view), None => 0 };
            seen + 2
        }
        "#,
    );
    let output = f.run(&["run"]);
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    assert_eq!(stdout(&output), "Result: i32(42)\n");
    assert!(output.stderr.is_empty(), "{}", stderr(&output));
}

#[test]
fn option_spelling_in_an_imported_module_is_silent() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='d3-optional'\nentry='main::main'\n",
    );
    f.write(
        "src/model.mb",
        "pub type Maybe = u32?;\npub fn none() -> Maybe { None }\n",
    );
    f.write(
        "src/main.mb",
        "use model;\nfn main() -> i32 { match model::none() { Some(n) => n as i32, None => 42 } }\n",
    );
    let output = f.run(&["run"]);
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    assert_eq!(stdout(&output), "Result: i32(42)\n");
    assert!(output.stderr.is_empty(), "{}", stderr(&output));
}

#[test]
fn contextual_none_and_matching_work_through_calls_and_returns_in_source_and_wasm() {
    let f = Fixture::new();
    f.project(
        r#"
        fn choose(flag: bool) -> i32? { if flag { Some(40) } else { None } }
        fn value_or(item: i32?, fallback: i32) -> i32 {
            match item { Some(n) => n, None => fallback }
        }
        fn main() -> i32 {
            value_or(choose(true), 0) + value_or(None, 2) + value_or(choose(false), 0)
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert_eq!(source.status.code(), Some(0), "{}", stderr(&source));
    assert_eq!(stdout(&source), "Result: i32(42)\n");
    assert!(source.stderr.is_empty(), "{}", stderr(&source));
    let build = f.run(&["build", "--output", "out.wasm"]);
    assert_eq!(build.status.code(), Some(0), "{}", stderr(&build));
    let artifact = f.run(&["run", "out.wasm"]);
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn postfix_optional_type_errors_are_reported() {
    let f = Fixture::new();
    for (source, message) in [
        (
            "fn main() { let flag: bool? = Some(1); }",
            "expected bool, found",
        ),
        (
            "fn main() { let value := None; }",
            "cannot determine None's outcome type; provide a 'T?' annotation",
        ),
        ("fn take(value: i32?) {} fn main() { take(true); }", "TE002"),
    ] {
        f.project(source);
        let output = f.run(&["check"]);
        assert_eq!(output.status.code(), Some(1), "{source}");
        let text = stderr(&output);
        assert!(
            text.contains("TE002") && text.contains(message),
            "{source}: {text}"
        );
    }
}

#[test]
fn optional_and_fallible_operators_compose_in_source_and_wasm() {
    let f = Fixture::new();
    f.project(
        "fn lookup(value: u32?) -> u32 ?! Error { match value { Some(n) => if n > 100 { Err(Error { code: n }) } else { Ok(Some(n)) }, None => Ok(None) } }\nfn main() -> i32 { let a: u32? = Some(42); match lookup(a) { Ok(Some(n)) => n as i32, Ok(None) => 0, Err(e) => 0 - e.code as i32 } }\n",
    );
    let output = f.run(&["run"]);
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    assert_eq!(stdout(&output), "Result: i32(42)\n");
    assert!(output.stderr.is_empty(), "{}", stderr(&output));
}
