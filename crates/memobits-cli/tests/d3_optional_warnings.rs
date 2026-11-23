//! D3 acceptance tests: the non-failing MW warning channel (proven with MW003)
//! and silent `Option<T>` acceptance, plus the `T?` clauses that needed
//! dedicated evidence (contextual None, matching, type errors).

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

const LEGACY: &str = "fn pick(value: Option<i32>) -> i32 {\n    match value { Some(n) => n, None => 2 }\n}\nfn main() -> i32 { pick(Some(40)) + pick(None) }\n";

#[test]
fn option_spelling_is_silent_on_check_build_and_run() {
    let f = Fixture::new();
    f.project(LEGACY);
    for args in [
        &["check"][..],
        &["build", "--output", "out.wasm"][..],
        &["run"][..],
    ] {
        let output = f.run(args);
        assert_eq!(
            output.status.code(),
            Some(0),
            "{args:?}: {}",
            stderr(&output)
        );
        assert!(output.stderr.is_empty(), "{args:?}: {}", stderr(&output));
    }
    let run = f.run(&["run"]);
    assert_eq!(stdout(&run), "Result: i32(42)\n");
    let artifact = f.run(&["run", "out.wasm"]);
    assert_eq!(artifact.status.code(), Some(0));
    assert_eq!(stdout(&artifact), "Result: i32(42)\n");
    assert!(artifact.stderr.is_empty(), "{}", stderr(&artifact));
}

#[test]
fn option_spelling_is_silent_on_standalone_source_commands() {
    let f = Fixture::new();
    f.write("legacy.mb", LEGACY);
    for command in ["analyze", "ownership"] {
        let output = f.run(&[command, "legacy.mb"]);
        assert_eq!(
            output.status.code(),
            Some(0),
            "{command}: {}",
            stderr(&output)
        );
        assert!(!stderr(&output).contains("warning"), "{command}");
    }
}

#[test]
fn bytes_warning_proves_the_channel_is_non_failing_and_prints_before_run_output() {
    let f = Fixture::new();
    f.project("fn main() -> i32 { let b: Bytes<2> = [1, 2]; 42 }\n");
    for args in [&["check"][..], &["run"][..]] {
        let output = f.run(args);
        assert_eq!(
            output.status.code(),
            Some(0),
            "{args:?}: {}",
            stderr(&output)
        );
        let text = stderr(&output);
        assert!(text.starts_with("warning[MW003]"), "{args:?}: {text}");
    }
    assert_eq!(stdout(&f.run(&["run"])), "Result: i32(42)\n");
}

#[test]
fn errors_still_fail_when_warnings_are_present() {
    let f = Fixture::new();
    f.project("fn pick(value: Bytes<2>) -> i32 { 1 }\nfn main() -> i32 { let flag: Bool = 3; 1 }\n");
    for args in [&["check"][..], &["build"][..], &["run"][..]] {
        let output = f.run(args);
        assert_eq!(output.status.code(), Some(1), "{args:?}");
        assert!(output.stdout.is_empty(), "{args:?}");
        let text = stderr(&output);
        let warning = text
            .find("warning[MW003]")
            .unwrap_or_else(|| panic!("{args:?}: {text}"));
        let error = text
            .find("error[TE002]")
            .unwrap_or_else(|| panic!("{args:?}: {text}"));
        assert!(
            warning < error,
            "warning is printed before the error: {text}"
        );
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
    assert!(text.contains("TE017") && !text.contains("warning"), "{text}");
}

#[test]
fn option_spelling_with_borrow_payloads_and_nesting_is_silent() {
    let f = Fixture::new();
    f.project(
        r#"
        fn read(value: borrow i32) -> i32 { value.copy() }
        type Box { slot: Option<i32> }
        fn main() -> i32 {
            var owner := 40;
            let wrapped: Option<borrow i32> = Some(owner.borrow());
            let inner: Option<Option<i32>> = None;
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
        "pub type Maybe = Option<u32>;\npub fn none() -> Maybe { None }\n",
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
        fn choose(flag: Bool) -> i32? { if flag { Some(40) } else { None } }
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
            "fn main() { let flag: Bool? = Some(1); }",
            "expected Bool, found",
        ),
        (
            "fn main() { let value := None; }",
            "cannot determine None's outcome type; provide an Option<T> annotation",
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
fn postfix_and_option_spellings_are_the_same_type() {
    let f = Fixture::new();
    f.project(
        "fn legacy(value: Option<i32>) -> i32? { value }\nfn main() -> i32 { let a: i32? = Some(42); let b: Option<i32> = a; match legacy(b) { Some(n) => n, None => 0 } }\n",
    );
    let output = f.run(&["run"]);
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    assert_eq!(stdout(&output), "Result: i32(42)\n");
    assert!(output.stderr.is_empty(), "{}", stderr(&output));
}
