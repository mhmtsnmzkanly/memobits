//! Source-level tests: `test fn`, `assert`, `mb test`, and `mb build --tests`.
use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new(modules: &[(&str, &str)]) -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-test-cmd-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            "[package]\nname='tested'\nentry='main::main'\n",
        )
        .unwrap();
        for (name, text) in modules {
            fs::write(path.join("src").join(format!("{name}.mb")), text).unwrap();
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

    fn path(&self, name: &str) -> String {
        self.0.join(name).to_str().unwrap().to_owned()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn stdout(output: &Output) -> String {
    String::from_utf8(output.stdout.clone()).unwrap()
}

fn stderr(output: &Output) -> String {
    String::from_utf8(output.stderr.clone()).unwrap()
}

const MAIN: &str = "fn main() -> i32 { 42 }\n";

const MIXED: &str = "\
fn main() -> i32 { 42 }
fn double(value: i32) -> i32 { value * 2 }
test fn passes() {
    assert(double(21) == 42);
}
test fn fails() {
    let value := double(2);
    assert(value == 5);
}
test fn also_passes() {
    assert(true);
}
";

#[test]
fn source_and_standalone_artifact_print_identical_reports() {
    let f = Fixture::new(&[("main", MIXED)]);
    let source = f.run(&["test"]);
    assert_eq!(source.status.code(), Some(1), "{source:?}");
    assert!(stderr(&source).is_empty(), "{}", stderr(&source));
    let report = stdout(&source);
    assert!(report.starts_with("running 3 tests\n"), "{report}");
    assert!(
        report.contains("test main::also_passes ... ok\n"),
        "{report}"
    );
    assert!(report.contains("test main::passes ... ok\n"), "{report}");
    assert!(report.contains("test main::fails ... FAILED\n"), "{report}");
    assert!(report.contains("    assertion failed\n"), "{report}");
    assert!(report.contains("src/main.mb:8:5"), "{report}");
    assert!(report.contains("assert(value == 5);"), "{report}");
    assert!(
        report.ends_with("test result: FAILED. 2 passed; 1 failed; 0 filtered out\n"),
        "{report}"
    );

    let artifact = f.path("tests.wasm");
    let build = f.run(&["build", "--tests", "--output", &artifact]);
    assert!(build.status.success(), "{build:?}");
    assert!(stdout(&build).contains("3 tests"), "{}", stdout(&build));
    let standalone = f.run(&["test", &artifact]);
    assert_eq!(standalone.status.code(), Some(1), "{standalone:?}");
    assert!(stderr(&standalone).is_empty());
    assert_eq!(stdout(&standalone), report);

    // The default output path and a filter after the artifact.
    let default = f.run(&["build", "--tests"]);
    assert!(default.status.success(), "{default:?}");
    assert!(f.0.join("target/memobits/tests.wasm").is_file());
    let filtered = f.run(&["test", &artifact, "passes"]);
    assert_eq!(filtered.status.code(), Some(0), "{filtered:?}");
    assert!(
        stdout(&filtered).contains("2 passed; 0 failed; 1 filtered out"),
        "{}",
        stdout(&filtered)
    );
}

#[test]
fn all_passing_tests_exit_zero_and_a_filter_selects_by_qualified_name() {
    let f = Fixture::new(&[("main", MIXED)]);
    let ok = f.run(&["test", "passes"]);
    assert_eq!(ok.status.code(), Some(0), "{ok:?}");
    assert_eq!(
        stdout(&ok),
        "running 2 tests\ntest main::also_passes ... ok\ntest main::passes ... ok\n\n\
         test result: ok. 2 passed; 0 failed; 1 filtered out\n"
    );
    let by_module = f.run(&["test", "main::fa"]);
    assert_eq!(by_module.status.code(), Some(1));
    assert!(stdout(&by_module).starts_with("running 1 test\n"));
    let none = f.run(&["test", "nothing-matches"]);
    assert_eq!(none.status.code(), Some(0));
    assert!(
        stdout(&none).contains("running 0 tests"),
        "{}",
        stdout(&none)
    );
    let two = f.run(&["test", "a", "b"]);
    assert_eq!(two.status.code(), Some(1));
    assert!(
        stderr(&two).contains("at most one FILTER"),
        "{}",
        stderr(&two)
    );
}

#[test]
fn a_project_without_tests_reports_zero_tests_and_succeeds() {
    let f = Fixture::new(&[("main", MAIN)]);
    let output = f.run(&["test"]);
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(
        stdout(&output),
        "running 0 tests\n\ntest result: ok. 0 passed; 0 failed; 0 filtered out\n"
    );
    assert!(stderr(&output).is_empty());
}

#[test]
fn tests_in_every_module_run_including_modules_main_does_not_import() {
    let f = Fixture::new(&[
        ("main", MAIN),
        (
            "extra",
            "fn hidden() -> bool { true }\ntest fn hidden_is_true() { assert(hidden()); }\n",
        ),
    ]);
    let output = f.run(&["test"]);
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert!(
        stdout(&output).contains("test extra::hidden_is_true ... ok"),
        "{}",
        stdout(&output)
    );
    // The normal artifact still does not load the unreachable module.
    let build = f.run(&["build"]);
    assert!(build.status.success(), "{build:?}");
}

#[test]
fn a_test_may_use_private_items_of_its_own_module() {
    let f = Fixture::new(&[
        (
            "main",
            "type Point { x: i32, y: i32 }\n\
             fn sum(point: borrow Point) -> i32 { point.x + point.y }\n\
             fn main() -> i32 { 42 }\n\
             test fn private_items() {\n    let point := Point { x: 1, y: 2 };\n    assert(sum(point.borrow()) == 3);\n}\n",
        ),
    ]);
    let output = f.run(&["test"]);
    assert_eq!(
        output.status.code(),
        Some(0),
        "{output:?}{}",
        stderr(&output)
    );
}

#[test]
fn a_test_cannot_reach_private_items_of_another_module() {
    let f = Fixture::new(&[
        (
            "main",
            "use helper;\nfn main() -> i32 { 42 }\ntest fn t() { assert(helper::secret()); }\n",
        ),
        ("helper", "fn secret() -> bool { true }\n"),
    ]);
    let output = f.run(&["test"]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("private"), "{}", stderr(&output));
}

#[test]
fn assert_in_ordinary_code_traps_with_its_location_in_source_and_wasm() {
    let f = Fixture::new(&[(
        "main",
        "fn main() -> i32 {\n    let value := 1;\n    assert(value == 2);\n    42\n}\n",
    )]);
    let source = f.run(&["run"]);
    assert_eq!(source.status.code(), Some(1), "{source:?}");
    let text = stderr(&source);
    assert!(text.contains("assertion failed"), "{text}");
    assert!(text.contains("src/main.mb:3:5"), "{text}");
    assert!(text.contains("assert(value == 2);"), "{text}");
    let artifact = f.path("app.wasm");
    assert!(f.run(&["build", "--output", &artifact]).status.success());
    let wasm = f.run(&["run", &artifact]);
    assert_eq!(stderr(&wasm), text);

    let passing = Fixture::new(&[("main", "fn main() -> i32 { assert(1 < 2); 42 }\n")]);
    let ok = passing.run(&["run"]);
    assert_eq!(stdout(&ok), "Result: i32(42)\n");
}

#[test]
fn a_user_function_or_import_named_assert_takes_precedence() {
    let local = Fixture::new(&[(
        "main",
        "fn assert(ok: bool) -> i32 { 7 }\nfn main() -> i32 { assert(1 == 2) }\n",
    )]);
    assert_eq!(stdout(&local.run(&["run"])), "Result: i32(7)\n");

    let imported = Fixture::new(&[
        (
            "main",
            "use check::assert;\nfn main() -> i32 { assert(false) }\n",
        ),
        ("check", "pub fn assert(ok: bool) -> i32 { 9 }\n"),
    ]);
    let output = imported.run(&["run"]);
    assert_eq!(stdout(&output), "Result: i32(9)\n", "{output:?}");

    // Inside a test the user's `assert` also wins, so this test does not trap.
    let in_test = Fixture::new(&[(
        "main",
        "fn assert(ok: bool) {}\nfn main() -> i32 { 42 }\ntest fn t() { assert(false); }\n",
    )]);
    assert_eq!(in_test.run(&["test"]).status.code(), Some(0));
}

#[test]
fn assert_argument_diagnostics() {
    let f = Fixture::new(&[(
        "main",
        "fn main() -> i32 { assert(1); assert(true, true); assert(); 42 }\n",
    )]);
    let output = f.run(&["check"]);
    assert_eq!(output.status.code(), Some(1));
    let text = stderr(&output);
    assert!(text.contains("expected bool, found i32"), "{text}");
    assert!(
        text.contains("assert() expects one argument, found 2"),
        "{text}"
    );
    assert!(
        text.contains("assert() expects one argument, found 0"),
        "{text}"
    );
}

#[test]
fn test_function_declaration_diagnostics() {
    let cases = [
        ("pub test fn t() {}", "cannot be `pub`"),
        ("test fn t(x: i32) {}", "cannot take parameters"),
        ("test fn t() -> i32 { 1 }", "must not return a value"),
        ("test fn t<T>() {}", "cannot have generic parameters"),
        (
            "fn helper() {}\ntest fn t() { helper(); }\nfn caller() { t(); }",
            "test functions cannot be called",
        ),
        ("test fn t() {}\nfn t() {}", "duplicate module binding 't'"),
    ];
    for (extra, message) in cases {
        let f = Fixture::new(&[("main", &format!("{MAIN}{extra}\n"))]);
        for args in [&["test"][..], &["check", "--tests"]] {
            let output = f.run(args);
            assert_eq!(output.status.code(), Some(1), "{extra}: {output:?}");
            assert!(
                stderr(&output).contains(message),
                "{extra}: {}",
                stderr(&output)
            );
            assert!(stdout(&output).is_empty(), "{extra}");
        }
    }
    // Declaration errors are syntax errors, so a normal run reports them too.
    let f = Fixture::new(&[("main", &format!("{MAIN}test fn t(x: i32) {{}}\n"))]);
    assert_eq!(f.run(&["run"]).status.code(), Some(1));
}

#[test]
fn check_and_test_fail_on_a_broken_test_but_build_and_run_ignore_tests() {
    let f = Fixture::new(&[(
        "main",
        &format!("{MAIN}test fn broken() {{\n    let x: bool = 1;\n}}\n"),
    )]);
    for args in [&["check"][..], &["test"], &["check", "--tests"]] {
        let output = f.run(args);
        assert_eq!(output.status.code(), Some(1), "{args:?}: {output:?}");
        assert!(
            stderr(&output).contains("expected bool, found i32"),
            "{args:?}: {}",
            stderr(&output)
        );
    }
    let build = f.run(&["build"]);
    assert_eq!(build.status.code(), Some(0), "{build:?}");
    let run = f.run(&["run"]);
    assert_eq!(stdout(&run), "Result: i32(42)\n", "{run:?}");
}

#[test]
fn check_covers_unreachable_modules_but_build_and_run_do_not() {
    let f = Fixture::new(&[("main", MAIN), ("orphan", "fn broken() -> bool { 1 }\n")]);
    let check = f.run(&["check"]);
    assert_eq!(check.status.code(), Some(1), "{check:?}");
    assert!(
        stderr(&check).contains("expected bool, found i32"),
        "{}",
        stderr(&check)
    );
    let build = f.run(&["build"]);
    assert_eq!(build.status.code(), Some(0), "{build:?}");
    let run = f.run(&["run"]);
    assert_eq!(stdout(&run), "Result: i32(42)\n", "{run:?}");
    let clean = Fixture::new(&[("main", MAIN), ("orphan", "fn fine() -> bool { true }\n")]);
    assert_eq!(clean.run(&["check"]).status.code(), Some(0));
}

#[test]
fn tests_are_excluded_from_normal_artifacts() {
    let plain = Fixture::new(&[("main", MAIN)]);
    let with_tests = Fixture::new(&[(
        "main",
        &format!("{MAIN}fn unused() -> i32 {{ 1 }}\ntest fn t() {{ assert(true); }}\n"),
    )]);
    let app = |f: &Fixture| {
        let out = f.run(&["build"]);
        assert!(out.status.success(), "{out:?}");
        assert!(stdout(&out).contains("1 export(s)"), "{}", stdout(&out));
        fs::read(f.0.join("target/memobits/app.wasm")).unwrap()
    };
    let with = app(&with_tests);
    let without_unused = {
        let f = Fixture::new(&[("main", &format!("{MAIN}fn unused() -> i32 {{ 1 }}\n"))]);
        app(&f)
    };
    assert_eq!(
        with, without_unused,
        "a test must not change the app artifact"
    );
    assert!(!app(&plain).is_empty());
    let exports = memobits_runtime::exported_functions(&with).unwrap();
    assert!(
        exports.iter().all(|name| !name.starts_with("test::")),
        "{exports:?}"
    );

    // A library build exports only the manifest exports.
    let library = Fixture::new(&[(
        "lib",
        "pub fn one() -> i32 { 1 }\ntest fn t() { assert(one() == 1); }\n",
    )]);
    fs::write(
        library.0.join("project.toml"),
        "[package]\nname='lib'\n[export]\none='lib::one'\n",
    )
    .unwrap();
    let out = library.run(&["build", "--lib"]);
    assert!(out.status.success(), "{out:?}{}", stderr(&out));
    assert!(stdout(&out).contains("1 export(s)"));
    let bytes = fs::read(library.0.join("target/memobits/library.wasm")).unwrap();
    assert_eq!(
        memobits_runtime::exported_functions(&bytes).unwrap(),
        ["one"]
    );

    // The test artifact exports exactly the tests, by qualified name.
    let artifact = with_tests.path("tests.wasm");
    assert!(with_tests
        .run(&["build", "--tests", "--output", &artifact])
        .status
        .success());
    let bytes = fs::read(&artifact).unwrap();
    assert_eq!(
        memobits_runtime::exported_functions(&bytes)
            .unwrap()
            .into_iter()
            .filter(|name| name.starts_with("test::"))
            .collect::<Vec<_>>(),
        ["test::main::t"]
    );
}

#[test]
fn the_documented_example_artifact_is_unchanged_by_an_added_test() {
    let example = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/topics/basics");
    let copy =
        std::env::temp_dir().join(format!("memobits-test-cmd-basics-{}", std::process::id()));
    let _ = fs::remove_dir_all(&copy);
    fs::create_dir_all(copy.join("src")).unwrap();
    fs::copy(example.join("project.toml"), copy.join("project.toml")).unwrap();
    for entry in fs::read_dir(example.join("src")).unwrap() {
        let path = entry.unwrap().path();
        fs::copy(&path, copy.join("src").join(path.file_name().unwrap())).unwrap();
    }
    let mb = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_mb"))
            .current_dir(&copy)
            .args(args)
            .output()
            .unwrap()
    };
    assert!(mb(&["build", "--output", "before.wasm"]).status.success());
    let main = copy.join("src/main.mb");
    let mut text = fs::read_to_string(&main).unwrap();
    text.push_str("\ntest fn added_by_the_test() {\n    assert(1 + 1 == 2);\n}\n");
    fs::write(&main, text).unwrap();
    assert!(mb(&["build", "--output", "after.wasm"]).status.success());
    assert_eq!(
        fs::read(copy.join("before.wasm")).unwrap(),
        fs::read(copy.join("after.wasm")).unwrap()
    );
    let tested = mb(&["test"]);
    assert_eq!(tested.status.code(), Some(0), "{tested:?}");
    assert!(stdout(&tested).contains("added_by_the_test ... ok"));
    let _ = fs::remove_dir_all(&copy);
}

#[test]
fn heap_using_tests_run_repeatedly_in_fresh_instances() {
    let f = Fixture::new(&[(
        "main",
        "fn main() -> i32 { 42 }\n\
         test fn concat_one() {\n    let joined := \"é\".concat(\"!\");\n    assert(joined.len() == 3);\n}\n\
         test fn concat_many() {\n    var count := 0;\n    loop {\n        count += 1;\n        if count > 50 { break; }\n        let part := \"ab\".concat(\"cd\");\n        assert(part.len() == 4);\n    }\n}\n",
    )]);
    let first = f.run(&["test"]);
    assert_eq!(first.status.code(), Some(0), "{first:?}{}", stderr(&first));
    for _ in 0..3 {
        assert_eq!(stdout(&f.run(&["test"])), stdout(&first));
    }
    let artifact = f.path("heap.wasm");
    assert!(f
        .run(&["build", "--tests", "--output", &artifact])
        .status
        .success());
    for _ in 0..3 {
        assert_eq!(stdout(&f.run(&["test", &artifact])), stdout(&first));
    }
    assert!(
        stdout(&first).contains("2 passed; 0 failed"),
        "{}",
        stdout(&first)
    );
}

#[test]
fn a_test_that_exhausts_fuel_fails_without_stopping_the_others() {
    let f = Fixture::new(&[(
        "main",
        "fn main() -> i32 { 42 }\ntest fn spins() {\n    loop {}\n}\ntest fn fine() { assert(true); }\n",
    )]);
    let output = f.run(&["test", "--fuel", "100000"]);
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let report = stdout(&output);
    assert!(report.contains("test main::fine ... ok"), "{report}");
    assert!(report.contains("test main::spins ... FAILED"), "{report}");
    assert!(report.contains("fuel exhausted"), "{report}");
}

#[test]
fn help_and_usage_errors() {
    let f = Fixture::new(&[("main", MAIN)]);
    let help = f.run(&["test", "--help"]);
    assert!(help.status.success());
    assert!(stdout(&help).contains("mb test"));
    assert!(stdout(&help).contains("assert(condition)"));
    let bad = f.run(&["test", "--bogus"]);
    assert_eq!(bad.status.code(), Some(1));
    assert!(stderr(&bad).contains("unexpected test argument"));
    let both = f.run(&["build", "--tests", "--lib"]);
    assert_eq!(both.status.code(), Some(1));
    assert!(stderr(&both).contains("--tests cannot be combined with --lib"));
    let missing = f.run(&["test", "missing.wasm"]);
    assert_eq!(missing.status.code(), Some(1));
}
