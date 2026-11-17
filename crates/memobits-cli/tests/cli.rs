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
            "memobits-cli-{}-{}",
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
fn err(output: Output, code: &str) -> String {
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let text = String::from_utf8(output.stderr).unwrap();
    assert!(text.contains(code), "{text}");
    text
}

fn wasm_exports(bytes: &[u8]) -> Vec<String> {
    wasmparser::Validator::new().validate_all(bytes).unwrap();
    let mut names = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::ExportSection(exports) = payload.unwrap() {
            for export in exports {
                names.push(export.unwrap().name.to_owned());
            }
        }
    }
    names
}

#[test]
fn inventory_is_sorted_and_does_not_compile_sources() {
    let f = Fixture::new();
    f.write("project.toml", "[package]\nname='demo'\nversion='1.2'\nentry='main::run'\n[export]\nZed='z::Zed'\nAlpha='a::Alpha'\n");
    f.write("src/z.mb", "not valid source syntax");
    f.write("src/a/b.mb", "");
    f.write("src/ignored.txt", "");
    let output = f.run(&["project"]);
    assert!(output.status.success(), "{:?}", output);
    assert!(output.stderr.is_empty());
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("Package: demo\nVersion: 1.2\nEntry: main::run\n"));
    assert!(text.contains("Exports (2):\n  Alpha -> a::Alpha\n  Zed -> z::Zed\n"));
    assert!(text.contains(&format!(
        "Modules (2):\n  a::b -> {}\n  z -> z.mb\n",
        PathBuf::from("a").join("b.mb").display()
    )));
    assert_eq!(text.as_bytes(), f.run(&["project"]).stdout);
}

#[test]
fn override_uses_manifest_parent_for_sources() {
    let f = Fixture::new();
    f.write(
        "nested/custom.toml",
        "[package]\nname='override'\nentry='main::run'\nsrc='code'\n",
    );
    f.write("nested/code/main.mb", "");
    let output = f.run(&["project", "--project", "nested/custom.toml"]);
    assert!(output.status.success());
    assert!(String::from_utf8(output.stdout)
        .unwrap()
        .contains("Modules (1):\n  main -> main.mb\n"));
    let path = f.0.join("nested/custom.toml");
    assert!(f
        .run(&["project", "--project", path.to_str().unwrap()])
        .status
        .success());
}

#[test]
fn typed_project_failures_have_stable_codes() {
    let f = Fixture::new();
    err(f.run(&["project"]), "PE001");
    f.write("project.toml", "this is not TOML");
    err(f.run(&["project"]), "PE002");
    f.write("project.toml", "[package]\nname=''\nentry='main::run'\n");
    err(f.run(&["project"]), "PE003");
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='main::run'\n",
    );
    err(f.run(&["project"]), "PE001");
    f.write("src/not-valid.mb", "");
    err(f.run(&["project"]), "PE003");
}

#[test]
fn help_usage_and_unsupported_commands_are_truthful() {
    let f = Fixture::new();
    for args in [&["--help"][..], &["-h"], &["project", "--help"]] {
        let output = f.run(args);
        assert!(output.status.success());
        assert!(output.stderr.is_empty());
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(text.contains("Usage: mb project [--project PATH]"));
        assert!(text.contains("mb resolve [--project PATH] [--lib]"));
        assert!(text.contains("mb ownership-project [--project PATH] [--lib]"));
        assert!(text.contains("not supported yet"));
    }
    for args in [
        &[][..],
        &["unknown"],
        &["project", "--project"],
        &["project", "--project", "--help"],
        &["project", "extra"],
        &["project", "--project", "a", "--project", "b"],
        &["--help", "extra"],
        &["project", "--lib"],
        &["resolve", "--project"],
        &["resolve", "--lib", "--lib"],
        &["resolve", "--project", "a", "--project", "b"],
        &["build", "--output"],
        &["build", "--output", "a", "--output", "b"],
        &["build", "--lib", "--lib"],
        &["run", "app.wasm", "--entry"],
        &["run", "app.wasm", "--entry", "a", "--entry", "b"],
        &["run", "app.wasm", "--project", "project.toml"],
        &["run", "--project", "project.toml", "--entry", "main"],
    ] {
        err(f.run(args), "PE004");
    }
    assert!(err(f.run(&["check"]), "PE005").contains("unsupported"));
}

#[test]
fn build_writes_valid_application_and_library_wasm_exports() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='app::main'\n",
    );
    f.write("src/app.mb", "fn main() -> i32 { 42 }");
    let output = f.run(&["build", "--output", "app.wasm"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(wasm_exports(&fs::read(f.0.join("app.wasm")).unwrap()).contains(&"main".into()));
    let output = f.run(&["build"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(f.0.join("target/memobits/app.wasm").is_file());

    f.write(
        "library/project.toml",
        "[package]\nname='lib'\n[export]\nplus='math::add'\n",
    );
    f.write(
        "library/src/math.mb",
        "pub fn add(value: i32) -> i32 { value }",
    );
    let output = f.run(&[
        "build",
        "--lib",
        "--project",
        "library/project.toml",
        "--output",
        "library.wasm",
    ]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let names = wasm_exports(&fs::read(f.0.join("library.wasm")).unwrap());
    assert!(names.contains(&"plus".into()), "{names:?}");
    assert!(!names.contains(&"main".into()), "{names:?}");
}

#[test]
fn failed_build_preserves_existing_artifact_and_rejects_type_exports() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='app::main'\n",
    );
    f.write(
        "src/app.mb",
        "fn main() { let x := [1]; let y := x; let z := x; }",
    );
    f.write("previous.wasm", "previous artifact");
    let message = err(f.run(&["build", "--output", "previous.wasm"]), "BE001");
    assert!(message.contains("app.mb:1:"), "{message}");
    assert_eq!(
        fs::read(f.0.join("previous.wasm")).unwrap(),
        b"previous artifact"
    );

    f.write(
        "library/project.toml",
        "[package]\nname='lib'\n[export]\nNumber='math::Number'\n",
    );
    f.write("library/src/math.mb", "pub type Number = i32;");
    let message = err(
        f.run(&[
            "build",
            "--lib",
            "--project",
            "library/project.toml",
            "--output",
            "type.wasm",
        ]),
        "PE006",
    );
    assert!(
        message.contains("type export 'Number' is unsupported"),
        "{message}"
    );
    assert!(!f.0.join("type.wasm").exists());
}

#[test]
fn source_and_artifact_run_use_the_same_wasm_runtime() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='app::main'\n",
    );
    f.write("src/app.mb", "fn main() -> i32 { 42 }");
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(
        String::from_utf8(source.stdout).unwrap(),
        "Result: i32(42)\n"
    );

    let build = f.run(&["build", "--output", "app.wasm"]);
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let artifact = f.run(&["run", "app.wasm"]);
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(
        String::from_utf8(artifact.stdout).unwrap(),
        "Result: i32(42)\n"
    );
    let bare = Fixture::new();
    fs::copy(f.0.join("app.wasm"), bare.0.join("app.wasm")).unwrap();
    let without_project = bare.run(&["run", "app.wasm"]);
    assert!(
        without_project.status.success(),
        "{}",
        String::from_utf8_lossy(&without_project.stderr)
    );
    assert_eq!(
        String::from_utf8(without_project.stdout).unwrap(),
        "Result: i32(42)\n"
    );

    f.write("src/app.mb", "fn main() {}");
    let unit_source = f.run(&["run"]);
    assert!(unit_source.status.success());
    assert_eq!(
        String::from_utf8(unit_source.stdout).unwrap(),
        "Result: Unit\n"
    );
    let unit_build = f.run(&["build", "--output", "unit.wasm"]);
    assert!(unit_build.status.success());
    let unit_artifact = f.run(&["run", "unit.wasm"]);
    assert!(unit_artifact.status.success());
    assert_eq!(
        String::from_utf8(unit_artifact.stdout).unwrap(),
        "Result: Unit\n"
    );
}

#[test]
fn run_reports_runtime_and_compile_failures_with_nonzero_status() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='app::main'\n",
    );
    f.write(
        "src/app.mb",
        "fn main() -> i32 { let value := 2147483647; value + 1 }",
    );
    let output = f.run(&["run"]);
    assert_eq!(output.status.code(), Some(1));
    let message = String::from_utf8(output.stderr).unwrap();
    assert!(message.contains("RE007"), "{message}");
    assert!(
        message.contains("integer overflow in addition"),
        "{message}"
    );
    assert!(message.contains("app.mb:1:"), "{message}");

    f.write("bad.wasm", "not a wasm module");
    assert!(err(f.run(&["run", "bad.wasm"]), "RE001").contains("invalid WebAssembly"));
    let build = f.run(&["build", "--output", "app.wasm"]);
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    assert!(
        err(f.run(&["run", "app.wasm", "--entry", "missing"]), "RE004")
            .contains("missing function export")
    );

    f.write(
        "src/app.mb",
        "fn main() { let value := [1]; let moved := value; let again := value; }",
    );
    let message = err(f.run(&["run"]), "BE001");
    assert!(message.contains("app.mb:1:"), "{message}");

    f.write("src/app.mb", "fn main(value: i32) -> i32 { value }");
    assert!(err(f.run(&["run"]), "RE005").contains("takes 1 parameter"));
}

#[test]
fn ownership_project_checks_resolved_roots_and_imported_moves() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='main::main'\n[export]\nconsume='api::consume'\n",
    );
    f.write("src/api.mb", "pub fn consume(value: Array<i32, 1>) {}");
    f.write(
        "src/main.mb",
        "use api::consume; fn main() { let value := [1]; consume(value); consume(value); }",
    );
    let message = err(f.run(&["ownership-project"]), "BE001");
    assert!(message.contains("main.mb:1:"), "{message}");
    assert!(message.contains("value"));

    // Library mode follows exports and must not load the application's entry.
    f.write("src/main.mb", "not valid source syntax");
    let output = f.run(&["ownership-project", "--lib"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("library exports"));
    assert!(text.contains("supported primitive moves and loans checked"));
    assert!(text.contains("borrow safety not guaranteed"));
}

#[test]
fn ownership_project_accepts_supported_imported_calls() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='main::main'\n[export]\nadd='math::add'\n[prelude]\nother_add='math::add'\n",
    );
    f.write("src/math.mb", "pub fn add(a: i32, b: i32) -> i32 { a + b }");
    f.write(
        "src/main.mb",
        "use self::math::add as math_add; fn main() -> i32 { math_add(1, 2) + other_add(3, 4) + self::math::add(5, 6) }",
    );
    let output = f.run(&["ownership-project"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    f.write(
        "src/main.mb",
        "use absent::consume; fn main() { consume(1); }",
    );
    assert!(err(f.run(&["ownership-project"]), "ME003").contains("unavailable"));
}

#[test]
fn resolve_uses_target_roots_and_ignores_unreachable_sources() {
    let f = Fixture::new();
    f.write(
        "nested/project.toml",
        "[package]\nname='demo'\nentry='main::main'\n[export]\nadd='math::add'\n",
    );
    f.write(
        "nested/src/main.mb",
        "use self::math::add; fn main() -> i32 { add(1, 2) }",
    );
    f.write(
        "nested/src/math.mb",
        "pub fn add(a: i32, b: i32) -> i32 { a + b }",
    );
    f.write("nested/src/unreachable.mb", "not valid source syntax");
    let app = f.run(&["resolve", "--project", "nested/project.toml"]);
    assert!(app.status.success(), "{:?}", app);
    assert!(app.stderr.is_empty());
    let text = String::from_utf8(app.stdout).unwrap();
    assert!(
        text.contains("Resolved application entry: 2 reachable module(s)"),
        "{text}"
    );
    assert!(text.contains("names checked; further semantics, types, and ownership not checked"));
    assert!(text.contains("  main -> main.mb\n  math -> math.mb\n"));
    assert!(!text.contains("unreachable"));
    let lib = f.run(&["resolve", "--lib", "--project", "nested/project.toml"]);
    assert!(lib.status.success(), "{:?}", lib);
    let text = String::from_utf8(lib.stdout).unwrap();
    assert!(text.contains("Resolved library exports: 1 reachable module(s)"));
    assert!(text.contains("  math -> math.mb\n"));
    assert!(!text.contains("  main ->"));
}

#[test]
fn resolve_renders_source_diagnostics_and_root_errors() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='main::main'\n[export]\nadd='math::add'\n",
    );
    f.write("src/main.mb", "fn main() { unknown_name; }");
    f.write("src/math.mb", "fn add() {}");
    let message = err(f.run(&["resolve"]), "NE001");
    assert!(message.contains("main.mb:1:"), "{message}");
    assert!(message.contains("unknown_name"));
    let message = err(f.run(&["resolve", "--lib"]), "ME007");
    assert!(message.contains("private"));
    f.write("src/main.mb", "fn main() { let x = 1; }");
    let message = err(f.run(&["resolve"]), "SE002");
    assert!(message.contains("main.mb:1:"), "{message}");
    f.write(
        "project.toml",
        "[package]\nname='demo'\n[export]\nadd='math::add'\n",
    );
    err(f.run(&["resolve"]), "ME001");
}

#[test]
fn syntax_reports_source_diagnostics_without_claiming_semantic_validation() {
    let f = Fixture::new();
    f.write("valid.mb", "fn main() -> i32 { unknown_name }");
    let output = f.run(&["syntax", "valid.mb"]);
    assert!(output.status.success());
    assert!(String::from_utf8(output.stdout)
        .unwrap()
        .contains("semantics not checked"));
    f.write("broken.mb", "fn main() { let x = 1; }");
    let message = err(f.run(&["syntax", "broken.mb"]), "SE002");
    assert!(message.contains("broken.mb:1:"));
    assert!(message.contains("let x = 1"));
    err(f.run(&["syntax"]), "PE004");
    err(f.run(&["syntax", "missing.mb"]), "PE001");
    err(f.run(&["syntax", "valid.mb", "extra.mb"]), "PE004");
}

#[test]
fn standalone_analysis_checks_types_and_loop_control() {
    let f = Fixture::new();
    f.write("valid.mb", "fn main() -> i32 { let value := 2; value + 3 }");
    let output = f.run(&["analyze", "valid.mb"]);
    assert!(output.status.success());
    assert!(String::from_utf8_lossy(&output.stdout).contains("ownership not checked"));
    f.write("invalid.mb", "fn main() { break; let value: Bool = 1; }");
    let output = f.run(&["analyze", "invalid.mb"]);
    let message = err(output, "TE020");
    assert!(message.contains("TE002"));
    assert!(message.contains("invalid.mb:1:"));
    f.write("syntax.mb", "fn main( {");
    let message = err(f.run(&["analyze", "syntax.mb"]), "SE002");
    assert!(!message.contains("TE"));
}

#[test]
fn standalone_ownership_checks_moves_and_renders_source_errors() {
    let f = Fixture::new();
    f.write(
        "moves.mb",
        "fn main() { let x := [1]; let y := x; let z := x; }",
    );
    let message = err(f.run(&["ownership", "moves.mb"]), "BE001");
    assert!(message.contains("moves.mb:1:"), "{message}");
    assert!(message.contains("x"));

    f.write("reads.mb", "fn main() { let x := 1; x + x; }");
    let output = f.run(&["ownership", "reads.mb"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("owned moves checked"));

    f.write(
        "reinit.mb",
        "fn g(a: i32, b: i32) {} fn main() { var x := 1; g(x, { x = 2; 0 }); x + 1; }",
    );
    let output = f.run(&["ownership", "reinit.mb"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    f.write("types.mb", "fn main() { let x: Bool = 1; }");
    assert!(err(f.run(&["ownership", "types.mb"]), "TE002").contains("types.mb:1:"));
    f.write("syntax.mb", "fn main( {");
    assert!(err(f.run(&["ownership", "syntax.mb"]), "SE002").contains("syntax.mb:1:"));
    for access in ["borrow", "share"] {
        f.write("access.mb", &format!("fn main(x: {access} i32) {{}}"));
        let output = f.run(&["ownership", "access.mb"]);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn project_analysis_checks_imported_call_types() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='test'\nentry='main::main'\n[export]\nadd='math::add'\n",
    );
    f.write("src/math.mb", "pub fn add(x: i32) -> i32 { x + 1 }");
    f.write("src/main.mb", "use math::add; fn main() -> i32 { add(2) }");
    assert!(f.run(&["analyze-project"]).status.success());
    assert!(f.run(&["analyze-project", "--lib"]).status.success());
    f.write(
        "src/main.mb",
        "use math::add; fn main() -> i32 { add(false) }",
    );
    let message = err(f.run(&["analyze-project"]), "TE002");
    assert!(message.contains("main.mb:1:"));
    assert!(f.run(&["analyze-project", "--lib"]).status.success());
}

#[test]
fn published_numeric_analysis_example_remains_valid() {
    let f = Fixture::new();
    f.write(
        "numeric.mb",
        include_str!("../../../examples/analysis/numeric.mb"),
    );
    let output = f.run(&["analyze", "numeric.mb"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn library_build_excludes_same_module_entry_and_unrelated_bodies() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='main::main'\n[export]\nanswer='main::answer'\n",
    );
    f.write("src/main.mb", "fn main() -> i32 { 99 } fn helper() -> i32 { 42 } fn unused() -> i32 { 7 } pub fn answer() -> i32 { helper() }");
    let output = f.run(&["build", "--lib", "--output", "library.wasm"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let bytes = fs::read(f.0.join("library.wasm")).unwrap();
    wasmparser::validate(&bytes).unwrap();
    let count = wasmparser::Parser::new(0)
        .parse_all(&bytes)
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::FunctionSection(section) => Some(section.count()),
            _ => None,
        })
        .unwrap();
    assert_eq!(count, 2);
    assert_eq!(wasm_exports(&bytes), vec!["answer".to_string()]);
}

#[test]
fn primitive_reference_checks_and_execution_work_in_cli() {
    let f = Fixture::new();
    f.write(
        "access.mb",
        "fn update(x: share i32) { x += 1; } fn main() { var x := 1; update(x.share()); x + 1; }",
    );
    let output = f.run(&["ownership", "access.mb"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    f.write(
        "conflict.mb",
        "fn main() { var x := 1; let r := x.borrow(); x = 2; r + 1; }",
    );
    assert!(err(f.run(&["ownership", "conflict.mb"]), "BE005").contains("conflict.mb:1:"));
    f.write(
        "project.toml",
        r#"[package]
name = "references"
entry = "main::main"
"#,
    );
    f.write(
        "src/main.mb",
        "fn update(x: share i32) { x += 1; } fn main() { var x := 1; update(x.share()); }",
    );
    let output = f.run(&["ownership-project"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = f.run(&["build"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(source.stdout, artifact.stdout);
}

#[test]
fn share_writes_are_visible_across_modules_in_source_and_artifact_runs() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        r#"[package]
name = "reference-result"
entry = "main::main"
"#,
    );
    f.write(
        "src/math.mb",
        "pub fn update(value: share i32) { value += 2; }",
    );
    f.write("src/main.mb", "use self::math::update; fn main() -> i32 { var value := 40; update(value.share()); value }");
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert!(String::from_utf8_lossy(&source.stdout).contains("42"));
    let built = f.run(&["build"]);
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(source.stdout, artifact.stdout);
}

#[test]
fn fixed_array_syntax_is_inspectable_and_read_only_arrays_are_executable() {
    let f = Fixture::new();
    f.write(
        "arrays.mb",
        "fn main() { let values: Array<i32, 3> = [1, 2, 3]; values[0]; }",
    );
    let parsed = f.run(&["syntax", "arrays.mb"]);
    assert!(
        parsed.status.success(),
        "{}",
        String::from_utf8_lossy(&parsed.stderr)
    );
    let analyzed = f.run(&["analyze", "arrays.mb"]);
    assert!(
        analyzed.status.success(),
        "{}",
        String::from_utf8_lossy(&analyzed.stderr)
    );
    let owned = f.run(&["ownership", "arrays.mb"]);
    assert!(
        owned.status.success(),
        "{}",
        String::from_utf8_lossy(&owned.stderr)
    );
    // Repetition executes; repeating an owned binding is a repeated move.
    f.write("repeat.mb", "fn main() { let values := [1; 3]; }");
    let repeated = f.run(&["ownership", "repeat.mb"]);
    assert!(
        repeated.status.success(),
        "{}",
        String::from_utf8_lossy(&repeated.stderr)
    );
    f.write(
        "moved.mb",
        "fn main() { let x := [1, 2]; let values := [x; 3]; }",
    );
    assert!(err(f.run(&["ownership", "moved.mb"]), "BE001").contains("'x'"));
    f.write("nested.mb", "fn main() { let values := [[1; 2]; 3]; }");
    assert!(f.run(&["ownership", "nested.mb"]).status.success());
    // Reference-typed elements stay gated.
    f.write(
        "refs.mb",
        "fn main() { var x := 1; let values := [x.borrow()]; }",
    );
    err(f.run(&["ownership", "refs.mb"]), "TE017");
}

fn run_both(f: &Fixture, source: &str) -> String {
    f.write("src/app.mb", source);
    let direct = f.run(&["run"]);
    assert!(
        direct.status.success(),
        "{}",
        String::from_utf8_lossy(&direct.stderr)
    );
    let built = f.run(&["build"]);
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(direct.stdout, artifact.stdout);
    String::from_utf8_lossy(&direct.stdout).into_owned()
}

#[test]
fn array_mutation_repetition_and_moves_run_from_source_and_artifact() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='arrays'\nentry='app::main'\n",
    );
    // The element expression runs once per slot, in order: elements are 1, 2, 3.
    let out = run_both(
        &f,
        "fn next(c: share i32) -> i32 { c += 1; c + 0 } fn main() -> i32 { var n := 0; let a := [next(n.share()); 3]; a[0] * 100 + a[1] * 10 + a[2] }",
    );
    assert!(out.contains("123"), "{out}");
    let out = run_both(
        &f,
        "fn main() -> i32 { var a := [0; 8]; var i := 0; loop { if i >= 8 { break; } a[i] = i * i; i += 1; } a[3] += 1; let b := a; b[3] + b[7] }",
    );
    assert!(out.contains("59"), "{out}");
    // Element writes trap out of range from both runs.
    f.write(
        "src/app.mb",
        "fn put(n: i32) -> i32 { var a := [1, 2]; a[n] = 3; a[0] + 0 } fn main() -> i32 { let n := 1; put(n + 1) }",
    );
    let source = f.run(&["run"]);
    assert_eq!(source.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&source.stderr).contains("RE007"));
    assert!(f.run(&["build"]).status.success());
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert_eq!(artifact.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&artifact.stderr).contains("RE007"));
    // Compile-time rejections.
    f.write(
        "src/app.mb",
        "fn main() -> i32 { let a := [1]; a[0] = 2; 0 }",
    );
    err(f.run(&["run"]), "TE004");
    f.write(
        "src/app.mb",
        "fn main() -> i32 { let a := [1, 2]; let b := a; a[0] + b[0] }",
    );
    err(f.run(&["run"]), "BE001");
    f.write(
        "src/app.mb",
        "fn main() -> i32 { var a := [1]; a[1] = 2; 0 }",
    );
    err(f.run(&["run"]), "TE008");
    f.write(
        "src/app.mb",
        "fn main() -> i32 { let a: Array<i64, 65537> = [0; 65537]; 0 }",
    );
    assert!(err(f.run(&["run"]), "LE900").contains("configured stack size"));
}

#[test]
fn array_programs_run_from_source_and_artifact_with_dynamic_bounds_traps() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='arrays'\nentry='app::main'\n",
    );
    f.write(
        "src/app.mb",
        "fn main() -> i32 { let a := [1, 2, 3]; a[0] + a[2] }",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert!(String::from_utf8_lossy(&source.stdout).contains('4'));
    let built = f.run(&["build"]);
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(source.stdout, artifact.stdout);

    // A dynamic out-of-range index traps from both source and artifact runs.
    f.write(
        "src/app.mb",
        "fn pick(n: i32) -> i32 { let a := [1, 2, 3]; a[n] + 0 } fn main() -> i32 { let n := 2; pick(n + 1) }",
    );
    let source = f.run(&["run"]);
    assert_eq!(source.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&source.stderr).contains("RE007"));
    let built = f.run(&["build"]);
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert_eq!(artifact.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&artifact.stderr).contains("RE007"));

    // Extracting an aggregate element into a binding is a compile-time error.
    f.write(
        "src/app.mb",
        "fn main() -> i32 { let a := [[1, 2], [3, 4]]; let x := a[1]; 0 }",
    );
    err(f.run(&["run"]), "TE022");
}

#[test]
fn fixed_array_types_are_checked_without_enabling_execution() {
    let f = Fixture::new();
    f.write(
        "arrays.mb",
        "fn main() { let values: Array<i8, 3> = [1, 2, 3]; let nested := [[1, 2], [3, 4]]; }",
    );
    let checked = f.run(&["analyze", "arrays.mb"]);
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stderr)
    );
    // Nested arrays are executable too.
    let owned = f.run(&["ownership", "arrays.mb"]);
    assert!(
        owned.status.success(),
        "{}",
        String::from_utf8_lossy(&owned.stderr)
    );
    f.write(
        "invalid.mb",
        "fn main() { let values: Array<i32, 3> = [1, 2]; }",
    );
    let invalid = f.run(&["analyze", "invalid.mb"]);
    assert!(!invalid.status.success());
    assert!(String::from_utf8_lossy(&invalid.stderr).contains("invalid.mb:1:"));
}

#[test]
fn array_parameters_run_from_source_and_artifact() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='arrays'\nentry='app::main'\n",
    );
    let sum = "fn sum(a: borrow Array<i32, 3>) -> i32 { var i := 0; var t := 0; loop { if i >= 3 { break; } t += a[i]; i += 1; } t } ";
    let fill = "fn fill(a: share Array<i32, 4>, v: i32) { var i := 0; loop { if i >= 4 { break; } a[i] = v + i; i += 1; } } ";
    // A borrow parameter called twice on the same array.
    let out = run_both(
        &f,
        &format!("{sum} fn main() -> i32 {{ let a := [1, 2, 3]; sum(a.borrow()) * 10 + sum(a.borrow()) }}"),
    );
    assert!(out.contains("66"), "{out}");
    // The caller observes writes made through a share parameter.
    let out = run_both(
        &f,
        &format!("{fill} fn main() -> i32 {{ var a := [0; 4]; fill(a.share(), 10); a[0] + a[3] }}"),
    );
    assert!(out.contains("23"), "{out}");
    // An owned parameter moves the source and the callee sees the contents.
    let out = run_both(
        &f,
        "fn f(a: Array<i32, 3>) -> i32 { a[0] + a[2] } fn main() -> i32 { let a := [1, 2, 3]; f(a) + f([10, 20, 30]) }",
    );
    assert!(out.contains("44"), "{out}");
    // Recursion with an array borrow parameter.
    let out = run_both(
        &f,
        "fn rec(a: borrow Array<i32, 3>, n: i32) -> i32 { let m := n + 0; var l := [m + 0, m * 2, m * 3]; if m + 0 == 0 { a[0] + 0 } else { let r := rec(a, m - 1); r + l[2] } } fn main() -> i32 { let a := [100, 2, 3]; rec(a.borrow(), 3) }",
    );
    assert!(out.contains("118"), "{out}");

    // A dynamic out-of-range index inside the callee traps in both runs.
    f.write(
        "src/app.mb",
        "fn get(a: borrow Array<i32, 3>, n: i32) -> i32 { a[n] + 0 } fn main() -> i32 { let a := [1, 2, 3]; let n := 2; get(a.borrow(), n + 1) }",
    );
    let source = f.run(&["run"]);
    assert_eq!(source.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&source.stderr).contains("RE007"));
    assert!(f.run(&["build"]).status.success());
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert_eq!(artifact.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&artifact.stderr).contains("RE007"));

    // Compile-time diagnostics.
    f.write(
        "src/app.mb",
        "fn get(a: borrow Array<i32, 3>) -> i32 { a[3] + 0 } fn main() -> i32 { 0 }",
    );
    err(f.run(&["run"]), "TE008");
    f.write(
        "src/app.mb",
        "fn get(a: borrow Array<i32, 3>) -> i32 { a[0] + 0 } fn main() -> i32 { let a := [1, 2]; get(a.borrow()) }",
    );
    err(f.run(&["run"]), "TE002");
    f.write(
        "src/app.mb",
        "fn own(a: Array<i32, 2>) -> i32 { a[0] + 0 } fn main() -> i32 { let a := [1, 2]; let r := own(a); a[0] + r }",
    );
    err(f.run(&["run"]), "BE001");
    f.write(
        "src/app.mb",
        "fn put(a: borrow Array<i32, 2>) { a[0] = 1; } fn main() -> i32 { 0 }",
    );
    err(f.run(&["run"]), "TE004");
    f.write(
        "src/app.mb",
        "fn two(a: share Array<i32, 2>, b: share Array<i32, 2>) {} fn main() -> i32 { var a := [1, 2]; two(a.share(), a.share()); 0 }",
    );
    err(f.run(&["run"]), "BE005");
}

#[test]
fn array_results_if_values_and_nested_arrays_run_from_source_and_artifact() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='arrays'\nentry='app::main'\n",
    );
    let sum = "fn sum(a: borrow Array<i32, 3>) -> i32 { var i := 0; var t := 0; loop { if i >= 3 { break; } t += a[i]; i += 1; } t } ";
    // A repetition-built result consumed by a borrow-taking sum and an owned call.
    let out = run_both(
        &f,
        &format!("{sum} fn make(v: i32) -> Array<i32, 3> {{ [v + 0; 3] }} fn own(a: Array<i32, 3>) -> i32 {{ a[0] + a[2] }} fn main() -> i32 {{ let a := make(4); sum(a.borrow()) * 100 + own(make(5)) }}"),
    );
    assert!(out.contains("1210"), "{out}");
    // An if-value chosen dynamically and recursion returning arrays.
    let out = run_both(
        &f,
        "fn pick(c: Bool) -> Array<i32, 2> { if c { [1, 2] } else { [3, 4] } } fn fib(n: i32) -> Array<i32, 2> { if n <= 0 { return [0, 1]; } let p := fib(n - 1); [p[1] + 0, p[0] + p[1]] } fn main() -> i32 { let a := pick(true); let b := pick(false); let c := fib(10); a[1] * 1000 + b[0] * 100 + c[0] }",
    );
    assert!(out.contains("2355"), "{out}");
    // A 3x3 matrix filled by nested loops, then traced and summed.
    let out = run_both(
        &f,
        "fn main() -> i32 { var m := [[0; 3]; 3]; var i := 0; loop { if i >= 3 { break; } var j := 0; loop { if j >= 3 { break; } m[i][j] = i * 3 + j; j += 1; } i += 1; } var tr := 0; var total := 0; var k := 0; loop { if k >= 3 { break; } tr += m[k][k]; var l := 0; loop { if l >= 3 { break; } total += m[k][l]; l += 1; } k += 1; } tr * 100 + total }",
    );
    assert!(out.contains("1236"), "{out}");
    // Rows by borrow/share and a whole-row replacement.
    let out = run_both(
        &f,
        &format!("{sum} fn zero(a: share Array<i32, 3>) {{ a[0] = 0; a[1] = 0; a[2] = 0; }} fn main() -> i32 {{ var m := [[1, 2, 3], [4, 5, 6]]; zero(m[0].share()); m[1] = [7, 8, 9]; sum(m[0].borrow()) * 100 + sum(m[1].borrow()) }}"),
    );
    assert!(out.contains("24"), "{out}");
    // Evaluation order of nested assignment: index, index, right-hand side.
    let out = run_both(
        &f,
        "fn d(log: share i32, k: i32) -> i32 { log = log * 10 + k; 0 } fn main() -> i32 { var log := 0; var m := [[0; 2]; 2]; m[d(log.share(), 1)][d(log.share(), 2)] = d(log.share(), 3); log }",
    );
    assert!(out.contains("123"), "{out}");

    // Either index of a nested read traps in both runs.
    for body in [
        "let m := [[1, 2], [3, 4]]; let i := 1; m[i + 1][0] + 0",
        "let m := [[1, 2], [3, 4]]; let i := 1; m[0][i + 1] + 0",
    ] {
        f.write("src/app.mb", &format!("fn main() -> i32 {{ {body} }}"));
        let source = f.run(&["run"]);
        assert_eq!(source.status.code(), Some(1));
        assert!(String::from_utf8_lossy(&source.stderr).contains("RE007"));
        assert!(f.run(&["build"]).status.success());
        let artifact = f.run(&["run", "target/memobits/app.wasm"]);
        assert_eq!(artifact.status.code(), Some(1));
        assert!(String::from_utf8_lossy(&artifact.stderr).contains("RE007"));
    }

    // Compile-time diagnostics.
    for (source, code) in [
        ("fn main() -> i32 { let m := [[1, 2], [3, 4]]; let r := m[0]; 0 }", "TE022"),
        ("fn main() -> i32 { let m := [[1, 2], [3, 4]]; m[0][2] + 0 }", "TE008"),
        ("fn main() -> i32 { let m := [[1, 2], [3, 4]]; m[2][0] + 0 }", "TE008"),
        ("fn main() -> i32 { var m := [[1, 2], [3, 4]]; let r := m.borrow(); m[0][0] = 1; r[0][0] + 0 }", "BE005"),
        ("fn make() -> Array<i32, 2> { [1, 2] } fn main() -> i32 { let a := make(); let b := a; a[0] + 0 }", "BE001"),
        ("fn make() -> Array<i32, 2> { [1, 2] } fn main() -> i32 { make()[0] + 0 }", "TE017"),
        ("fn main() -> Array<i32, 2> { [1, 2] }", "LE900"),
        ("fn main() -> i32 { let m: Array<Array<i32, 4000>, 4000> = [[0; 4000]; 4000]; 0 }", "LE900"),
    ] {
        f.write("src/app.mb", source);
        err(f.run(&["run"]), code);
    }
}

#[test]
fn primitive_copy_runs_from_source_and_artifact_and_is_checked() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='copies'\nentry='app::main'\n",
    );
    let out = run_both(
        &f,
        "fn mk(v: i32) -> Array<i32, 3> { [v.copy(), v.copy() + 1, v + 2] } \
         fn swap(a: share Array<i32, 3>, i: i32, j: i32) { let t := a[i].copy(); a[i] = a[j].copy(); a[j] = t; } \
         fn main() -> i32 { var a := mk(1); swap(a.share(), 0, 2); a[0] * 100 + a[1] * 10 + a[2] }",
    );
    assert!(out.contains("321"), "{out}");
    let out = run_both(
        &f,
        "fn pick(flags: borrow Array<Bool, 2>, i: i32) -> Bool { flags[i].copy() } \
         fn main() -> i32 { let flags := [false, true]; let on := pick(flags.borrow(), 1); if on { 7 } else { 0 } }",
    );
    assert!(out.contains('7'), "{out}");
    // Compile-time rejections.
    for (source, code) in [
        (
            "fn main() -> i32 { let a := [1, 2]; let b := a.copy(); 0 }",
            "TE017",
        ),
        (
            "fn main() -> i32 { let a := [1, 2]; let b := a; a[0] + b[0] }",
            "BE001",
        ),
        (
            "fn main() -> i32 { let a := [[1, 2], [3, 4]]; let x := a[1]; 0 }",
            "TE022",
        ),
    ] {
        f.write("src/app.mb", source);
        err(f.run(&["run"]), code);
    }
}

#[test]
fn implicit_primitive_copies_run_from_source_and_artifact() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='implicit'\nentry='app::main'\n",
    );
    let out = run_both(
        &f,
        "type P { x: i32, y: i32 } \
         fn bump(n: i32) -> i32 { n + 1 } \
         fn mk(v: i32) -> Array<i32, 3> { [v, v + 1, v + 2] } \
         fn get(r: borrow i32) -> i32 { r } \
         fn swap(a: share Array<i32, 3>) { let t := a[0]; a[0] = a[2]; a[2] = t; } \
         fn main() -> i32 { \
           let x := 4; let y := x; \
           var i := 0; var acc := 0; loop { if i >= 3 { break; } acc += bump(i); i += 1; } \
           var a := mk(1); swap(a.share()); \
           let rep := [x; 3]; let p := P { x: 5, y: 6 }; let flags := [false, true]; let on := flags[1]; \
           let g := get(x.borrow()); \
           if on { x + y + acc + a[0] * 100 + rep[2] + bump(p.x) + g } else { 0 } }",
    );
    // 4 + 4 + 6 + 300 + 4 + 6 + 4
    assert!(out.contains("328"), "{out}");
    // Implicit copies are reads: a live share still conflicts.
    f.write(
        "src/app.mb",
        "fn main() -> i32 { var x := 1; var s := x.share(); let y := x; s += 1; y }",
    );
    err(f.run(&["run"]), "BE005");
}

#[test]
fn array_parameters_cross_modules_and_stay_out_of_exported_signatures() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='arrays'\nentry='main::main'\n",
    );
    f.write(
        "src/vec.mb",
        "pub fn total(a: borrow Array<i32, 3>) -> i32 { var i := 0; var t := 0; loop { if i >= 3 { break; } t += a[i]; i += 1; } t }\n\
         pub fn scale(a: share Array<i32, 3>, k: i32) { var i := 0; loop { if i >= 3 { break; } a[i] *= k; i += 1; } }\n\
         pub fn first(a: Array<i32, 3>) -> i32 { a[0] + 0 }\n",
    );
    f.write(
        "src/main.mb",
        "use vec::total; use vec::scale; use vec::first;\n\
         fn main() -> i32 { var a := [1, 2, 3]; scale(a.share(), 10); let t := total(a.borrow()); t + first(a) }\n",
    );
    assert!(f.run(&["analyze-project"]).status.success());
    assert!(f.run(&["ownership-project"]).status.success());
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert!(String::from_utf8_lossy(&source.stdout).contains("70"));
    assert!(f.run(&["build"]).status.success());
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert_eq!(source.stdout, artifact.stdout);

    // Mismatched array types across a module boundary are type errors.
    f.write(
        "src/main.mb",
        "use vec::total; fn main() -> i32 { let a := [1, 2]; total(a.borrow()) }",
    );
    err(f.run(&["run"]), "TE002");

    // Arrays and array references are rejected in exported signatures.
    f.write("src/main.mb", "fn main() -> i32 { 0 }\n");
    f.write(
        "project.toml",
        "[package]\nname='arrays'\nentry='main::main'\n[export]\ntotal='vec::total'\nfirst='vec::first'\n",
    );
    let message = err(f.run(&["build", "--lib"]), "LE900");
    assert!(message.contains("arrays or array references"), "{message}");
    f.write(
        "project.toml",
        "[package]\nname='arrays'\nentry='main::main'\n[export]\nfirst='vec::first'\n",
    );
    err(f.run(&["build", "--lib"]), "LE900");
    f.write("src/main.mb", "fn main(a: Array<i32, 2>) -> i32 { 0 }\n");
    err(f.run(&["run"]), "LE900");
}

#[test]
fn structs_run_from_source_and_artifact() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='structs'\nentry='app::main'\n",
    );
    let out = run_both(
        &f,
        "type P { x: i32, y: i32 } fn main() -> i32 { let p := P { x: 3, y: 4 }; p.x * p.y }",
    );
    assert!(out.contains("Result: i32(12)"), "{out}");
    // Mixed widths: every field reads back, `.copy()` yields an owned value.
    let out = run_both(
        &f,
        "type M { a: u8, b: i64, c: Bool, d: f32, e: i16 } \
         fn main() -> i64 { let m := M { e: -7, a: 200, d: 1.5, c: true, b: 5000000000 }; \
             let b := m.b.copy(); if m.c { b + 1 } else { 0 } }",
    );
    assert!(out.contains("5000000001"), "{out}");
    // Initialisers run in source order, not declaration order.
    let out = run_both(
        &f,
        "type P { a: i32, b: i32, c: i32 } \
         fn next(c: share i32) -> i32 { c += 1; c.copy() } \
         fn main() -> i32 { var n := 0; \
             let p := P { c: next(n.share()), a: next(n.share()), b: next(n.share()) }; \
             p.a * 100 + p.b * 10 + p.c }",
    );
    assert!(out.contains("Result: i32(231)"), "{out}");
    // Bool field as a condition; alias to a struct; a parenthesised literal.
    let out = run_both(
        &f,
        "type Flags { on: Bool, n: i32 } type F = Flags; \
         fn main() -> i32 { let f: F = F { n: 9, on: true }; if f.on { f.n + 1 } else { 0 } }",
    );
    assert!(out.contains("Result: i32(10)"), "{out}");
}

#[test]
fn struct_diagnostics_are_rendered_with_stable_codes() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='structs'\nentry='app::main'\n",
    );
    let head = "type P { x: i32, y: i32 } ";
    for (body, code, text) in [
        (
            "let p := P { x: 1 }; 0",
            "TE023",
            "missing field(s) in 'P' literal: y",
        ),
        (
            "let p := P { x: 1, y: 2, z: 3 }; 0",
            "TE023",
            "has no field 'z'",
        ),
        (
            "let p := P { x: 1, x: 2, y: 3 }; 0",
            "TE023",
            "more than once",
        ),
        (
            "let p := P { x: 1, y: true }; 0",
            "TE002",
            "expected i32, found Bool",
        ),
        ("let p := Q { x: 1 }; 0", "NE003", "unknown type 'Q'"),
        ("let n := 1; n.x + 1", "TE024", "requires a struct value"),
        (
            "let p := P { x: 1, y: 2 }; p.z + 1",
            "TE024",
            "has no field 'z'",
        ),
        ("let p := P { x: 1, y: 2 }; p.x = 3; 0", "TE004", ""),
        (
            "if 1 == P { x: 1, y: 2 } { 1 } else { 2 }",
            "SE002",
            "wrap it in parentheses",
        ),
        (
            "let P { x, y: Q { z } } := P { x: 1, y: 2 }; 0",
            "SE002",
            "nested destructuring",
        ),
    ] {
        f.write(
            "src/app.mb",
            &format!("{head} fn main() -> i32 {{ {body} }}"),
        );
        let message = err(f.run(&["run"]), code);
        assert!(message.contains(text), "{body}: {message}");
        assert!(message.contains("app.mb:1:"), "{message}");
    }
    for (source, code, text) in [
        (
            "type A { a: A } fn main() -> i32 { 0 }",
            "TE026",
            "recursive struct",
        ),
        (
            "type A = B; type B = A; fn main() -> i32 { 0 }",
            "TE026",
            "alias cycle",
        ),
        (
            "type A { xs: Array<A, 2> } fn main() -> i32 { 0 }",
            "TE026",
            "recursive struct",
        ),
        (
            "type E [ A, B ] fn main() -> i32 { let e: E = 1; 0 }",
            "TE002",
            "E",
        ),
    ] {
        f.write("src/app.mb", source);
        let message = err(f.run(&["run"]), code);
        assert!(message.contains(text), "{source}: {message}");
    }
    // Library exports with struct signatures are rejected too.
    f.write(
        "project.toml",
        "[package]\nname='structs'\nentry='app::main'\n[export]\nf='app::f'\n",
    );
    f.write(
        "src/app.mb",
        "pub type P { pub x: i32 } pub fn f(p: P) -> i32 { 0 } fn main() -> i32 { 0 }",
    );
    err(f.run(&["build", "--lib"]), "LE900");
}

#[test]
fn structs_cross_module_boundaries_by_visibility() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='structs'\nentry='main::main'\n",
    );
    f.write(
        "src/geom.mb",
        "pub type Point { pub x: i32, pub y: i32 }\n\
         pub type Account { pub id: i32, balance: i32 }\n\
         pub type Meters = Point;\n\
         pub fn opening() -> i32 { let a := Account { id: 1, balance: 40 }; a.balance + a.id }\n",
    );
    f.write(
        "src/main.mb",
        "use geom::Point; use geom::Meters; use geom::opening;\n\
         fn main() -> i32 { let p := Point { y: 4, x: 3 }; let m := geom::Point { x: 5, y: 6 }; \
             let q := Meters { x: 7, y: 8 }; p.x * p.y + m.x + q.y + opening() }\n",
    );
    assert!(f.run(&["analyze-project"]).status.success());
    assert!(f.run(&["ownership-project"]).status.success());
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert!(String::from_utf8_lossy(&source.stdout).contains("Result: i32(66)"));
    assert!(f.run(&["build"]).status.success());
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert_eq!(source.stdout, artifact.stdout);

    // A struct with a private field cannot be built from another module, and
    // its private field is not readable there either.
    f.write(
        "src/main.mb",
        "use geom::Account;\n\
         fn main() -> i32 { let a := Account { id: 1, balance: 2 }; a.balance + 0 }\n",
    );
    let message = err(f.run(&["run"]), "TE025");
    assert!(
        message.contains("cannot construct struct 'Account' outside module 'geom'"),
        "{message}"
    );
    assert!(
        message.contains("field 'balance' of struct 'Account' is private to module 'geom'"),
        "{message}"
    );

    // A private type cannot be named from another module, an unknown one is a name error.
    f.write("src/geom.mb", "type Hidden { x: i32 } pub fn f() {}\n");
    f.write(
        "src/main.mb",
        "fn main() -> i32 { let h := geom::Hidden { x: 1 }; 0 }\n",
    );
    err(f.run(&["run"]), "ME007");
    f.write(
        "src/main.mb",
        "fn main() -> i32 { let h := Nope { x: 1 }; 0 }\n",
    );
    err(f.run(&["run"]), "NE003");
}

fn stack_project(f: &Fixture, build: &str, source: &str) {
    f.write(
        "project.toml",
        &format!("[package]\nname='demo'\nentry='app::main'\n{build}"),
    );
    f.write("src/app.mb", source);
}

#[test]
fn build_stack_size_controls_frame_limits() {
    let f = Fixture::new();
    let big = "pub fn main() -> i32 { let a: Array<i32, 524288> = [1; 524288]; a[524287] }";
    stack_project(&f, "", big);
    let text = err(f.run(&["run"]), "LE900");
    assert!(
        text.contains("1048576") && text.contains("[build].stack_size"),
        "{text}"
    );
    stack_project(&f, "[build]\nstack_size = 4194304\n", big);
    let out = f.run(&["build"]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let grid = "pub fn main() -> i32 { var g: Array<Array<i32, 100>, 100> = [[0; 100]; 100]; g[99][99] = 4; g[99][99] }";
    stack_project(&f, "", grid);
    assert!(f.run(&["build"]).status.success());
}

#[test]
fn stack_exhaustion_is_a_distinct_runtime_error() {
    let f = Fixture::new();
    let source = "fn rec(n: i32) -> i32 { let a: Array<i32, 1024> = [n; 1024]; \
        if n == 0 { 0 } else { rec(n - 1) + a[1023] } } \
        pub fn main() -> i32 { rec(100000) }";
    stack_project(&f, "[build]\nstack_size = 65536\n", source);
    let text = err(f.run(&["run"]), "RE008");
    assert!(text.contains("stack overflow"), "{text}");
    // A subsequent run of shallower work is unaffected.
    stack_project(
        &f,
        "[build]\nstack_size = 65536\n",
        &source.replace("rec(100000)", "rec(3)"),
    );
    let out = f.run(&["run"]);
    assert!(
        String::from_utf8_lossy(&out.stdout).contains("Result: i32(6)"),
        "{out:?}"
    );
}

#[test]
fn invalid_build_settings_have_stable_codes() {
    let f = Fixture::new();
    for value in ["0", "-16", "100", "4100", "999999999999"] {
        stack_project(
            &f,
            &format!("[build]\nstack_size = {value}\n"),
            "pub fn main() {}",
        );
        err(f.run(&["project"]), "PE007");
    }
    stack_project(&f, "[build]\nstack_size = 'big'\n", "pub fn main() {}");
    err(f.run(&["project"]), "PE002");
    stack_project(&f, "[build]\nstack = 4096\n", "pub fn main() {}");
    err(f.run(&["project"]), "PE002");
}

#[test]
fn run_fuel_options_control_the_execution_budget() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='app::main'\n",
    );
    f.write(
        "src/app.mb",
        "fn main() -> i32 { var i := 0; var s := 0; loop { if i == 100000 { break; } s = s + 1; i += 1; } s }",
    );
    let default = f.run(&["run"]);
    assert!(default.status.success(), "{default:?}");
    assert_eq!(
        String::from_utf8(default.stdout).unwrap(),
        "Result: i32(100000)\n"
    );
    let build = f.run(&["build", "--output", "app.wasm"]);
    assert!(build.status.success(), "{build:?}");
    assert_eq!(
        String::from_utf8(f.run(&["run", "app.wasm"]).stdout).unwrap(),
        "Result: i32(100000)\n"
    );

    for args in [
        &["run", "--fuel", "1000"][..],
        &["run", "app.wasm", "--fuel", "1000"],
    ] {
        let text = err(f.run(args), "RE006");
        assert!(text.contains("--fuel"), "{text}");
    }
    for args in [
        &["run", "--fuel", "100000000"][..],
        &["run", "--no-fuel-limit"],
        &["run", "app.wasm", "--fuel", "100000000"],
        &["run", "app.wasm", "--no-fuel-limit"],
    ] {
        let out = f.run(args);
        assert_eq!(
            String::from_utf8(out.stdout).unwrap(),
            "Result: i32(100000)\n",
            "{args:?}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }

    for args in [
        &["run", "--fuel"][..],
        &["run", "--fuel", "0"],
        &["run", "--fuel", "-5"],
        &["run", "--fuel", "1.5"],
        &["run", "--fuel", "abc"],
        &["run", "--fuel", "1", "--fuel", "2"],
        &["run", "--fuel", "1", "--no-fuel-limit"],
        &["run", "--no-fuel-limit", "--no-fuel-limit"],
        &["run", "app.wasm", "--fuel", "0"],
        &["run", "app.wasm", "--fuel"],
        &["run", "app.wasm", "--no-fuel-limit", "--fuel", "5"],
    ] {
        err(f.run(args), "PE004");
    }
}

#[test]
fn deep_recursion_with_frame_arrays_reports_stack_overflow_not_fuel() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='app::main'\n",
    );
    f.write(
        "src/app.mb",
        "fn r(n: i32) -> i32 { let a := [n; 1000]; if n == 0 { 0 } else { r(n - 1) + a[0] } } \
         fn main() -> i32 { r(100000) }",
    );
    let text = err(f.run(&["run"]), "RE008");
    assert!(!text.contains("RE006"), "{text}");
    assert!(text.contains("stack overflow"), "{text}");
}
