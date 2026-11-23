//! `mb check` runs every build stage without writing an artifact.
use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new(source: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-check-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(
            path.join("project.toml"),
            "[package]\nname='checked'\nentry='main::main'\n",
        )
        .unwrap();
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(path.join("src/main.mb"), source).unwrap();
        Self(path)
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

fn failure(output: Output, code: &str, message: &str) {
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty());
    let text = String::from_utf8(output.stderr).unwrap();
    assert!(text.contains(code), "{text}");
    assert!(text.contains(message), "{text}");
}

#[test]
fn check_succeeds_without_writing_an_artifact() {
    let f = Fixture::new("fn main() -> Result<i32, Error> { Ok(1 + 2) }");
    let output = f.run(&["check"]);
    assert!(output.status.success(), "{output:?}");
    assert!(String::from_utf8(output.stdout)
        .unwrap()
        .starts_with("Check passed"));
    assert!(!f.0.join("target").exists());
    // build still writes the artifact it always did.
    assert!(f.run(&["build"]).status.success());
    assert!(f.0.join("target/memobits/app.wasm").exists());
}

#[test]
fn check_reports_type_errors_like_build() {
    let f = Fixture::new("fn main() -> Result<i32, Error> { let x: i32 = true; Ok(x) }");
    let output = f.run(&["check"]);
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let checked = String::from_utf8(output.stderr).unwrap();
    assert!(checked.contains("TE"), "{checked}");
    let built = f.run(&["build"]);
    assert_eq!(String::from_utf8(built.stderr).unwrap(), checked);
    assert!(!f.0.join("target").exists());
}

#[test]
fn check_reports_wasm_layout_gates_without_an_artifact() {
    let f = Fixture::new(r#"pub fn main() -> string { "é" }"#);
    failure(
        f.run(&["check"]),
        "LE900",
        "exported signatures cannot use String",
    );
    assert!(!f.0.join("target").exists());
}

#[test]
fn check_rejects_build_only_options() {
    let f = Fixture::new("fn main() -> Result<i32, Error> { Ok(1) }");
    failure(
        f.run(&["check", "--output", "x.wasm"]),
        "PE004",
        "unexpected argument",
    );
}
