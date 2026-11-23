//! D2 reconciliation tests for tuple clauses that had no dedicated evidence:
//! label/ordinal storage identity, written-order labeled initialization,
//! missing-label rejection and tuple exported-signature rejection.

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
            "memobits-d2-tuple-{}-{}",
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

    fn project(&self, source: &str, extra: &str) {
        self.write(
            "project.toml",
            &format!("[package]\nname='d2-tuple'\nentry='main::main'\n{extra}"),
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

    /// Run from source and from a standalone artifact; both must agree.
    fn source_and_wasm(&self, expected: &str) {
        let source = self.run(&["run"]);
        assert!(
            source.status.success(),
            "source failed: {}",
            String::from_utf8_lossy(&source.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&source.stdout), expected);
        let build = self.run(&["build", "--output", "out.wasm"]);
        assert!(
            build.status.success(),
            "build failed: {}",
            String::from_utf8_lossy(&build.stderr)
        );
        let wasm = self.run(&["run", "out.wasm"]);
        assert!(
            wasm.status.success(),
            "Wasm run failed: {}",
            String::from_utf8_lossy(&wasm.stderr)
        );
        assert_eq!(wasm.stdout, source.stdout);
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn tuple_label_and_ordinal_address_the_same_storage_in_source_and_wasm() {
    let f = Fixture::new();
    f.project(
        r#"
        fn main() -> i32 {
            var pair := (left: 1, right: 2);
            let before := pair.left + pair.1;
            pair.0 = 30;
            pair.right = 12;
            before * 100 + pair.left + pair.1
        }
        "#,
        "",
    );
    // before = 1 + 2 = 3; after writes through ordinal 0 and label `right`,
    // reading back through label `left` and ordinal 1: 30 + 12 = 42.
    f.source_and_wasm("Result: i32(342)\n");
}

#[test]
fn labeled_tuple_initializers_evaluate_in_written_order_in_source_and_wasm() {
    let f = Fixture::new();
    f.project(
        r#"
        fn take(pair: (left: i32, right: i32)) -> i32 {
            pair.left * 10 + pair.right
        }
        fn main() -> i32 {
            var order: i32 = 0;
            let result := take((right: { order += 1; order }, left: { order += 1; order }));
            result + order * 100
        }
        "#,
        "",
    );
    // `right` is written first and evaluates to 1, `left` second and gets 2,
    // yet the slots follow the declared type order: left=2, right=1.
    f.source_and_wasm("Result: i32(221)\n");
}

#[test]
fn labeled_tuple_missing_label_is_rejected() {
    let f = Fixture::new();
    for source in [
        "fn take(pair: (left: i32, right: i32)) {} fn main() { take((left: 1,)); }",
        "fn take(pair: (left: i32, right: i32)) {} fn main() { let p := (left: 1, right: 2); take((left: p.left,)); }",
    ] {
        f.write("missing.mb", source);
        let output = f.run(&["analyze", "missing.mb"]);
        assert_eq!(output.status.code(), Some(1));
        let message = String::from_utf8(output.stderr).unwrap();
        assert!(message.contains("TE002"), "{message}");
        assert!(
            message.contains("tuple arity does not match its expected type"),
            "{message}"
        );
    }
}

#[test]
fn tuple_exported_signatures_stay_rejected() {
    let f = Fixture::new();
    for (source, export, expected) in [
        (
            "fn main() {}\npub fn check(p: (i32, i32)) -> i32 { p.0 }\n",
            "check='main::check'",
            "exported signatures cannot take structs",
        ),
        (
            "fn main() {}\npub fn check() -> (left: i32, right: i32) { (left: 1, right: 2) }\n",
            "check='main::check'",
            "exported signatures cannot return structs",
        ),
    ] {
        f.project(source, &format!("[export]\n{export}\n"));
        let output = f.run(&["build", "--lib"]);
        assert_eq!(output.status.code(), Some(1));
        let message = String::from_utf8_lossy(&output.stderr);
        assert!(message.contains("LE900"), "{message}");
        assert!(message.contains(expected), "{message}");
    }
}
