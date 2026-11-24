//! D2 nested `Result<String, E>` storage: a Result held in a struct field or a
//! fixed-array element is accepted only while its payload is a String literal
//! (zero allocation provenance) or an `Err` payload. Heap-owning Results must
//! stay rejected by IR ownership validation so no heap block can reach nested
//! storage that lacks a consuming read path.
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
            "memobits-nested-result-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::create_dir(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            "[package]\nname='nested-result'\nentry='main::main'\n",
        )
        .unwrap();
        Self(path)
    }

    fn source(&self, text: &str) {
        fs::write(self.0.join("src/main.mb"), text).unwrap();
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

fn assert_source_and_wasm(source_text: &str, expected: u32) {
    let fixture = Fixture::new();
    fixture.source(source_text);
    let source = fixture.run(&["run"]);
    assert!(source.status.success(), "source failed: {source:?}");
    assert_eq!(
        source.stdout,
        format!("Result: u32({expected})\n").as_bytes()
    );
    let build = fixture.run(&["build", "--output", "nested.wasm"]);
    assert!(build.status.success(), "build failed: {build:?}");
    let wasm = fixture.run(&["run", "nested.wasm"]);
    assert!(wasm.status.success(), "Wasm failed: {wasm:?}");
    assert_eq!(wasm.stdout, format!("Result: i32({expected})\n").as_bytes());
}

#[test]
fn struct_fields_hold_literal_ok_and_err_results() {
    assert_source_and_wasm(
        r#"type Box { text: string ! Error, n: u32 }
fn main() -> u32 {
    let ok: string ! Error = Ok("é");
    let first := Box { text: ok, n: 5 };
    let failed: string ! Error = Err(Error { code: 7 });
    let second := Box { text: failed, n: 2 };
    let code := match second.text { Ok(_) => 0 as u32, Err(error) => error.code };
    first.n + second.n + code
}"#,
        14,
    );
}

#[test]
fn fixed_arrays_of_results_read_back_through_match_and_move_into_calls() {
    assert_source_and_wasm(
        r#"fn code_at(items: array<string ! Error, 2>) -> u32 {
    match items[1] { Ok(_) => 0, Err(error) => error.code }
}
fn count(items: borrow array<string ! Error, 2>) -> u32 { 2 }
fn main() -> u32 {
    let first: string ! Error = Ok("é");
    let second: string ! Error = Err(Error { code: 9 });
    let items := [first, second];
    let counted := count(items.borrow());
    let direct := match items[1] { Ok(_) => 0 as u32, Err(error) => error.code };
    counted + direct + code_at(items)
}"#,
        20,
    );
}

#[test]
fn heap_owning_results_stay_rejected_in_nested_storage() {
    for source in [
        // Struct field initialized from a heap String payload.
        r#"type Box { text: string ! Error, n: u32 }
fn main() -> u32 {
    let text := "a".concat("b");
    let result: string ! Error = Ok(text);
    let boxed := Box { text: result, n: 1 };
    boxed.n
}"#,
        // Array element from a heap Result returned by a call.
        r#"fn make(text: string) -> string ! Error { Ok(text) }
fn main() -> u32 {
    let result := make("a".concat("b"));
    let items := [result];
    1
}"#,
        // Replacing a literal element with a heap Result.
        r#"fn main() -> u32 {
    let first: string ! Error = Ok("a");
    var items := [first];
    let text := "a".concat("b");
    let heap: string ! Error = Ok(text);
    items[0] = heap;
    1
}"#,
        // Reading a heap-capable nested Result without a consuming match.
        r#"type Box { text: string ! Error, n: u32 }
fn main() -> u32 {
    let ok: string ! Error = Ok("a");
    let boxed := Box { text: ok, n: 1 };
    match boxed.text { Ok(value) => value.len(), Err(error) => error.code }
}"#,
    ] {
        let fixture = Fixture::new();
        fixture.source(source);
        for args in [&["run"][..], &["build", "--output", "nested.wasm"][..]] {
            let output = fixture.run(args);
            assert!(!output.status.success(), "{source}");
            let stderr = String::from_utf8_lossy(&output.stderr);
            // Overwriting an owning element in place is TE022 (E1a); the other
            // shapes stay TE018.
            assert!(
                stderr.contains("TE018") || stderr.contains("TE022"),
                "{stderr}"
            );
        }
        assert!(!fixture.0.join("nested.wasm").exists());
    }
}
