//! D2 nested `Result<String, E>` storage: a Result held in a struct field or a
//! fixed-array element, including a heap-owning one (lifted by F2: nested
//! storage releases a Result's String type-directed like any other enum).
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
fn heap_owning_results_work_in_nested_storage() {
    // F2 lifted the old rejection: a heap Result in a struct field, a fixed
    // array element, an element replacement or a `match` on a field works from
    // source and from the Wasm artifact (cleanup is covered by the capped
    // stress tests in `f2_payloads.rs`).
    assert_source_and_wasm(
        r#"type Box { text: string ! Error, n: u32 }
fn main() -> u32 {
    let text := "a".concat("b");
    let result: string ! Error = Ok(text);
    let boxed := Box { text: result, n: 1 };
    boxed.n
}"#,
        1,
    );
    assert_source_and_wasm(
        r#"fn make(text: string) -> string ! Error { Ok(text) }
fn main() -> u32 {
    let result := make("a".concat("b"));
    let items := [result];
    match items[0] { Ok(text) => text.len(), Err(error) => error.code }
}"#,
        2,
    );
    assert_source_and_wasm(
        r#"fn main() -> u32 {
    let first: string ! Error = Ok("a");
    var items := [first];
    let text := "abc".concat("d");
    let heap: string ! Error = Ok(text);
    items[0] = heap;
    match items[0] { Ok(text) => text.len(), Err(error) => error.code }
}"#,
        4,
    );
    assert_source_and_wasm(
        r#"type Box { text: string ! Error, n: u32 }
fn main() -> u32 {
    let ok: string ! Error = Ok("a");
    let boxed := Box { text: ok, n: 1 };
    match boxed.text { Ok(value) => value.len(), Err(error) => error.code }
}"#,
        1,
    );
}
