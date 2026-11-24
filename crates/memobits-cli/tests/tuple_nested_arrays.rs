//! D2 aggregate placement acceptance: tuples and fixed arrays must compose
//! in both directions through source execution and the Wasm backend.
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
            "memobits-tuple-arrays-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::create_dir(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            "[package]\nname='tuple-array-placement'\nentry='main::main'\n",
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

fn assert_source_and_wasm(fixture: &Fixture, source_text: &str, artifact: &str) {
    assert_source_and_wasm_output(
        fixture,
        source_text,
        artifact,
        b"Result: i32(42)\n",
        b"Result: i32(42)\n",
    );
}

fn assert_source_and_wasm_output(
    fixture: &Fixture,
    source_text: &str,
    artifact: &str,
    source_expected: &[u8],
    wasm_expected: &[u8],
) {
    fixture.source(source_text);
    let source = fixture.run(&["run"]);
    assert!(source.status.success(), "source failed: {source:?}");
    assert_eq!(source.stdout, source_expected);

    let build = fixture.run(&["build", "--output", artifact]);
    assert!(build.status.success(), "build failed: {build:?}");
    let wasm = fixture.run(&["run", artifact]);
    assert!(wasm.status.success(), "Wasm failed: {wasm:?}");
    assert_eq!(wasm.stdout, wasm_expected);
}

#[test]
fn tuples_compose_with_fixed_arrays_in_both_aggregate_directions() {
    let fixture = Fixture::new();

    assert_source_and_wasm(
        &fixture,
        "fn read(values: array<(i32, bool), 2>) -> i32 { if values[1].1 { values[0].0 + values[1].0 } else { 0 } } fn main() -> i32 { read([(40, false), (2, true)]) }",
        "array-of-tuples.wasm",
    );

    assert_source_and_wasm(
        &fixture,
        "fn read(value: (array<i32, 2>, i32)) -> i32 { value.0[1] + value.1 } fn main() -> i32 { read(([40, 2], 40)) }",
        "tuple-with-array.wasm",
    );
}

#[test]
fn string_owning_tuple_arrays_transfer_through_owned_calls() {
    let fixture = Fixture::new();
    assert_source_and_wasm_output(
        &fixture,
        "fn sum(values: array<(string, u32), 2>) -> u32 { values[0].1 + values[1].1 } fn main() -> u32 { let left := \"left\".concat(\"!\"); let right := \"right\".concat(\"!\"); let first: (string, u32) = (left, 20); let second: (string, u32) = (right, 22); let rows: array<(string, u32), 2> = [first, second]; sum(rows) }",
        "string-tuple-array.wasm",
        b"Result: u32(42)\n",
        b"Result: i32(42)\n",
    );

    assert_source_and_wasm_output(
        &fixture,
        "fn text_len(row: borrow (string, u32)) -> u32 { row.0.len() } fn main() -> u32 { let text := \"borrowed\".concat(\"!\"); let row: (string, u32) = (text, 40); let rows: array<(string, u32), 1> = [row]; text_len(rows[0].borrow()) + rows[0].1 }",
        "borrow-string-tuple-array.wasm",
        b"Result: u32(49)\n",
        b"Result: i32(49)\n",
    );
}

#[test]
fn tuple_array_elements_keep_reference_and_list_gates() {
    let fixture = Fixture::new();
    for (name, source, diagnostic) in [
        (
            "reference",
            "fn main() -> i32 { var value := 1; let rows := [(value.borrow(), 2)]; 0 }",
            "tuple elements cannot contain direct or nested references",
        ),
        (
            "list",
            "use alloc::List; fn main() -> i32 { let values: List<u8> = []; let rows := [(values, 2)]; 0 }",
            "arrays cannot contain tuples with List fields",
        ),
    ] {
        fixture.source(source);
        let output = fixture.run(&["build"]);
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("TE017"), "{name}: {stderr}");
        assert!(stderr.contains(diagnostic), "{name}: {stderr}");
    }
}

#[test]
fn enum_arrays_clean_active_tuple_and_nested_array_payloads() {
    let fixture = Fixture::new();
    assert_source_and_wasm_output(
        &fixture,
        "type Text [ Rows(array<(string, u32), 2>), Single((string, u32)), Empty ] fn consume(values: array<Text, 2>, early: bool) -> u32 { if early { return 1; } 42 } fn main() -> u32 { let a := \"a\".concat(\"\"); let b := \"b\".concat(\"\"); let c := \"c\".concat(\"\"); let first: (string, u32) = (a, 20); let second: (string, u32) = (b, 22); let third: (string, u32) = (c, 7); let rows: array<(string, u32), 2> = [first, second]; let row_state: Text = Text::Rows(rows); let single_state: Text = Text::Single(third); let values: array<Text, 2> = [row_state, single_state]; consume(values, false) }",
        "enum-array-owning-tuples.wasm",
        b"Result: u32(42)\n",
        b"Result: i32(42)\n",
    );
}
