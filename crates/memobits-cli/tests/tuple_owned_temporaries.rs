//! Owned String tuples may be created temporarily for a direct internal call.
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
            "memobits-tuple-temporary-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            "[package]\nname='tuple-owned-temporary'\nentry='main::main'\n",
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

#[test]
fn temporary_owned_string_tuple_transfers_to_call_and_cleans_on_later_exit() {
    let fixture = Fixture::new();
    fixture.source(
        r#"
        fn consume(pair: (string, string, u32)) -> i32 {
            let (left, right, base) := pair;
            if left.len() == 3 && right.len() == 3 { base as i32 + 6 } else { 0 }
        }
        fn postpone(pair: (string, u32), flag: bool) -> i32 { pair.1 as i32 }
        fn main() -> i32 {
            let left := "xy".concat("!");
            let right := "ab".concat("?");
            let result := consume((left, right, 36 as u32));
            if result == 42 {
                let text := "zz".concat("");
                postpone((text, 1 as u32), { return result; false })
            } else { 0 }
        }
        "#,
    );

    let source = fixture.run(&["run"]);
    assert!(source.status.success(), "source failed: {source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");

    let build = fixture.run(&["build", "--output", "tuple-owned-temporary.wasm"]);
    assert!(build.status.success(), "build failed: {build:?}");
    let wasm = fixture.run(&["run", "tuple-owned-temporary.wasm"]);
    assert!(wasm.status.success(), "Wasm failed: {wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn nested_nominal_string_owning_tuple_temporaries_keep_the_existing_transport_gate() {
    let fixture = Fixture::new();
    fixture.source(
        "type Holder { text: string } fn consume(pair: (Holder, bool)) {} fn main() -> i32 { let text := \"x\".concat(\"\"); let inner := Holder { text: text }; consume((inner, true)); 0 }",
    );
    let build = fixture.run(&["build"]);
    assert_eq!(build.status.code(), Some(1), "{build:?}");
    let stderr = String::from_utf8_lossy(&build.stderr);
    assert!(stderr.contains("TE017"), "{stderr}");
    assert!(
        stderr
            .contains("owned tuple calls cannot transport nested String-owning aggregates other than tuples in this slice"),
        "{stderr}"
    );
}

#[test]
fn nested_string_tuples_move_through_temporary_calls_and_destructure_in_source_and_wasm() {
    let fixture = Fixture::new();
    fixture.source(
        r#"
        fn forward(pair: ((string, string), u32)) -> ((string, string), u32) { pair }
        fn consume(pair: ((string, string), u32)) -> i32 {
            let ((left, right), base) := pair;
            if left.len() == 2 && right.len() == 2 { base as i32 + 4 } else { 0 }
        }
        fn main() -> i32 {
            let left := "ab".concat("");
            let right := "cd".concat("");
            let inner := (left, right);
            consume(forward((inner, 38 as u32)))
        }
        "#,
    );

    let source = fixture.run(&["run"]);
    assert!(source.status.success(), "source failed: {source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");

    let build = fixture.run(&["build", "--output", "nested-string-tuple.wasm"]);
    assert!(build.status.success(), "build failed: {build:?}");
    let wasm = fixture.run(&["run", "nested-string-tuple.wasm"]);
    assert!(wasm.status.success(), "Wasm failed: {wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn string_owning_tuple_field_in_local_nominal_record_cleans_in_source_and_wasm() {
    let fixture = Fixture::new();
    fixture.source(
        r#"
        type TextRecord { values: (string, string), count: u32 }
        fn main() -> i32 {
            let left := "ab".concat("");
            let right := "cd".concat("");
            let values := (left, right);
            let record := TextRecord { values: values, count: 38 as u32 };
            if record.values.0.len() == 2 && record.values.1.len() == 2 {
                record.count as i32 + 4
            } else { 0 }
        }
        "#,
    );

    let source = fixture.run(&["run"]);
    assert!(source.status.success(), "source failed: {source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");

    let build = fixture.run(&["build", "--output", "tuple-owner-record.wasm"]);
    assert!(build.status.success(), "build failed: {build:?}");
    let wasm = fixture.run(&["run", "tuple-owner-record.wasm"]);
    assert!(wasm.status.success(), "Wasm failed: {wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn string_owning_tuple_enum_payload_moves_and_cleans_on_normal_and_early_returns() {
    let fixture = Fixture::new();
    fixture.source(
        r#"
        type TextState [ Texts((string, string), u32), Empty ]
        fn package(pair: (string, string), count: u32) -> TextState {
            TextState::Texts(pair, count)
        }
        fn consume(state: TextState) -> u32 {
            match state {
                TextState::Texts(pair, count) => {
                    let (left, right) := pair;
                    left.len() + right.len() + count
                },
                TextState::Empty => 0,
            }
        }
        fn exit_early(state: TextState, flag: bool) -> u32 {
            if flag { return 1; }
            consume(state)
        }
        fn main() -> i32 {
            let left := "ab".concat("");
            let right := "cd".concat("");
            let early := exit_early(package((left, right), 90 as u32), true);
            let first := "ab".concat("");
            let second := "cd".concat("");
            let normal := package((first, second), 40 as u32);
            early as i32 + consume(normal) as i32
        }
        "#,
    );

    let source = fixture.run(&["run"]);
    assert!(source.status.success(), "source failed: {source:?}");
    assert_eq!(source.stdout, b"Result: i32(45)\n");

    let build = fixture.run(&["build", "--output", "tuple-enum-payload.wasm"]);
    assert!(build.status.success(), "build failed: {build:?}");
    let wasm = fixture.run(&["run", "tuple-enum-payload.wasm"]);
    assert!(wasm.status.success(), "Wasm failed: {wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn nested_tuple_owner_does_not_open_by_value_nominal_transport() {
    let fixture = Fixture::new();
    fixture.source(
        "type TextRecord { values: (string, string), count: u32 } fn consume(record: TextRecord) {} fn main() { let left := \"a\".concat(\"\"); let right := \"b\".concat(\"\"); let values := (left, right); consume(TextRecord { values: values, count: 0 }); }",
    );
    let build = fixture.run(&["build"]);
    assert_eq!(build.status.code(), Some(1), "{build:?}");
    let stderr = String::from_utf8_lossy(&build.stderr);
    assert!(stderr.contains("LE900"), "{stderr}");
    assert!(
        stderr.contains("structs with String fields can cross internal calls only as borrow or share parameters"),
        "{stderr}"
    );
}
