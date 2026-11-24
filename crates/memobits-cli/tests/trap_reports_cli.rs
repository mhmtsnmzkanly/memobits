//! Checked runtime failures are reported with their reason and source
//! location, from a source run and from a built artifact alike.
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
            "memobits-trap-cli-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            "[package]\nname='traps'\nentry='app::main'\n",
        )
        .unwrap();
        Self(path)
    }
    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_mb"))
            .current_dir(&self.0)
            .args(args)
            .output()
            .unwrap()
    }
    fn failure(&self, args: &[&str]) -> String {
        let output = self.run(args);
        assert_eq!(output.status.code(), Some(1), "{args:?}");
        assert!(output.stdout.is_empty());
        String::from_utf8(output.stderr).unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Remove the custom section named `name` from a module (sections are framed
/// as id, LEB size, payload).
fn strip_custom_section(module: &[u8], name: &str) -> Vec<u8> {
    fn leb(bytes: &[u8]) -> (usize, usize) {
        let (mut value, mut shift) = (0usize, 0);
        for (index, byte) in bytes.iter().enumerate() {
            value |= usize::from(byte & 0x7f) << shift;
            shift += 7;
            if byte & 0x80 == 0 {
                return (value, index + 1);
            }
        }
        panic!("bad leb");
    }
    let mut out = module[..8].to_vec();
    let mut at = 8;
    while at < module.len() {
        let id = module[at];
        let (size, used) = leb(&module[at + 1..]);
        let end = at + 1 + used + size;
        let payload = &module[at + 1 + used..end];
        let (name_len, name_used) = leb(payload);
        let is_target = id == 0 && &payload[name_used..name_used + name_len] == name.as_bytes();
        if !is_target {
            out.extend_from_slice(&module[at..end]);
        }
        at = end;
    }
    out
}

/// Run `source` from source and from a built artifact; both must report
/// `reason` at `line:column` of `src/app.mb`. A stripped artifact falls back to
/// the generic trap message.
fn reports(source: &str, reason: &str, line: usize, column: usize) {
    let f = Fixture::new();
    fs::write(f.0.join("src/app.mb"), source).unwrap();
    let source_run = f.failure(&["run"]);
    assert!(build_ok(&f), "{source}");
    let artifact = f.failure(&["run", "target/memobits/app.wasm"]);
    for text in [&source_run, &artifact] {
        assert!(
            text.starts_with(&format!("error[RE007]: {reason}\n")),
            "{source}: {text}"
        );
        assert!(
            text.contains(&format!("app.mb:{line}:{column}\n")),
            "{source}: {text}"
        );
        assert!(
            text.contains(&format!(
                " {line} | {}",
                source.lines().nth(line - 1).unwrap()
            )),
            "{source}: {text}"
        );
        assert!(!text.contains("unreachable"), "{text}");
    }
    assert_eq!(source_run, artifact);

    let path = f.0.join("target/memobits/app.wasm");
    let bytes = fs::read(&path).unwrap();
    let stripped = strip_custom_section(&bytes, "memobits.traps");
    assert!(stripped.len() < bytes.len(), "section was present");
    fs::write(f.0.join("stripped.wasm"), stripped).unwrap();
    let generic = f.failure(&["run", "stripped.wasm"]);
    assert!(
        generic.contains("error[RE007]: WebAssembly execution trapped"),
        "{generic}"
    );
    assert!(!generic.contains("app.mb"), "{generic}");
}

fn build_ok(f: &Fixture) -> bool {
    f.run(&["build"]).status.success()
}

#[test]
fn integer_overflow_reports_the_operation() {
    reports(
        "fn main() -> i32 {\n    var a := 2147483647;\n    a + 1\n}",
        "integer overflow in addition",
        3,
        5,
    );
    reports(
        "fn main() -> i32 {\n    var a := -2147483647;\n    a - 2\n}",
        "integer overflow in subtraction",
        3,
        5,
    );
    reports(
        "fn main() -> i32 {\n    var a := 2147483647;\n    a * 2\n}",
        "integer overflow in multiplication",
        3,
        5,
    );
    reports(
        "fn main() -> i32 {\n    var a := -2147483647 - 1;\n    -a\n}",
        "integer overflow in negation",
        3,
        5,
    );
}

#[test]
fn narrow_and_wide_integers_report_too() {
    reports(
        "fn main() -> u8 {\n    var a: u8 = 0;\n    a - 1\n}",
        "integer overflow in subtraction",
        3,
        5,
    );
    reports(
        "fn main() -> i64 {\n    var a: i64 = 9223372036854775807;\n    a + 1\n}",
        "integer overflow in addition",
        3,
        5,
    );
    reports(
        "fn main() -> i64 {\n    var a: i64 = 4611686018427387904;\n    a * 2\n}",
        "integer overflow in multiplication",
        3,
        5,
    );
}

#[test]
fn division_failures_report_zero_and_signed_overflow() {
    reports(
        "fn main() -> i32 {\n    var z := 0;\n    let x := 5 / z;\n    x\n}",
        "division by zero",
        3,
        14,
    );
    reports(
        "fn main() -> i32 {\n    var value := 5;\n    var divisor := 0;\n    value /= divisor;\n    value\n}",
        "division by zero",
        4,
        5,
    );
    reports(
        "fn main() -> i32 {\n    var z := 0;\n    7 % z\n}",
        "remainder by zero",
        3,
        5,
    );
    reports(
        "fn main() -> i32 {\n    var a := -2147483647 - 1;\n    var b := -1;\n    a / b\n}",
        "integer overflow in division",
        4,
        5,
    );
    reports(
        "fn main() -> i32 {\n    var value: i32 = -2147483647 - 1;\n    var divisor: i32 = -1;\n    value /= divisor;\n    value\n}",
        "integer overflow in division",
        4,
        5,
    );
    reports(
        "fn main() -> i64 {\n    var a: i64 = -9223372036854775807 - 1;\n    var b: i64 = -1;\n    a / b\n}",
        "integer overflow in division",
        4,
        5,
    );
    reports(
        "fn main() -> i8 {\n    var a: i8 = -127 - 1;\n    var b: i8 = -1;\n    a / b\n}",
        "integer overflow in division",
        4,
        5,
    );
}

#[test]
fn array_bounds_report_reads_and_writes_at_every_level() {
    reports(
        "fn main() -> i32 {\n    var a := [1, 2, 3];\n    var i := 3;\n    a[i]\n}",
        "array index out of bounds",
        4,
        5,
    );
    reports(
        "fn main() -> i32 {\n    var g := [[1, 2], [3, 4]];\n    var i := 2;\n    g[0][i]\n}",
        "array index out of bounds",
        4,
        5,
    );
    reports(
        "fn main() -> i32 {\n    var g := [[1, 2], [3, 4]];\n    var i := 2;\n    g[i][0]\n}",
        "array index out of bounds",
        4,
        5,
    );
    reports(
        "fn main() -> i32 {\n    var g := [[1, 2], [3, 4]];\n    var i := 5;\n    g[1][i] = 7;\n    0\n}",
        "array index out of bounds",
        4,
        5,
    );
}

#[test]
fn stack_overflow_keeps_its_own_code() {
    let f = Fixture::new();
    fs::write(
        f.0.join("project.toml"),
        "[package]\nname='traps'\nentry='app::main'\n[build]\nstack_size = 65536\n",
    )
    .unwrap();
    fs::write(
        f.0.join("src/app.mb"),
        "fn rec(n: i32) -> i32 { let a: array<i32, 1024> = [n; 1024]; \
         if n == 0 { 0 } else { rec(n - 1) + a[1023] } } \
         pub fn main() -> i32 { rec(100000) }",
    )
    .unwrap();
    let text = f.failure(&["run"]);
    assert!(text.contains("error[RE008]"), "{text}");
}

#[test]
fn the_trap_reasons_agree_between_backend_and_runtime() {
    use memobits_wasm::TrapReason as Wasm;
    // Explicit codes decode to a reason; the native division codes do not.
    let f = Fixture::new();
    fs::write(
        f.0.join("src/app.mb"),
        "fn main() -> i32 {\n    var a := 2147483647;\n    a + 1\n}",
    )
    .unwrap();
    assert!(build_ok(&f));
    let bytes = fs::read(f.0.join("target/memobits/app.wasm")).unwrap();
    let payload = memobits_runtime::custom_section(&bytes, memobits_wasm::TRAP_SECTION).unwrap();
    assert!(memobits_runtime::TrapTable::decode(payload).is_some());
    assert_eq!(memobits_wasm::TRAP_EXPORT, "__mb_trap");
    assert_eq!(memobits_runtime::TRAP_SECTION, memobits_wasm::TRAP_SECTION);
    assert_eq!(Wasm::Division.code(), 5);
    assert_eq!(Wasm::Remainder.code(), 6);
    use memobits_runtime::TrapReason as Runtime;
    for (wasm, runtime) in [
        (Wasm::Add, Runtime::AddOverflow),
        (Wasm::Subtract, Runtime::SubtractOverflow),
        (Wasm::Multiply, Runtime::MultiplyOverflow),
        (Wasm::Negate, Runtime::NegateOverflow),
        (Wasm::DivisionOverflow, Runtime::DivisionOverflow),
        (Wasm::IndexOutOfBounds, Runtime::IndexOutOfBounds),
        (Wasm::ArgumentRange, Runtime::ArgumentRange),
        (Wasm::HeapAllocation, Runtime::HeapAllocation),
        (Wasm::ShiftCount, Runtime::ShiftCount),
        (Wasm::AssertionFailed, Runtime::AssertionFailed),
        (Wasm::InvalidFunction, Runtime::InvalidFunction),
    ] {
        assert_eq!(Runtime::from_explicit_code(wasm.code()), Some(runtime));
    }
    assert_eq!(Runtime::from_explicit_code(Wasm::Division.code()), None);
    assert_eq!(Runtime::from_explicit_code(Wasm::Remainder.code()), None);
}
