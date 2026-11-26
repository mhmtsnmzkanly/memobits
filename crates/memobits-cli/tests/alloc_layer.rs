//! The alloc layer: `use alloc::List;` and `[build] alloc = true|false`.
use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    /// A project whose manifest has the given `[build]` body (may be empty).
    fn new(build: &str, main: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-alloc-layer-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        let build = if build.is_empty() {
            String::new()
        } else {
            format!("[build]\n{build}\n")
        };
        fs::write(
            path.join("project.toml"),
            format!("[package]\nname='layers'\nentry='main::main'\n{build}"),
        )
        .unwrap();
        fs::write(path.join("src/main.mb"), main).unwrap();
        Self(path)
    }

    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_mb"))
            .current_dir(&self.0)
            .args(args)
            .output()
            .unwrap()
    }

    /// Rewrite the manifest with another `[build]` body, keeping the sources
    /// (so artifacts compare byte for byte, trap metadata paths included).
    fn set_build(&self, build: &str) {
        let build = if build.is_empty() {
            String::new()
        } else {
            format!("[build]\n{build}\n")
        };
        fs::write(
            self.0.join("project.toml"),
            format!("[package]\nname='layers'\nentry='main::main'\n{build}"),
        )
        .unwrap();
    }

    fn artifact(&self, name: &str) -> Vec<u8> {
        let built = self.run(&["build", "--output", name]);
        assert!(built.status.success(), "{built:?}");
        fs::read(self.0.join(name)).unwrap()
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

fn succeeds(output: &Output) {
    assert!(output.status.success(), "{output:?}");
    assert!(stderr(output).is_empty(), "{output:?}");
}

fn fails_with(output: &Output, code: &str) -> String {
    let text = stderr(output);
    assert!(!output.status.success(), "{output:?}");
    assert!(text.contains(&format!("error[{code}]")), "{text}");
    text
}

const LIST_BODY: &str = "fn main() -> u32 ! Error {
    var bytes: List<u8> = [];
    bytes.push(7);
    bytes.push(9);
    Ok(bytes.len())
}";

#[test]
fn list_imports_work_in_every_form() {
    for (label, source) in [
        ("direct", format!("use alloc::List;\n{LIST_BODY}")),
        ("grouped", format!("use alloc::{{List}};\n{LIST_BODY}")),
        (
            "module path",
            LIST_BODY.replace("List<u8>", "alloc::List<u8>").replacen(
                "fn main",
                "use alloc;\nfn main",
                1,
            ),
        ),
    ] {
        for build in ["", "alloc = true"] {
            let project = Fixture::new(build, &source);
            let run = project.run(&["run"]);
            succeeds(&run);
            assert_eq!(stdout(&run), "Result: Ok(u32(2))\n", "{label} / {build}");
            succeeds(&project.run(&["check"]));
        }
    }
}

#[test]
fn list_without_an_import_is_an_unknown_type_with_a_note() {
    for source in [
        LIST_BODY.to_owned(),
        // `use alloc::List;` of another symbol or the module path alone is not enough.
        format!("use alloc;\n{LIST_BODY}"),
        LIST_BODY
            .replace("List<u8>", "alloc::List<u8>")
            .replacen("fn main", "fn main", 1),
    ] {
        let project = Fixture::new("", &source);
        for command in ["check", "build", "run"] {
            let text = fails_with(&project.run(&[command]), "NE003");
            assert!(text.contains("unknown type 'List'"), "{text}");
            assert!(
                text.contains("note: add `use alloc::List;` to use List"),
                "{text}"
            );
        }
    }
}

#[test]
fn alloc_false_rejects_alloc_imports_naming_the_setting() {
    for import in ["use alloc::List;", "use alloc::{List};", "use alloc;"] {
        let source = format!("{import}\nfn main() -> i32 {{ 1 }}");
        let project = Fixture::new("alloc = false", &source);
        for command in ["check", "build", "run", "test"] {
            let text = fails_with(&project.run(&[command]), "ME012");
            assert!(text.contains("`[build] alloc = false`"), "{import}: {text}");
        }
    }
}

#[test]
fn alloc_false_list_without_an_import_names_the_setting_in_the_note() {
    let project = Fixture::new("alloc = false", LIST_BODY);
    let text = fails_with(&project.run(&["check"]), "NE003");
    assert!(text.contains("`[build] alloc = false`"), "{text}");
    assert!(!text.contains("add `use alloc::List;`"), "{text}");
}

#[test]
fn alloc_false_rejects_every_heap_producing_string_operation() {
    let cases = [
        (
            "concat",
            "fn main() -> u32 ! Error { let joined := \"ab\".concat(\"cd\"); Ok(joined.len()) }",
        ),
        (
            "push_str",
            "fn main() -> u32 ! Error { var text := \"ab\"; text.push_str(\"cd\"); Ok(text.len()) }",
        ),
        (
            "to_utf8_string",
            "fn main() -> u32 ! Error {
                let bytes: array<u8, 2> = [104, 105];
                match bytes.to_utf8_string(2) { Ok(text) => Ok(text.len()), Err(_) => Ok(0) }
            }",
        ),
    ];
    for (operation, source) in cases {
        // The same source compiles with the default alloc layer.
        let with_alloc = Fixture::new("", source);
        succeeds(&with_alloc.run(&["check"]));
        let project = Fixture::new("alloc = false", source);
        for command in ["check", "build", "run"] {
            let text = fails_with(&project.run(&[command]), "TE033");
            assert!(text.contains(operation), "{operation}: {text}");
            assert!(
                text.contains("`[build] alloc = false`"),
                "{operation}: {text}"
            );
        }
        // Test functions are checked in the same way.
        let tested = Fixture::new(
            "alloc = false",
            &format!(
                "fn main() -> i32 {{ 1 }}\n{}",
                source.replace("fn main", "fn helper")
            ),
        );
        fails_with(&tested.run(&["check"]), "TE033");
    }
}

const CORE_ONLY: &str = "type Shape [ Dot, Square(u32), Rect(u32, u32) ]
fn area(shape: Shape) -> u32 {
    match shape { Shape::Dot => 1, Shape::Square(side) => side * side, Shape::Rect(w, h) => w * h }
}
fn digits(text: borrow string) -> u32 {
    var count: u32 = 0;
    var index: u32 = 0;
    loop {
        if index >= text.len() { break; }
        match text.byte_at(index) { Some(byte) => { if byte >= 48 && byte <= 57 { count = count + 1; } }, None => {} }
        index = index + 1;
    }
    count
}
test fn core_only_test() {
    assert(area(Shape::Rect(2, 3)) == 6);
}
fn main() -> u32 ! Error {
    let label := \"a1b22\";
    let data: array<u8, 4> = [1, 2, 3, 4];
    Ok(area(Shape::Square(4)) + digits(label.borrow()) + data[3] as u32)
}";

struct Shape {
    functions: u32,
    grows: bool,
    memory: Option<(u64, Option<u64>)>,
}

fn shape(bytes: &[u8]) -> Shape {
    let mut shape = Shape {
        functions: 0,
        grows: false,
        memory: None,
    };
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        match payload.unwrap() {
            wasmparser::Payload::FunctionSection(section) => shape.functions = section.count(),
            wasmparser::Payload::MemorySection(section) => {
                let memory = section.into_iter().next().unwrap().unwrap();
                shape.memory = Some((memory.initial, memory.maximum));
            }
            wasmparser::Payload::CodeSectionEntry(body) => {
                for operator in body.get_operators_reader().unwrap() {
                    shape.grows |=
                        matches!(operator.unwrap(), wasmparser::Operator::MemoryGrow { .. });
                }
            }
            _ => {}
        }
    }
    shape
}

#[test]
fn alloc_false_runs_a_core_only_program_without_an_allocator() {
    let project = Fixture::new("alloc = false", CORE_ONLY);
    succeeds(&project.run(&["check"]));
    let source = project.run(&["run"]);
    succeeds(&source);
    assert_eq!(stdout(&source), "Result: Ok(u32(23))\n");
    let artifact = project.artifact("core.wasm");
    let standalone = project.run(&["run", "core.wasm"]);
    succeeds(&standalone);
    assert_eq!(stdout(&standalone), stdout(&source));

    let core = shape(&artifact);
    assert!(!core.grows, "alloc = false output must not grow memory");
    let (initial, maximum) = core.memory.expect("the program has a memory");
    assert_eq!(maximum, Some(initial), "memory must be fixed");

    // The same program is byte-identical with an explicit `alloc = true` or
    // no setting (the allocator is only emitted when a heap operation is
    // reachable).
    project.set_build("alloc = true");
    assert!(project.artifact("core.wasm") == artifact);
    project.set_build("");
    assert!(project.artifact("core.wasm") == artifact);
}

#[test]
fn allocator_functions_exist_only_when_the_program_allocates() {
    // Positive control: a concat program has the allocator, growth and a
    // growable memory, so the absence above is meaningful.
    let heap = Fixture::new(
        "",
        "fn main() -> u32 ! Error { let joined := \"ab\".concat(\"cd\"); Ok(joined.len()) }",
    );
    let allocating = shape(&heap.artifact("heap.wasm"));
    let core = shape(&Fixture::new("alloc = false", CORE_ONLY).artifact("core.wasm"));
    assert!(allocating.grows);
    let (initial, maximum) = allocating.memory.unwrap();
    assert!(maximum.is_none_or(|maximum| maximum > initial));
    // Reserve, release and copy helpers are three extra functions.
    assert!(allocating.functions >= 3, "{}", allocating.functions);
    assert!(!core.grows);
}

#[test]
fn alloc_true_artifacts_do_not_depend_on_the_setting() {
    let source = format!("use alloc::List;\n{LIST_BODY}");
    let project = Fixture::new("", &source);
    let default = project.artifact("a.wasm");
    project.set_build("alloc = true");
    assert!(project.artifact("a.wasm") == default);
}

#[test]
fn mb_test_works_in_both_modes() {
    let off = Fixture::new("alloc = false", CORE_ONLY);
    let report = off.run(&["test"]);
    succeeds(&report);
    assert!(
        stdout(&report).contains("test result: ok. 1 passed; 0 failed; 0 filtered out"),
        "{}",
        stdout(&report)
    );
    let on = Fixture::new(
        "alloc = true",
        "use alloc::List;
fn main() -> i32 { 0 }
test fn list_len() {
    var bytes: List<u8> = [];
    bytes.push(1);
    assert(bytes.len() == 1);
}
test fn concat_len() {
    let joined := \"ab\".concat(\"cd\");
    assert(joined.len() == 4);
}",
    );
    let report = on.run(&["test"]);
    succeeds(&report);
    assert!(
        stdout(&report).contains("test result: ok. 2 passed; 0 failed; 0 filtered out"),
        "{}",
        stdout(&report)
    );
    // The same tests fail to compile when the alloc layer is off.
    let off_again = Fixture::new(
        "alloc = false",
        "fn main() -> i32 { 0 }
test fn concat_len() {
    let joined := \"ab\".concat(\"cd\");
    assert(joined.len() == 4);
}",
    );
    fails_with(&off_again.run(&["test"]), "TE033");
}

#[test]
fn a_bare_user_type_named_list_needs_no_import() {
    let project = Fixture::new(
        "alloc = false",
        "type List { count: u32 }
fn main() -> u32 ! Error { let items: List = List { count: 3 }; Ok(items.count) }",
    );
    let run = project.run(&["run"]);
    succeeds(&run);
    assert_eq!(stdout(&run), "Result: Ok(u32(3))\n");
}

#[test]
fn a_project_module_named_alloc_is_reserved() {
    let project = Fixture::new("", "fn main() -> i32 { 1 }");
    fs::write(project.0.join("src/alloc.mb"), "pub fn x() -> i32 { 1 }").unwrap();
    fails_with(&project.run(&["check"]), "ME011");
}
