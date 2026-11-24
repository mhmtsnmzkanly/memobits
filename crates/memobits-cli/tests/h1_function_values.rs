//! H1: function values (no captures).
//!
//! Function types (`fn(T, ...) -> R`, access modes in parameter positions),
//! top-level, imported and anonymous functions as values, `=>` expression
//! bodies, calls through locals, parameters, fields, elements and results, the
//! table-based Wasm representation, exact owner cleanup through function
//! values under capped memory, and the negative cases. Every positive program
//! runs from source and as a standalone Wasm artifact.
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
        Self::with(&[("main", source)], "")
    }

    fn with(modules: &[(&str, &str)], extra_manifest: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-h1-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            format!("[package]\nname='h1'\nentry='main::main'\n{extra_manifest}"),
        )
        .unwrap();
        for (name, source) in modules {
            fs::write(path.join(format!("src/{name}.mb")), source).unwrap();
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
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// Compile `source` and return stderr; `check` must fail with `code` and the
/// message must contain `needle`.
fn rejects(source: &str, code: &str, needle: &str) {
    let f = Fixture::new(source);
    let output = f.run(&["check", "--tests"]);
    let stderr = text(&output.stderr);
    assert!(!output.status.success(), "accepted:\n{source}");
    assert!(
        stderr.contains(code) && stderr.contains(needle),
        "expected {code} `{needle}` for:\n{source}\n{stderr}"
    );
}

/// `check`, `test` (expected count when nonzero), source `run` and standalone
/// Wasm `run`, each with empty stderr and the same `Result: i32(expected)`.
fn verify(f: &Fixture, tests: usize, expected: i64, label: &str) {
    let checked = f.run(&["check"]);
    assert!(
        checked.status.success(),
        "{label}: {}",
        text(&checked.stderr)
    );
    if tests > 0 {
        let report = f.run(&["test"]);
        let stdout = text(&report.stdout);
        assert!(
            report.status.success()
                && stdout.contains(&format!("test result: ok. {tests} passed; 0 failed")),
            "{label}: {stdout}{}",
            text(&report.stderr)
        );
    }
    let want = format!("Result: i32({expected})\n");
    let source_run = f.run(&["run"]);
    assert!(
        source_run.status.success() && source_run.stderr.is_empty(),
        "{label} source run: {}",
        text(&source_run.stderr)
    );
    assert_eq!(text(&source_run.stdout), want, "{label} (source)");
    let build = f.run(&["build", "--output", "h1.wasm"]);
    assert!(build.status.success(), "{label}: {}", text(&build.stderr));
    let wasm = f.run(&["run", "h1.wasm"]);
    assert!(
        wasm.status.success() && wasm.stderr.is_empty(),
        "{label} wasm run: {}",
        text(&wasm.stderr)
    );
    assert_eq!(text(&wasm.stdout), want, "{label} (wasm)");
}

fn single(source: &str, tests: usize, expected: i64, label: &str) {
    verify(&Fixture::new(source), tests, expected, label);
}

// ---------------------------------------------------------------------------
// Function types and values in every position

#[test]
fn higher_order_helpers_and_passing() {
    single(
        r#"fn inc(x: i32) -> i32 { x + 1 }
fn dbl(x: i32) -> i32 => x * 2
fn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }
fn twice(f: fn(i32) -> i32, x: i32) -> i32 { f(f(x)) }
fn then(f: fn(i32) -> i32, g: fn(i32) -> i32, x: i32) -> i32 { g(f(x)) }
fn map_sum(f: fn(i32) -> i32, xs: array<i32, 4>) -> i32 {
    var total := 0;
    loop x in xs { total += f(x); }
    total
}
fn fold(f: fn(i32, i32) -> i32, start: i32, xs: array<i32, 4>) -> i32 {
    var accumulator := start;
    var i: u32 = 0;
    loop {
        if i == 4 { break; }
        accumulator = f(accumulator, xs[i]);
        i += 1;
    }
    accumulator
}
fn add(a: i32, b: i32) -> i32 { a + b }
fn unit_step(f: fn(share i32), v: share i32) { f(v.share()); }
fn pick(flag: bool) -> fn(i32) -> i32 { if flag { inc } else { dbl } }
test fn passing() {
    assert(apply(inc, 1) == 2);
    assert(apply(dbl, 4) == 8);
    assert(twice(inc, 1) == 3);
    assert(twice(dbl, 3) == 12);
    assert(then(inc, dbl, 2) == 6);
    assert(then(dbl, inc, 2) == 5);
    assert(map_sum(inc, [1, 2, 3, 4]) == 14);
    assert(map_sum(dbl, [1, 2, 3, 4]) == 20);
    assert(fold(add, 0, [1, 2, 3, 4]) == 10);
    assert(pick(true)(5) == 6);
    assert(pick(false)(5) == 10);
}
fn bump(n: share i32) { n = n + 1; }
test fn modes() {
    var k := 1;
    unit_step(bump, k.share());
    assert(k == 2);
}
fn main() -> i32 { then(inc, dbl, 3) + fold(add, 1, [1, 1, 1, 1]) + twice(dbl, 1) }
"#,
        2,
        8 + 5 + 4,
        "higher_order",
    );
}

#[test]
fn recursion_through_values() {
    single(
        r#"fn fact(self_call: fn(i32) -> i32, n: i32) -> i32 {
    if n <= 1 { 1 } else { n * self_call(n - 1) }
}
fn fact_entry(n: i32) -> i32 { fact(fact_entry, n) }
fn fib(self_call: fn(i32) -> i32, n: i32) -> i32 {
    if n < 2 { n } else { self_call(n - 1) + self_call(n - 2) }
}
fn fib_entry(n: i32) -> i32 => fib(fib_entry, n)
test fn recursion() {
    assert(fact_entry(5) == 120);
    assert(fib_entry(10) == 55);
}
fn main() -> i32 { fact_entry(4) + fib_entry(7) }
"#,
        1,
        24 + 13,
        "recursion",
    );
}

#[test]
fn function_values_in_aggregates() {
    single(
        r#"use alloc::List;
type Handler { name: u32, run: fn(i32) -> i32 }
type Op [ Unary(fn(i32) -> i32), Binary(fn(i32, i32) -> i32), Nothing ]
type Pair = (fn(i32) -> i32, i32);
fn inc(x: i32) -> i32 { x + 1 }
fn dbl(x: i32) -> i32 { x * 2 }
fn add(a: i32, b: i32) -> i32 { a + b }
fn run_op(op: Op, x: i32) -> i32 {
    match op {
        Unary(f) => f(x),
        Binary(g) => g(x, x),
        Nothing => 0,
    }
}
fn maybe(f: (fn(i32) -> i32)?, x: i32) -> i32 {
    match f { Some(g) => g(x), None => -1 }
}
fn run_pair(p: Pair) -> i32 { p.0(p.1) }
test fn fields_and_tuples() {
    let h := Handler { name: 7, run: dbl };
    assert(h.run(21) == 42);
    assert(h.name == 7);
    let record := { op: inc, base: 10 };
    assert(record.op(record.base) == 11);
    assert(run_pair((dbl, 4)) == 8);
}
test fn arrays_and_lists() {
    let table := [inc, dbl, inc];
    assert(table[0](1) == 2);
    assert(table[1](5) == 10);
    var total := 0;
    loop f in table { total += f(10); }
    assert(total == 11 + 20 + 11);
    var fs: List<fn(i32) -> i32> = [];
    fs.push(inc);
    fs.push(fn(x: i32) -> i32 => x * 100);
    assert(fs.len() == 2);
    match fs.get(1) { Some(f) => assert(f(2) == 200), None => assert(false) }
    match fs.pop() { Some(f) => assert(f(3) == 300), None => assert(false) }
    assert(fs.len() == 1);
}
test fn enums_and_options() {
    assert(run_op(Op::Unary(inc), 5) == 6);
    assert(run_op(Op::Binary(add), 5) == 10);
    assert(run_op(Op::Nothing, 5) == 0);
    assert(maybe(Some(inc), 1) == 2);
    assert(maybe(None, 1) == -1);
}
fn main() -> i32 {
    var h := Handler { name: 1, run: inc };
    h.run = dbl;
    h.run(8) + run_op(Op::Unary(inc), 1) + maybe(Some(dbl), 2)
}
"#,
        3,
        16 + 2 + 4,
        "aggregates",
    );
}

#[test]
fn function_values_are_copyable() {
    single(
        r#"fn inc(x: i32) -> i32 { x + 1 }
fn use_twice(f: fn(i32) -> i32) -> i32 {
    let a := f;
    let b := f;
    a(1) + b(2) + f(3)
}
fn main() -> i32 {
    let f := inc;
    let g := f;
    use_twice(f) + use_twice(g) + f(0)
}
"#,
        0,
        (2 + 3 + 4) * 2 + 1,
        "copyable",
    );
}

#[test]
fn named_and_imported_values_respect_visibility() {
    let f = Fixture::with(
        &[
            (
                "main",
                r#"use self::math::{triple, quad};
fn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }
fn main() -> i32 {
    apply(triple, 2) + apply(math::triple, 1) + apply(quad, 1)
        + apply(fn(y: i32) -> i32 => math::exposed(y), 1)
}
"#,
            ),
            (
                "math",
                r#"pub fn triple(x: i32) -> i32 => x * 3
pub fn quad(x: i32) -> i32 { x * 4 }
fn secret(x: i32) -> i32 => x + 1000
pub fn exposed(x: i32) -> i32 => secret(x)
"#,
            ),
        ],
        "",
    );
    verify(&f, 0, 6 + 3 + 4 + 1001, "imports");
    let private = Fixture::with(
        &[
            ("main", "fn main() -> i32 { let f := math::secret; f(1) }\n"),
            ("math", "fn secret(x: i32) -> i32 => x\n"),
        ],
        "",
    );
    let output = private.run(&["check"]);
    assert!(!output.status.success());
    assert!(
        text(&output.stderr).contains("private"),
        "{}",
        text(&output.stderr)
    );
}

#[test]
fn generic_functions_need_an_expected_type() {
    single(
        r#"fn id<T>(x: T) -> T { x }
fn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }
fn main() -> i32 {
    let f: fn(i32) -> i32 = id;
    let g: fn(bool) -> bool = id;
    let flag := if g(true) { 1 } else { 0 };
    apply(id, 10) + f(5) + flag
}
"#,
        0,
        16,
        "generic values",
    );
    rejects(
        "fn id<T>(x: T) -> T { x }\nfn main() -> i32 { let f := id; 0 }\n",
        "TE002",
        "cannot be used as a value without an expected function type",
    );
    rejects(
        "fn id<T>(x: T) -> T { x }\nfn main() -> i32 { let f: fn(i32) -> bool = id; 0 }\n",
        "TE002",
        "expected fn(i32) -> bool, found fn(i32) -> i32",
    );
    rejects(
        "fn id<T>(x: T) -> T { x }\nfn main() -> i32 { let f: fn(i32, i32) -> i32 = id; 0 }\n",
        "TE010",
        "takes 1 arguments, but the expected function type has 2",
    );
}

#[test]
fn test_functions_are_never_values_and_externs_are() {
    rejects(
        "test fn t() {}\nfn main() -> i32 { let f := t; 0 }\n",
        "NE001",
        "test functions cannot be called or used as values",
    );
    // An `extern` host function is a plain function in the backend, so it is a
    // valid value (source run only: the host import needs the CLI profile).
    let f = Fixture::with(
        &[(
            "main",
            r#"extern fn write_i32(value: i32);
fn emit(f: fn(i32), v: i32) { f(v); }
fn main() -> i32 {
    emit(write_i32, 41);
    let g := write_i32;
    g(1);
    7
}
"#,
        )],
        "[host]\nprofile = \"cli\"\n[[host.imports]]\nmodule = \"memobits:console\"\nname = \"write_i32\"\nparams = [\"i32\"]\nresult = \"unit\"\n",
    );
    let run = f.run(&["run"]);
    assert!(run.status.success(), "{}", text(&run.stderr));
    assert_eq!(
        text(&run.stdout),
        "Host i32: 41\nHost i32: 1\nResult: i32(7)\n"
    );
}

// ---------------------------------------------------------------------------
// Anonymous functions and `=>` bodies

#[test]
fn anonymous_functions_in_every_position() {
    single(
        r#"use alloc::List;
const FACTOR: i32 = 3;
type Box1 { f: fn(i32) -> i32 }
fn scale(x: i32) -> i32 => x * FACTOR
fn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }
fn make() -> fn(i32) -> i32 { fn(x: i32) -> i32 => x + 100 }
fn make_inferred() -> fn(i32) -> i32 { fn(x) => x + 200 }
test fn positions() {
    // Argument, with and without annotations.
    assert(apply(fn(x: i32) -> i32 => x + 1, 1) == 2);
    assert(apply(fn(x) => x + 2, 1) == 3);
    assert(apply(fn(x) { x + 3 }, 1) == 4);
    assert(apply(fn(x: i32) -> i32 { let y := x * 2; y + 1 }, 4) == 9);
    // Local binding, annotated or inferred from the expected type.
    let a := fn(x: i32) -> i32 => x - 1;
    let b: fn(i32) -> i32 = fn(x) => x - 2;
    assert(a(10) == 9);
    assert(b(10) == 8);
    // Result of a function.
    assert(make()(1) == 101);
    assert(make_inferred()(1) == 201);
    // Struct field, array element, List element, Option payload, tuple.
    let holder := Box1 { f: fn(x) => x * 5 };
    assert(holder.f(3) == 15);
    let table := [fn(x: i32) -> i32 => x, fn(x: i32) -> i32 => x * 2];
    assert(table[1](4) == 8);
    var fs: List<fn(i32) -> i32> = [];
    fs.push(fn(x) => x + 7);
    match fs.get(0) { Some(f) => assert(f(1) == 8), None => assert(false) }
    let maybe: (fn(i32) -> i32)? = Some(fn(x) => x * 9);
    match maybe { Some(f) => assert(f(2) == 18), None => assert(false) }
    let pair: (fn(i32) -> i32, i32) = (fn(x) => x + 1, 1);
    assert(pair.0(pair.1) == 2);
    // Constants and top-level functions are not captures.
    assert(apply(fn(x) => scale(x) + FACTOR, 2) == 9);
    // Immediately called.
    assert((fn(x: i32) -> i32 => x + 1)(5) == 6);
    // Nested.
    let nested := fn(x: i32) -> i32 { apply(fn(y) => y * 2, x) + 1 };
    assert(nested(4) == 9);
    // Reassigned.
    var current: fn(i32) -> i32 = fn(x) => x;
    assert(current(1) == 1);
    current = fn(x) => x + 10;
    assert(current(1) == 11);
}
test fn shapes() {
    let no_parameters := fn() -> i32 => 42;
    assert(no_parameters() == 42);
    let two := fn(a: i32, b: i32) -> i32 => a - b;
    assert(two(9, 4) == 5);
    let unit_result := fn(x: i32) { assert(x == 3); };
    unit_result(3);
    let early := fn(x: i32) -> i32 { if x > 5 { return 5; } x };
    assert(early(9) == 5);
    assert(early(2) == 2);
    var total := 0;
    let adder := fn(var n: i32) -> i32 { n += 1; n };
    total += adder(1);
    assert(total == 2);
}
fn main() -> i32 { apply(fn(x) => x + 40, 2) }
"#,
        2,
        42,
        "anonymous",
    );
}

#[test]
fn named_expression_bodies() {
    single(
        r#"type Point { x: i32, y: i32 }
extend Point {
    fn sum(borrow self) -> i32 => self.x + self.y
    fn scaled(borrow self, k: i32) -> i32 => self.sum() * k
    fn shift(share self, d: i32) { self.x = self.x + d; }
}
fn double(x: i32) -> i32 => x * 2
fn pair_sum(a: i32, b: i32) -> i32 => double(a) + double(b);
fn nothing() => assert(true)
test fn named_bodies() {
    assert(double(4) == 8);
    assert(pair_sum(1, 2) == 6);
    let p := Point { x: 3, y: 4 };
    assert(p.sum() == 7);
    assert(p.scaled(10) == 70);
    var q := Point { x: 1, y: 1 };
    q.shift(5);
    assert(q.x == 6);
}
test fn expression_test() => assert(double(2) == 4)
fn main() -> i32 => double(21)
"#,
        2,
        42,
        "named bodies",
    );
}

// ---------------------------------------------------------------------------
// Calls through values

#[test]
fn calls_through_fields_methods_and_groups() {
    single(
        r#"type Holder { callback: fn(i32) -> i32, n: i32 }
type Both { run: fn(i32) -> i32 }
extend Both {
    // A method of the same name wins over the field.
    fn run(borrow self, x: i32) -> i32 => x + 1000
}
fn inc(x: i32) -> i32 { x + 1 }
fn dbl(x: i32) -> i32 { x * 2 }
fn make() -> fn(i32) -> i32 { dbl }
fn choose(flag: bool) -> fn(i32) -> i32 { if flag { inc } else { dbl } }
test fn field_calls() {
    let h := Holder { callback: inc, n: 4 };
    assert(h.callback(h.n) == 5);
    var m := Holder { callback: dbl, n: 4 };
    assert(m.callback(m.n) == 8);
    m.callback = inc;
    assert(m.callback(m.n) == 5);
}
test fn method_wins() {
    let b := Both { run: dbl };
    assert(b.run(1) == 1001);
    let field_value := b.run;
    assert(field_value(4) == 8);
}
test fn element_group_and_result_calls() {
    let table := [inc, dbl];
    assert(table[0](1) == 2);
    assert(table[1](4) == 8);
    assert((make())(3) == 6);
    assert(make()(3) == 6);
    assert(choose(true)(1) + choose(false)(1) == 4);
    assert((table[1])(5) == 10);
}
test fn shadowing() {
    // A local of function type shadows a top-level function of that name.
    let inc := dbl;
    assert(inc(5) == 10);
}
fn main() -> i32 { choose(false)(21) }
"#,
        4,
        42,
        "calls",
    );
}

#[test]
fn argument_passing_follows_the_target_modes() {
    single(
        r#"type Tag { label: string, id: u32 }
fn len_of(s: borrow string) -> u32 { s.len() }
fn consume(s: string) -> u32 { s.len() }
fn id_of(t: Tag) -> u32 { t.id }
fn bump(n: share u32) { n = n + 1; }
fn make_text(n: u32) -> string { let r := "ab".concat("cd"); r }
fn make_tag(n: u32) -> Tag { Tag { label: "xy", id: n } }
fn with_borrow(f: fn(borrow string) -> u32, s: borrow string) -> u32 { f(s) }
fn with_owned(f: fn(string) -> u32) -> u32 { let s := "he".concat("llo"); f(s) }
fn with_share(f: fn(share u32), n: share u32) { f(n.share()); f(n.share()); }
fn producing(f: fn(u32) -> string) -> u32 { let s := f(3); s.len() }
fn owners(f: fn(Tag) -> u32, g: fn(u32) -> Tag) -> u32 { let t := g(7); f(t) }
test fn modes() {
    let s := "hello".concat("!");
    assert(with_borrow(len_of, s.borrow()) == 6);
    assert(with_owned(consume) == 5);
    var n: u32 = 0;
    with_share(bump, n.share());
    assert(n == 2);
    assert(producing(make_text) == 4);
    assert(owners(id_of, make_tag) == 7);
}
fn main() -> i32 { (with_owned(consume) + producing(make_text) + owners(id_of, make_tag)) as i32 }
"#,
        1,
        5 + 4 + 7,
        "modes",
    );
}

// ---------------------------------------------------------------------------
// Representation and the backend

#[test]
fn wasm_uses_a_function_table_and_call_indirect() {
    let f = Fixture::new(
        r#"fn inc(x: i32) -> i32 { x + 1 }
fn dbl(x: i32) -> i32 { x * 2 }
fn neg(x: i32) -> i32 { 0 - x }
fn flag(b: bool) -> bool { b }
fn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }
fn test_flag(f: fn(bool) -> bool) -> bool { f(true) }
fn main() -> i32 {
    let ok := if test_flag(flag) { 1 } else { 0 };
    apply(inc, 1) + apply(dbl, 2) + apply(neg, 3) + apply(fn(x) => x, 4) + ok
}
"#,
    );
    verify(&f, 0, 2 + 4 - 3 + 4 + 1, "table");
    let bytes = fs::read(f.0.join("h1.wasm")).unwrap();
    let mut tables = 0;
    let mut element_functions = 0;
    let mut call_indirect = 0;
    let mut types = std::collections::HashSet::new();
    for payload in wasmparser::Parser::new(0).parse_all(&bytes) {
        match payload.unwrap() {
            wasmparser::Payload::TableSection(section) => {
                for table in section {
                    let table = table.unwrap();
                    tables += 1;
                    // Slot 0 stays empty: one slot per function used as a
                    // value (`inc`, `dbl`, `neg`, `flag`, the anonymous one).
                    assert_eq!(table.ty.initial, 6);
                    assert_eq!(table.ty.maximum, Some(6));
                }
            }
            wasmparser::Payload::ElementSection(section) => {
                for element in section {
                    let element = element.unwrap();
                    match element.items {
                        wasmparser::ElementItems::Functions(functions) => {
                            element_functions += functions.count();
                        }
                        wasmparser::ElementItems::Expressions(..) => panic!("expected functions"),
                    }
                    match element.kind {
                        wasmparser::ElementKind::Active { offset_expr, .. } => {
                            let mut reader = offset_expr.get_operators_reader();
                            assert!(matches!(
                                reader.read().unwrap(),
                                wasmparser::Operator::I32Const { value: 1 }
                            ));
                        }
                        _ => panic!("expected an active segment at slot 1"),
                    }
                }
            }
            wasmparser::Payload::CodeSectionEntry(body) => {
                for operator in body.get_operators_reader().unwrap() {
                    if let wasmparser::Operator::CallIndirect { type_index, .. } = operator.unwrap()
                    {
                        call_indirect += 1;
                        types.insert(type_index);
                    }
                }
            }
            _ => {}
        }
    }
    assert_eq!(tables, 1);
    assert_eq!(element_functions, 5);
    // `apply` and `test_flag` each call through their parameter once; one
    // Wasm type per distinct signature.
    assert_eq!(call_indirect, 2);
    assert_eq!(types.len(), 2);

    // A program without function values has neither table nor elements.
    let plain = Fixture::new("fn main() -> i32 { 1 }\n");
    assert!(plain.run(&["build", "--output", "p.wasm"]).status.success());
    for payload in wasmparser::Parser::new(0).parse_all(&fs::read(plain.0.join("p.wasm")).unwrap())
    {
        assert!(!matches!(
            payload.unwrap(),
            wasmparser::Payload::TableSection(_) | wasmparser::Payload::ElementSection(_)
        ));
    }
}

#[test]
fn function_values_work_without_the_alloc_layer() {
    let f = Fixture::with(
        &[
            (
                "main",
                r#"use self::ops::{triple, quad};
fn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }
fn main() -> i32 { apply(triple, 2) + apply(quad, 1) + apply(fn(x) => x + 1, 1) }
"#,
            ),
            (
                "ops",
                "pub fn triple(x: i32) -> i32 => x * 3\npub fn quad(x: i32) -> i32 { x * 4 }\n",
            ),
        ],
        "[build]\nalloc = false\n",
    );
    verify(&f, 0, 6 + 4 + 2, "alloc=false");
}

#[test]
fn an_invalid_function_value_traps_with_a_report() {
    // A zero value (slot 0 is never filled) cannot be written in source, so
    // the artifact is patched: the constant `inc` slot (1) becomes 0.
    let f = Fixture::new(
        "fn inc(x: i32) -> i32 { x + 1 }\nfn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }\nfn main() -> i32 { apply(inc, 1) }\n",
    );
    assert!(f.run(&["build", "--output", "t.wasm"]).status.success());
    let mut bytes = fs::read(f.0.join("t.wasm")).unwrap();
    // `i64.const 1` (0x42 0x01) is the only i64 constant in this module.
    let at = bytes
        .windows(2)
        .position(|pair| pair == [0x42, 0x01])
        .expect("function value constant");
    bytes[at + 1] = 0x00;
    fs::write(f.0.join("t.wasm"), bytes).unwrap();
    let run = f.run(&["run", "t.wasm"]);
    assert!(!run.status.success());
    assert!(
        text(&run.stderr).contains("call through an invalid function value"),
        "{}",
        text(&run.stderr)
    );
}

// ---------------------------------------------------------------------------
// Exact cleanup of owners passed through function values

const ITERATIONS: u32 = 4_096;
const TEXT_BYTES: usize = 1_024;

fn read_uleb(bytes: &[u8], cursor: &mut usize) -> u32 {
    let mut value = 0;
    let mut shift = 0;
    loop {
        let byte = bytes[*cursor];
        *cursor += 1;
        value |= u32::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return value;
        }
        shift += 7;
        assert!(shift < 35, "invalid Wasm LEB128");
    }
}

fn write_uleb(mut value: u32, output: &mut Vec<u8>) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        output.push(byte);
        if value == 0 {
            break;
        }
    }
}

/// Lower the memory maximum to the initial size plus one page, so repeated
/// iterations must reuse released String blocks.
fn cap_memory(bytes: &[u8]) -> (Vec<u8>, u32, u32) {
    assert_eq!(&bytes[..8], b"\0asm\x01\0\0\0");
    let mut module = bytes[..8].to_vec();
    let mut section_start = 8;
    let mut result = None;
    while section_start < bytes.len() {
        let id = bytes[section_start];
        let mut header_cursor = section_start + 1;
        let payload_len = read_uleb(bytes, &mut header_cursor) as usize;
        let payload_start = header_cursor;
        let section_end = payload_start + payload_len;
        if id != 5 {
            module.extend_from_slice(&bytes[section_start..section_end]);
        } else {
            let mut cursor = payload_start;
            assert_eq!(read_uleb(bytes, &mut cursor), 1, "expected one memory");
            let limits = read_uleb(bytes, &mut cursor);
            assert_ne!(limits & 1, 0, "expected a declared maximum");
            let initial = read_uleb(bytes, &mut cursor);
            let maximum_start = cursor;
            let old_maximum = read_uleb(bytes, &mut cursor);
            let new_maximum = initial + 1;
            assert!(new_maximum <= old_maximum);
            let mut payload = bytes[payload_start..maximum_start].to_vec();
            write_uleb(new_maximum, &mut payload);
            payload.extend_from_slice(&bytes[cursor..section_end]);
            module.push(id);
            write_uleb(payload.len() as u32, &mut module);
            module.extend_from_slice(&payload);
            result = Some((initial, new_maximum));
        }
        section_start = section_end;
    }
    let (initial, maximum) = result.expect("Wasm memory section");
    (module, initial, maximum)
}

#[test]
fn owners_through_function_values_release_exactly_under_capped_memory() {
    let text_value = "x".repeat(TEXT_BYTES);
    let source = r#"type Label { text: string, n: u32 }
type Outer { inner: Label, k: u32 }
fn take_string(s: string) -> u32 { s.len() }
fn take_label(l: Label) -> u32 { l.n + l.text.len() }
fn take_outer(o: Outer) -> u32 { o.k + o.inner.text.len() }
fn peek(s: borrow string) -> u32 { s.len() }
fn make_string(n: u32) -> string { let r := "TEXT".concat(""); r }
fn make_label(n: u32) -> Label { let t := "TEXT".concat(""); Label { text: t, n: n } }
fn drop_all(s: string, n: u32) -> u32 { n }
fn call_string(f: fn(string) -> u32) -> u32 {
    let t := "TEXT".concat("");
    f(t)
}
fn call_label(f: fn(Label) -> u32) -> u32 {
    let t := "TEXT".concat("");
    f(Label { text: t, n: 3 })
}
fn call_outer(f: fn(Outer) -> u32) -> u32 {
    let t := "TEXT".concat("");
    f(Outer { inner: Label { text: t, n: 2 }, k: 5 })
}
fn call_borrow(f: fn(borrow string) -> u32) -> u32 {
    let t := "TEXT".concat("");
    f(t.borrow())
}
fn produce_string(f: fn(u32) -> string) -> u32 {
    let s := f(1);
    s.len()
}
fn produce_label(f: fn(u32) -> Label) -> u32 {
    let l := f(4);
    l.n + l.text.len()
}
fn discard_result(f: fn(u32) -> string) -> u32 {
    let s := f(1);
    drop(s);
    9
}
fn two_arguments(f: fn(string, u32) -> u32) -> u32 {
    let t := "TEXT".concat("");
    f(t, 6)
}
fn early(f: fn(string) -> u32, flag: bool) -> u32 {
    let t := "TEXT".concat("");
    let u := "TEXT".concat("");
    if flag { return f(t); }
    f(t) + f(u)
}
fn round() -> u32 {
    call_string(take_string)
        + call_label(take_label)
        + call_outer(take_outer)
        + call_borrow(peek)
        + produce_string(make_string)
        + produce_label(make_label)
        + discard_result(make_string)
        + two_arguments(drop_all)
        + early(take_string, true)
        + early(take_string, false)
        + call_string(fn(s: string) -> u32 => s.len() + 1)
        + produce_string(fn(n: u32) -> string { let r := "TEXT".concat(""); r })
}
fn main() -> u32 {
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {
        if iteration == ITERATIONS { break; }
        total += round();
        iteration += 1;
    }
    total
}
"#
    .replace("TEXT", &text_value)
    .replace("ITERATIONS", &ITERATIONS.to_string());
    let f = Fixture::new(&source);
    // 4096-byte stack keeps the frame small so the heap dominates memory.
    fs::write(
        f.0.join("project.toml"),
        "[package]\nname='h1'\nentry='main::main'\n[build]\nstack_size=4096\n",
    )
    .unwrap();
    let t = TEXT_BYTES as u64;
    let per_round = t // call_string
        + (3 + t) // call_label
        + (5 + t) // call_outer
        + t // call_borrow
        + t // produce_string
        + (4 + t) // produce_label
        + 9 // discard_result
        + 6 // two_arguments
        + t // early true
        + 2 * t // early false
        + (t + 1) // anonymous consumer
        + t; // anonymous producer
    let expected = per_round * u64::from(ITERATIONS);
    let source_run = f.run(&["run"]);
    assert!(
        source_run.status.success(),
        "source run: {}",
        text(&source_run.stderr)
    );
    assert_eq!(
        text(&source_run.stdout),
        format!("Result: u32({expected})\n")
    );
    let build = f.run(&["build", "--output", "owners.wasm"]);
    assert!(build.status.success(), "{}", text(&build.stderr));
    let wasm = f.run(&["run", "owners.wasm"]);
    assert!(wasm.status.success(), "wasm run: {}", text(&wasm.stderr));
    assert_eq!(text(&wasm.stdout), format!("Result: i32({expected})\n"));
    let path = f.0.join("owners.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&path).unwrap());
    fs::write(&path, capped).unwrap();
    let wasm = f.run(&["run", "owners.wasm"]);
    assert!(
        wasm.status.success(),
        "capped Wasm run failed: {}",
        text(&wasm.stderr)
    );
    assert_eq!(text(&wasm.stdout), format!("Result: i32({expected})\n"));
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(&path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

// ---------------------------------------------------------------------------
// Negative cases

#[test]
fn captures_are_rejected_until_the_next_step() {
    rejects(
        "fn main() -> i32 { let n := 5; let f := fn(x: i32) -> i32 => x + n; f(1) }\n",
        "TE017",
        "closures that capture variables arrive in the next step",
    );
    rejects(
        "fn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }\nfn outer(k: i32) -> i32 { apply(fn(x) => x + k, 1) }\nfn main() -> i32 { outer(1) }\n",
        "TE017",
        "uses 'k' from the enclosing function",
    );
    rejects(
        "fn main() -> i32 { var n := 1; let f := fn() { n = 2; }; f(); n }\n",
        "TE017",
        "uses 'n' from the enclosing function",
    );
    rejects(
        "fn main() -> i32 { let a := 1; let f := fn(x: i32) -> i32 { let g := fn(y: i32) -> i32 => y + a; g(x) }; f(1) }\n",
        "TE017",
        "uses 'a' from the enclosing function",
    );
    // Borrow and share function parameters belong to the closure step.
    rejects(
        "fn call(f: borrow fn(i32) -> i32) -> i32 { f(1) }\nfn main() -> i32 { 0 }\n",
        "TE017",
        "borrow or share function parameter",
    );
}

#[test]
fn mismatches_and_misuse_are_diagnosed() {
    let prelude =
        "fn inc(x: i32) -> i32 { x + 1 }\nfn len_of(s: borrow string) -> u32 { s.len() }\n";
    for (body, code, needle) in [
        (
            "let f := inc; f(1, 2)",
            "TE010",
            "expected 1 arguments, found 2",
        ),
        ("let f := inc; f(true)", "TE002", "expected i32, found bool"),
        (
            "let f: fn(string) -> u32 = len_of; 0",
            "TE002",
            "expected fn(string) -> u32, found fn(borrow string) -> u32",
        ),
        (
            "let f: fn(i32) -> bool = inc; 0",
            "TE002",
            "expected fn(i32) -> bool, found fn(i32) -> i32",
        ),
        (
            "let f: fn(i32, i32) -> i32 = fn(x) => x; 0",
            "TE010",
            "expected a function with 2 parameters, found 1",
        ),
        (
            "let f := fn(x) => x; 0",
            "TE002",
            "cannot infer the type of parameter 'x'",
        ),
        (
            "let f := inc; let g := inc; if f == g { 1 } else { 2 }",
            "TE007",
            "function values cannot be compared",
        ),
        (
            "let f := inc; let g := inc; if f != g { 1 } else { 2 }",
            "TE007",
            "no equality",
        ),
        ("let f := nosuch; 0", "NE001", "unknown name 'nosuch'"),
        (
            "let f := inc; f + 1",
            "TE007",
            "arithmetic requires numbers",
        ),
        ("let n := 3; n(1)", "TE011", "not callable"),
        (
            "let f := fn(x: i32) -> i32 => x; let y: i32 = f; y",
            "TE002",
            "expected i32, found fn(i32) -> i32",
        ),
        (
            "let f := fn(x: i32) -> bool => x; 0",
            "TE002",
            "expected bool, found i32",
        ),
    ] {
        rejects(
            &format!("{prelude}fn main() -> i32 {{ {body} }}\n"),
            code,
            needle,
        );
    }
}

#[test]
fn function_values_cannot_cross_the_exported_boundary() {
    for source in ["fn inc(x: i32) -> i32 { x + 1 }\nfn main() -> fn(i32) -> i32 { inc }\n"] {
        let f = Fixture::new(source);
        let build = f.run(&["build", "--output", "x.wasm"]);
        assert!(!build.status.success());
        let stderr = text(&build.stderr);
        assert!(
            stderr.contains("LE900") && stderr.contains("cannot use function values"),
            "{stderr}"
        );
    }
    let f = Fixture::with(
        &[(
            "main",
            "pub fn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }\nfn main() -> i32 { 0 }\n",
        )],
        "[export]\napply = \"main::apply\"\n",
    );
    let build = f.run(&["build", "--lib", "--output", "x.wasm"]);
    assert!(!build.status.success());
    assert!(
        text(&build.stderr).contains("cannot use function values"),
        "{}",
        text(&build.stderr)
    );
}
