//! H5b: uniform function value ownership and `var fn(...)`.
//!
//! Every function value (`fn(...)` and `var fn(...)`) is a move-only owner with
//! a nullable environment, whatever else the program contains. A closure that
//! mutates a captured variable is accepted only where the type is `var fn`, and
//! a `var fn` value is called through a mutable place. Every positive program
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
        Self::modules(&[("main", source)], "")
    }

    fn with(source: &str, extra_manifest: &str) -> Self {
        Self::modules(&[("main", source)], extra_manifest)
    }

    fn modules(files: &[(&str, &str)], extra_manifest: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-h5b-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            format!("[package]\nname='h5b'\nentry='main::main'\n{extra_manifest}"),
        )
        .unwrap();
        for (name, source) in files {
            fs::write(path.join("src").join(format!("{name}.mb")), source).unwrap();
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

/// `check --tests` fails; returns stderr.
fn failure(f: &Fixture, source: &str) -> String {
    let output = f.run(&["check", "--tests"]);
    let stderr = text(&output.stderr);
    assert!(!output.status.success(), "accepted:\n{source}");
    stderr
}

/// `check --tests` must fail with `code` and a message containing `needle`.
fn rejects(source: &str, code: &str, needle: &str) {
    let stderr = failure(&Fixture::new(source), source);
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
    let build = f.run(&["build", "--output", "h5b.wasm"]);
    assert!(build.status.success(), "{label}: {}", text(&build.stderr));
    let wasm = f.run(&["run", "h5b.wasm"]);
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

const ITERATIONS: u32 = 4_096;
const BASE_TEXT: usize = 1_024;

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

// ---------------------------------------------------------------------------
// One representation everywhere

/// A module with a capturing closure of the signature `fn(i32) -> i32` must not
/// change what another module may do with function values of that signature
/// (the rejected H5 design chose the representation per exact type for the
/// whole program).
#[test]
fn a_capturing_closure_in_another_module_changes_nothing() {
    let owner = "pub fn adder(n: i32) -> fn(i32) -> i32 { fn(x) => x + n }\n";
    let main_with = |extra: &str| {
        format!("{extra}fn inc(x: i32) -> i32 {{ x + 1 }}\nfn main() -> i32 {{ 0 }}\n")
    };
    // The same rejected programs, with and without the capturing module.
    let negatives = [
        (
            "use alloc::List;\nfn probe() -> i32 { var fs: List<fn(i32) -> i32> = []; fs.push(inc); match fs.get(0) { Some(h) => 1, None => 0 } }\n",
            "TE022",
        ),
        (
            "fn probe() -> i32 { let f := inc; let g := f; f(1) + g(1) }\n",
            "BE001",
        ),
        (
            "fn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }\nfn probe() -> i32 { let f := inc; apply(f, 1) + apply(f, 2) }\n",
            "BE001",
        ),
    ];
    for (probe, code) in negatives {
        let alone = Fixture::modules(&[("main", &main_with(probe))], "");
        let alone_err = failure(&alone, probe);
        assert!(alone_err.contains(code), "{alone_err}");
        let probe_module = format!("use a;\n{probe}");
        let with_owner = Fixture::modules(&[("a", owner), ("main", &main_with(&probe_module))], "");
        let with_err = failure(&with_owner, probe);
        assert!(with_err.contains(code), "{with_err}");
        // Same diagnostics (codes and messages) in both projects.
        let lines = |err: &str| {
            err.lines()
                .filter(|line| line.starts_with("error["))
                .map(str::to_owned)
                .collect::<Vec<_>>()
        };
        assert_eq!(lines(&alone_err), lines(&with_err), "{probe}");
    }
    // A program that lends a plain function and calls a stored one in place is
    // accepted and gives the same result with and without the other module.
    let positive = "use alloc::List;\nfn inc(x: i32) -> i32 { x + 1 }\nfn probe(f: borrow fn(i32) -> i32) -> i32 { f(1) + f(2) }\nfn main() -> i32 {\n    let f := inc;\n    var fs: List<fn(i32) -> i32> = [];\n    fs.push(inc);\n    probe(f) + probe(f) + fs[0](1) + probe(inc) + 25\n}\n";
    verify(&Fixture::new(positive), 0, 42, "alone");
    let with_use = format!("use a;\n{positive}");
    verify(
        &Fixture::modules(&[("a", owner), ("main", &with_use)], ""),
        0,
        42,
        "with another module's closure",
    );
    // The capturing module itself still works when used.
    let user = "use a;\nfn main() -> i32 { a::adder(40)(2) }\n";
    verify(
        &Fixture::modules(&[("a", owner), ("main", user)], ""),
        0,
        42,
        "owner module in use",
    );
}

#[test]
fn plain_values_are_move_only_with_fresh_values_per_mention() {
    // A name or non-capturing literal is a fresh value at each mention.
    single(
        r#"fn inc(x: i32) -> i32 { x + 1 }
fn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }
fn main() -> i32 {
    let a := inc;
    let b := inc;
    let lit1 := fn(x: i32) -> i32 => x + 2;
    apply(inc, 1) + apply(inc, 2) + a(3) + b(4) + apply(fn(x) => x * 2, 5) + lit1(1) + apply(a, 1) + 13
}
"#,
        0,
        // 2 + 3 + 4 + 5 + 10 + 3 + 2 + 13 = 42.
        42,
        "fresh values",
    );
    let prelude = "use alloc::List;\ntype H { run: fn(i32) -> i32 }\nfn inc(x: i32) -> i32 { x + 1 }\nfn dbl(x: i32) -> i32 { x * 2 }\nfn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }\nfn borrowed(f: borrow fn(i32) -> i32, x: i32) -> i32 { f(x) }\n";
    for (body, code) in [
        // Use after a move of a stored value.
        ("let f := inc; let g := f; f(1) + g(1)", "BE001"),
        ("let f := inc; apply(f, 1) + apply(f, 2)", "BE001"),
        ("let f := inc; let a := [f, f]; 0", "BE001"),
        ("let f := inc; let h := H { run: f }; f(1) + h.run(1)", "BE001"),
        (
            "let f := inc; let h := H { run: f }; let k := H { run: f }; 0",
            "BE001",
        ),
        // A stored value leaves a field or List only through `replace`,
        // `swap`, `pop` or `unbox`.
        ("let h := H { run: inc }; let f := h.run; f(1)", "TE022"),
        (
            "var fs: List<fn(i32) -> i32> = []; fs.push(inc); match fs.get(0) { Some(f) => f(1), None => 0 }",
            "TE022",
        ),
        // A whole function value is replaced, not assigned.
        ("var f := inc; f = dbl; f(1)", "TE018"),
    ] {
        let source = format!("{prelude}fn main() -> i32 {{ {body} }}\n");
        let stderr = failure(&Fixture::new(&source), &source);
        assert!(stderr.contains(code), "{body}: expected {code}\n{stderr}");
    }
    // The permitted ways out and around.
    single(
        &format!(
            "{prelude}fn main() -> i32 {{
    let f := inc;
    var h := H {{ run: dbl }};
    let old := replace(h.run, inc);
    var fs: List<fn(i32) -> i32> = [];
    fs.push(inc);
    fs.push(dbl);
    let last := match fs.pop() {{ Some(g) => g(10), None => 0 }};
    var slot := inc;
    let before := replace(slot, dbl);
    // lend, call in place, and fresh values
    borrowed(f, 1) + borrowed(f, 2) + f(3) + h.run(4) + old(5) + last + before(1) + slot(1) + fs[0](0) - 7
}}\n"
        ),
        0,
        // 2 + 3 + 4 + 5 + 10 + 20 + 2 + 2 + 1 = 49; 49 - 7 = 42.
        42,
        "ways around",
    );
}

// ---------------------------------------------------------------------------
// `var fn(...)`

#[test]
fn var_fn_types_in_every_position_and_calls_through_mutable_places() {
    // `var fn` as a result, parameter, `let` annotation, struct field, List and
    // array element, enum payload, `T?` and generic result; called through a
    // `var` local, a `share fn` parameter, a field or element of a `var`
    // owner, and a temporary; `fn` converts to `var fn` and both lend to
    // `share fn` (a `fn` also to `borrow fn`).
    let source = r#"use alloc::List;
fn inc(x: i32) -> i32 { x + 1 }
fn counter(start: i32) -> var fn() -> i32 {
    var c := start;
    fn() -> i32 { c += 1; c }
}
fn reader(n: i32) -> fn() -> i32 { fn() -> i32 => n }
fn run_twice(var f: var fn() -> i32) -> i32 { f() + f() }
fn through_share(f: share fn() -> i32) -> i32 { f() + f() }
fn through_borrow(f: borrow fn() -> i32) -> i32 { f() + f() }
type Slot { run: var fn() -> i32 }
type Step [ Run(var fn() -> i32), Skip ]
type Plain [ Run(fn() -> i32), Skip ]
fn is_run(step: Step) -> bool { match step { Run(f) => true, Skip => false } }
fn has_value(m: (var fn() -> i32)?) -> bool { match m { Some(f) => true, None => false } }
fn call_plain(p: Plain) -> i32 { match p { Run(f) => f(), Skip => 0 } }
fn maybe(flag: bool) -> (var fn() -> i32)? {
    if flag { Some(counter(100)) } else { None }
}
fn hold<T>(value: T) -> var fn() -> T { fn() -> T => value }
fn pass<T>(f: var fn() -> T) -> var fn() -> T { f }
fn adder(n: i32) -> var fn(i32) -> i32 { fn(x) => x + n }
test fn let_return_and_parameter_positions() {
    var c := counter(0);
    assert(c() == 1);
    assert(c() == 2);
    assert(run_twice(counter(10)) == 23);
    // A temporary is a mutable place.
    assert(counter(5)() == 6);
    let annotated: var fn() -> i32 = counter(20);
    var moved := annotated;
    assert(moved() == 21);
}
test fn share_parameters_and_lending() {
    var c := counter(0);
    assert(through_share(c) == 3);
    assert(through_share(c) == 7);
    assert(c() == 5);
    // A `fn` value is lent to `borrow fn` and `share fn` parameters.
    let r := reader(4);
    assert(through_borrow(r) == 8);
    assert(through_share(r) == 8);
    assert(r() == 4);
    // A `var fn` is lent to a `share fn`, a closure literal that reads goes to either.
    let k := 3;
    assert(through_borrow(fn() -> i32 => k) == 6);
}
test fn fn_coerces_to_var_fn() {
    let r := reader(7);
    let widened: var fn() -> i32 = r;
    var w := widened;
    assert(w() == 7);
    assert(run_twice(reader(2)) == 4);
    let h := hold(9);
    var hv := h;
    assert(hv() == 9);
    var passed := pass(counter(40));
    assert(passed() == 41);
    var add := adder(3);
    assert(add(4) == 7);
}
test fn var_fn_in_fields_elements_and_options() {
    var slot := Slot { run: counter(30) };
    assert((slot.run)() == 31);
    assert(slot.run() == 32);
    var list: List<var fn() -> i32> = [];
    list.push(counter(50));
    list.push(counter(60));
    assert(list[0]() == 51);
    assert(list[0]() == 52);
    assert(list[1]() == 61);
    var array := [counter(70), counter(80)];
    assert(array[1]() == 81);
    // Payload bindings are read-only places: a `var fn` payload is moved
    // around and dropped, and a plain `fn` payload is called.
    let step := Step::Run(counter(90));
    assert(is_run(step));
    let m := maybe(true);
    assert(has_value(m));
    assert(!has_value(maybe(false)));
    let plain := Plain::Run(reader(5));
    assert(call_plain(plain) == 5);
}
fn main() -> i32 {
    var c := counter(39);
    c() + c() - 39
}
"#;
    single(source, 4, 42, "var fn matrix");
}

/// Programs that must be rejected, with the code and a fragment of the message.
const PRELUDE: &str = "use alloc::List;
fn counter() -> var fn() -> i32 { var c := 0; fn() -> i32 { c += 1; c } }
fn reader() -> fn() -> i32 { fn() -> i32 => 1 }
fn read(f: borrow fn() -> i32) -> i32 { f() }
fn bump(f: share fn() -> i32) -> i32 { f() }
type H { run: var fn() -> i32 }
";

fn rejects_with_prelude(items: &str, body: &str, code: &str, needle: &str) {
    let source = format!("{PRELUDE}{items}\nfn main() -> i32 {{ {body} }}\n");
    rejects(&source, code, needle);
}

#[test]
fn a_mutating_closure_needs_a_var_fn_position() {
    // In a `fn(...)` position (result, annotated let, argument, field) the
    // error names the captured variable and suggests `var fn(...)`.
    for (items, body) in [
        (
            "fn make() -> fn() -> i32 { var n := 0; fn() -> i32 { n += 1; n } }",
            "make()()",
        ),
        (
            "",
            "var n := 1; let c: fn() -> i32 = fn() -> i32 { n += 1; n }; 0",
        ),
        (
            "fn take(f: fn() -> i32) -> i32 { f() }",
            "var n := 1; take(fn() -> i32 { n += 1; n })",
        ),
        (
            "type G { run: fn() -> i32 }",
            "var s := \"a\".concat(\"b\"); let g := G { run: fn() -> i32 { s.push_str(\"c\"); 1 } }; 0",
        ),
        (
            // A closure that calls a captured `var fn` mutates its environment.
            "fn wrap(f: var fn() -> i32) -> fn() -> i32 { fn() -> i32 { f() } }",
            "0",
        ),
    ] {
        let source = format!("{PRELUDE}{items}\nfn main() -> i32 {{ {body} }}\n");
        let stderr = failure(&Fixture::new(&source), &source);
        assert!(
            stderr.contains("TE017")
                && stderr.contains("changes its captured state")
                && stderr.contains("var fn(...)"),
            "{source}\n{stderr}"
        );
    }
    // The same closures are accepted in `var fn` positions, and a closure that
    // only reads is accepted in either.
    single(
        "fn make() -> var fn() -> i32 { var n := 0; fn() -> i32 { n += 1; n } }\nfn wrap(f: var fn() -> i32) -> var fn() -> i32 { fn() -> i32 { f() } }\nfn main() -> i32 { var w := wrap(make()); w() + w() + 39 }\n",
        0,
        42,
        "var positions",
    );
}

#[test]
fn calling_a_var_fn_needs_a_mutable_place_at_compile_time() {
    for (items, body, needle) in [
        ("", "let c := counter(); c()", "needs a mutable place"),
        (
            "",
            "let c: var fn() -> i32 = counter(); c()",
            "needs a mutable place",
        ),
        (
            "fn once(f: var fn() -> i32) -> i32 { f() }",
            "once(counter())",
            "needs a mutable place",
        ),
        (
            "",
            "let h := H { run: counter() }; h.run()",
            "needs a mutable place",
        ),
        (
            "fn peek(h: borrow H) -> i32 { h.run() }",
            "0",
            "needs a mutable place",
        ),
        (
            "fn elem(l: borrow List<var fn() -> i32>) -> i32 { l[0]() }",
            "0",
            "needs a mutable place",
        ),
        ("", "let c := counter(); bump(c)", "needs a mutable place"),
    ] {
        let source = format!("{PRELUDE}{items}\nfn main() -> i32 {{ {body} }}\n");
        let stderr = failure(&Fixture::new(&source), &source);
        assert!(
            stderr.contains("TE004") && stderr.contains(needle),
            "{source}\n{stderr}"
        );
        // A compile error: there is no run-time trap to reach.
        assert!(!stderr.contains("TR0"), "{stderr}");
    }
}

#[test]
fn var_fn_coercions_and_lending_rules() {
    // `fn` to `var fn` is accepted (checked in the positive matrix); the
    // reverse is rejected at every kind of position.
    for (items, body) in [
        ("", "let c: fn() -> i32 = counter(); 0"),
        ("fn take(f: fn() -> i32) -> i32 { 0 }", "take(counter())"),
        ("", "let l: List<fn() -> i32> = [counter()]; 0"),
        ("fn give() -> fn() -> i32 { counter() }", "0"),
        (
            "type G { run: fn() -> i32 }",
            "let g := G { run: counter() }; 0",
        ),
    ] {
        let source = format!("{PRELUDE}{items}\nfn main() -> i32 {{ {body} }}\n");
        let stderr = failure(&Fixture::new(&source), &source);
        assert!(
            stderr.contains("TE002") && stderr.contains("found var fn() -> i32"),
            "{source}\n{stderr}"
        );
    }
    // A `var fn` is never lent to `borrow fn`, directly or through a parameter.
    rejects_with_prelude(
        "",
        "var c := counter(); read(c)",
        "TE017",
        "only be lent to a `share fn`",
    );
    rejects_with_prelude(
        "fn go(var f: var fn() -> i32) -> i32 { read(f) }",
        "0",
        "TE017",
        "only be lent to a `share fn`",
    );
    rejects_with_prelude(
        "fn go(f: share fn() -> i32) -> i32 { read(f) }",
        "0",
        "TE017",
        "share fn",
    );
    // Lending to `share fn` needs a mutable lender.
    rejects_with_prelude("", "let c := counter(); bump(c)", "TE004", "mutable place");
    // `borrow`/`share` parameters are written `borrow fn` / `share fn`.
    rejects_with_prelude(
        "fn weird(g: borrow var fn() -> i32) -> i32 { 0 }",
        "0",
        "TE017",
        "is the type of an owned value",
    );
    // A stored `var fn` leaves a List only through the owner rules.
    rejects_with_prelude(
        "",
        "var l: List<var fn() -> i32> = []; l.push(counter()); match l.get(0) { Some(f) => 1, None => 0 }",
        "TE022",
        "get() copies",
    );
    // Accepted: `fn` lent to `borrow fn` and `share fn`, `var fn` to `share fn`
    // from a mutable lender, a read-only closure literal to `var fn`.
    single(
        &format!(
            "{PRELUDE}fn main() -> i32 {{ let r := reader(); var c := counter(); read(r) + bump(r) + bump(c) + bump(c) + 37 }}\n"
        ),
        0,
        42,
        "lending",
    );
}

// ---------------------------------------------------------------------------
// Heap environments under capped memory

fn capped_program(extra: &str, clear: &str) -> String {
    let text = "x".repeat(BASE_TEXT);
    format!(
        r#"use alloc::List;
type Slot {{ name: string, run: var fn() -> u32 }}
fn by_text(text: string) -> fn() -> u32 {{ fn() -> u32 => text.len() }}
fn counting(text: string) -> var fn() -> u32 {{
    var seen: u32 = 0;
    fn() -> u32 {{ seen += text.len(); seen }}
}}
fn growing(text: string) -> var fn() -> u32 {{
    var s := text;
    fn() -> u32 {{ s.push_str("ab"); s.len() }}
}}
fn widened(text: string) -> var fn() -> u32 {{ by_text(text) }}
fn round(keep: share List<var fn() -> u32>, early: bool) -> u32 {{
    var c := counting("{text}".concat(""));
    var g := growing("{text}".concat(""));
    var slot := Slot {{ name: "{text}".concat(""), run: counting("{text}".concat("")) }};
    var fs: List<var fn() -> u32> = [];
    fs.push(counting("{text}".concat("")));
    var w := widened("{text}".concat(""));
    var swap := counting("{text}".concat(""));
    var old := replace(swap, counting("{text}".concat("")));
    var arrays := [counting("{text}".concat("")), counting("{text}".concat(""))];
    {extra}
    let n := c() + c() + g() + (slot.run)() + fs[0]() + w() + old() + swap() + arrays[1]();
    if early {{ return n; }}
    n + slot.name.len()
}}
fn main() -> u32 {{
    var keep: List<var fn() -> u32> = [];
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {{
        if iteration == {ITERATIONS} {{ break; }}
        total += round(keep.share(), iteration % 2 == 0);
        {clear}
        iteration += 1;
    }}
    total
}}
"#
    )
}

fn run_capped(source: &str) -> (Fixture, Output) {
    let f = Fixture::with(source, "[build]\nstack_size=4096\n");
    let build = f.run(&["build", "--output", "capped.wasm"]);
    assert!(build.status.success(), "{}", text(&build.stderr));
    let path = f.0.join("capped.wasm");
    let (capped, _, _) = cap_memory(&fs::read(&path).unwrap());
    fs::write(&path, capped).unwrap();
    let output = f.run(&["run", "capped.wasm"]);
    (f, output)
}

#[test]
fn heap_environments_release_exactly_under_capped_memory() {
    // Per round: c() = t then 2t, g() = t + 2, and slot.run, fs[0], w, old,
    // swap and arrays[1] are t each: 3t + t + 2 + 6t = 10t + 2. An early round
    // returns that, the others add the name (t).
    let t = BASE_TEXT as u64;
    let early = 10 * t + 2;
    let late = early + t;
    let rounds = u64::from(ITERATIONS);
    let expected = (rounds / 2) * early + (rounds / 2) * late;
    let source = capped_program("", "");
    let f = Fixture::with(&source, "[build]\nstack_size=4096\n");
    let run = f.run(&["run"]);
    assert!(run.status.success(), "source run: {}", text(&run.stderr));
    assert_eq!(text(&run.stdout), format!("Result: u32({expected})\n"));
    let (f, capped) = run_capped(&source);
    assert!(
        capped.status.success() && capped.stderr.is_empty(),
        "capped Wasm run failed: {}",
        text(&capped.stderr)
    );
    assert_eq!(text(&capped.stdout), format!("Result: i32({expected})\n"));
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(f.0.join("capped.wasm")).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.maximum, Some(memory.initial + 1));
}

#[test]
fn mutation_check_keeping_a_var_fn_per_round_exhausts_the_capped_memory() {
    // Every round moves a fresh closure with a heap String into a List that is
    // never emptied: the cap must trap, so the clean run above really measures
    // the release of environments.
    let text_value = "x".repeat(BASE_TEXT);
    let keep = format!(r#"keep.push(counting("{text_value}".concat("")));"#);
    let (_f, kept) = run_capped(&capped_program(&keep, ""));
    assert!(!kept.status.success(), "{kept:?}");
    assert!(
        text(&kept.stderr).contains("guest heap allocation failed"),
        "{}",
        text(&kept.stderr)
    );
    // With the clear restored the same shape runs clean.
    let (_f, cleared) = run_capped(&capped_program(&keep, "keep.clear();"));
    assert!(
        cleared.status.success() && cleared.stderr.is_empty(),
        "{}",
        text(&cleared.stderr)
    );
}
