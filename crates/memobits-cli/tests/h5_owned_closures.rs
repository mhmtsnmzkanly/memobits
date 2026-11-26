//! H5: owned (escaping) closures.
//!
//! An anonymous function written where an owned `fn(...)` value is expected
//! may capture variables by move. The captures live in a heap environment
//! owned by the function value; moving, storing, returning, replacing and
//! dropping the value releases the environment exactly once. Every positive
//! program runs from source and as a standalone Wasm artifact.
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
        Self::with(source, "")
    }

    fn with(source: &str, extra_manifest: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-h5-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            format!("[package]\nname='h5'\nentry='main::main'\n{extra_manifest}"),
        )
        .unwrap();
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

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// `check --tests` must fail with `code` and a message containing `needle`.
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
    let build = f.run(&["build", "--output", "h5.wasm"]);
    assert!(build.status.success(), "{label}: {}", text(&build.stderr));
    let wasm = f.run(&["run", "h5.wasm"]);
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

// ---------------------------------------------------------------------------
// Typical uses

#[test]
fn adders_counters_and_captured_strings_work() {
    // adder: 15; counter: c() = 1, 2, 3 -> 3; greeter: "hello!".len() = 6;
    // button: label "okk" and callback "abcd".len() = 4; bound closure with a
    // string and a number: 3 + 4 = 7.
    // 3 + 15 + 10 + 3 + 7 + 4 = 42.
    let source = r#"fn make_adder(n: i32) -> fn(i32) -> i32 { fn(x) => x + n }
fn make_counter() -> var fn() -> i32 {
    var c := 0;
    fn() -> i32 { c += 1; c }
}
fn greeter(name: string) -> fn() -> u32 { fn() -> u32 => name.len() }
type Button { label: string, on_click: fn() -> u32 }
fn main() -> i32 {
    var c := make_counter();
    c();
    c();
    let three := c();
    let add := make_adder(10);
    let a := add(5);
    let g := greeter("hello".concat("!"));
    let button := Button { label: "ok".concat("k"), on_click: greeter("abc".concat("d")) };
    let n := (button.on_click)() + g();
    let word := "xyz".concat("w");
    let bound: fn(i32) -> i32 = fn(x) => x + word.len() as i32;
    three + a + n as i32 + button.label.len() as i32 + bound(3) + 4
}
"#;
    single(source, 0, 42, "typical uses");
}

#[test]
fn owned_closures_work_in_every_owned_position() {
    // Annotated let, return value, struct field, List element, array element,
    // Option, owned parameter, tuple field, enum payload, composition,
    // generic helper, replacement.
    let source = r#"use alloc::List;
fn adder(n: i32) -> fn(i32) -> i32 { fn(x) => x + n }
fn compose(f: fn(i32) -> i32, g: fn(i32) -> i32) -> fn(i32) -> i32 { fn(x) => g(f(x)) }
fn call_owned(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }
fn constant<T>(value: T) -> fn() -> T { fn() -> T => value }
type Holder { run: fn(i32) -> i32, tag: string }
type Step [ Run(fn(i32) -> i32), Skip ]
fn maybe(flag: bool) -> (fn(i32) -> i32)? {
    let k := 4;
    if flag { Some(fn(x) => x * k) } else { None }
}
fn pick(step: Step, x: i32) -> i32 {
    match step { Run(f) => f(x), Skip => 0 }
}
fn main() -> i32 {
    let k := 10;
    let local: fn(i32) -> i32 = fn(x) => x + k;
    let r1 := local(1);
    let r2 := adder(10)(2);
    let holder := Holder { run: adder(10), tag: "t".concat("g") };
    let r3 := (holder.run)(3);
    var list: List<fn(i32) -> i32> = [];
    list.push(adder(10));
    list.push(fn(x) => x + k + 1);
    let r4 := list[0](4) + list[1](4);
    let array := [adder(10), adder(11)];
    let r5 := array[1](5);
    let r6 := match maybe(true) { Some(f) => f(6) - 7, None => 0 };
    let r7 := call_owned(adder(10), 7);
    let pair := (adder(10), 1);
    let r8 := (pair.0)(8);
    let r9 := pick(Run(adder(10)), 9) + pick(Skip, 9);
    let both := compose(adder(1), adder(2));
    let r10 := both(0);
    let seven := constant(7);
    let r11 := seven();
    var swap := adder(1);
    let old := replace(swap, adder(2));
    let r12 := old(0) + swap(0);
    r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + holder.tag.len() as i32 - 125
}
"#;
    // 11 + 12 + 13 + 29 + 16 + 17 + 17 + 18 + 19 + 3 + 7 + 3 + 2 = 167.
    single(source, 0, 42, "owned positions");
}

#[test]
fn generic_helpers_return_closures_over_any_type() {
    // constant(String) returns a closure that owns the string; Option is a
    // closure result too.
    let source = r#"fn constant<T>(value: T) -> fn() -> T { fn() -> T => value }
fn twice<T>(f: fn(T) -> T) -> fn(T) -> T { fn(x) => f(f(x)) }
fn plus(n: i32) -> fn(i32) -> i32 { fn(x) => x + n }
fn main() -> i32 {
    let a := constant(40);
    let b := constant(true);
    let c := twice(plus(1));
    let d := twice(twice(plus(1)));
    if b() { a() + c(0) } else { 0 }
}
"#;
    // 40 + 2 = 42.
    single(source, 0, 42, "generic helpers");
}

#[test]
fn captures_copy_primitives_and_move_owners() {
    // The closure sees the primitive as it was when it captured it; the
    // enclosing variable keeps its own value and stays usable. A moved String
    // is owned by the closure.
    let source = r#"fn mk(text: string) -> fn() -> u32 { fn() -> u32 => text.len() }
fn outer(n: i32) -> fn(i32) -> fn(i32) -> i32 { fn(a) => fn(b) => a + b + n }
fn main() -> i32 {
    var n := 1;
    let f: fn() -> i32 = fn() -> i32 => n;
    n = 5;
    let nested := outer(10)(20);
    let word := mk("abc".concat("d"));
    f() + nested(10) + n + word() as i32 - 4 - 4 + 0
}
"#;
    // 1 + 40 + 5 + 4 - 8 = 42.
    single(source, 0, 42, "copy and move");
}

#[test]
fn plain_function_values_are_lent_beside_owned_closures() {
    // Every function value is a move-only owner. A name or a non-capturing
    // literal is a fresh value at each mention, a `let` of one is lent to
    // `borrow fn` parameters (never copied), and an owned closure is lent the
    // same way.
    let source = r#"fn inc(x: i32) -> i32 { x + 1 }
fn adder(n: i32) -> fn(i32) -> i32 { fn(x) => x + n }
fn apply(f: borrow fn(i32) -> i32, x: i32) -> i32 { f(x) }
fn main() -> i32 {
    let f := inc;
    let g := inc;
    let h := fn(x: i32) -> i32 => x * 2;
    apply(f, 1) + apply(f, 2) + apply(g, 3) + f(4) + h(1) + h(2) + apply(adder(1), 20) - 19 + 20
}
"#;
    single(source, 0, 42, "plain lending");
}

// ---------------------------------------------------------------------------
// Moves and copies (negatives)

#[test]
fn captured_owners_are_moved_and_use_after_move_is_rejected() {
    rejects(
        "fn main() -> i32 { let s := \"ab\".concat(\"c\"); let f: fn() -> i32 = fn() -> i32 => s.len() as i32; let n := s.len(); f() + n as i32 }\n",
        "BE001",
        "unavailable after a move",
    );
    // A List captured by move.
    rejects(
        "use alloc::List;\nfn main() -> i32 { var l: List<i32> = []; l.push(1); let f: fn() -> i32 = fn() -> i32 => l.len() as i32; l.len() as i32 + f() }\n",
        "BE001",
        "unavailable after a move",
    );
    // A struct captured by move.
    rejects(
        "type P { name: string, n: i32 }\nfn main() -> i32 { let p := P { name: \"a\".concat(\"b\"), n: 1 }; let f: fn() -> i32 = fn() -> i32 => p.n; p.n + f() }\n",
        "BE001",
        "unavailable after a move",
    );
    // A closure moved into another closure.
    rejects(
        "fn adder(n: i32) -> fn(i32) -> i32 { fn(x) => x + n }\nfn main() -> i32 { let f := adder(1); let g: fn(i32) -> i32 = fn(x) => f(x); f(1) + g(1) }\n",
        "BE001",
        "unavailable after a move",
    );
}

#[test]
fn copying_a_closure_with_an_environment_is_rejected() {
    let adder = "fn adder(n: i32) -> fn(i32) -> i32 { fn(x) => x + n }\nfn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }\n";
    for body in [
        // A binding copy.
        "let f := adder(1); let g := f; f(1) + g(1)",
        // Passed twice to owned parameters.
        "let f := adder(1); apply(f, 1) + apply(f, 2)",
        // Stored twice.
        "let f := adder(1); let a := [f, f]; 0",
        // A copy out of a field or a List.
        "let h := H { run: adder(1) }; let f := h.run; f(1)",
    ] {
        let source =
            format!("{adder}type H {{ run: fn(i32) -> i32 }}\nfn main() -> i32 {{ {body} }}\n");
        let f = Fixture::new(&source);
        let output = f.run(&["check", "--tests"]);
        assert!(!output.status.success(), "accepted:\n{source}");
        let stderr = text(&output.stderr);
        assert!(
            stderr.contains("BE001") || stderr.contains("TE022"),
            "{source}\n{stderr}"
        );
    }
}

#[test]
fn owned_closures_cannot_capture_borrowed_things() {
    // A borrowed parameter or a second-class closure cannot move into a heap
    // environment.
    rejects(
        "fn keep(f: borrow fn(i32) -> i32) -> fn(i32) -> i32 { fn(x) => f(x) }\nfn main() -> i32 { 0 }\n",
        "TE017",
        "captures by move",
    );
    rejects(
        "fn keep(s: borrow string) -> fn() -> u32 { fn() -> u32 => s.len() }\nfn main() -> i32 { 0 }\n",
        "TE017",
        "captures by move",
    );
    // A second-class closure cannot become an owned value.
    rejects(
        "fn take(f: fn(i32) -> i32) -> i32 { f(1) }\nfn main() -> i32 { let n := 3; let f := fn(x: i32) -> i32 => x + n; take(f) }\n",
        "TE017",
        "second-class",
    );
    rejects(
        "fn main() -> i32 { let n := 3; let f := fn(x: i32) -> i32 => x + n; let g: fn(i32) -> i32 = fn(x) => f(x); g(1) }\n",
        "TE017",
        "captures by move",
    );
    // Without an expected owned function type the closure stays second-class.
    rejects(
        "fn main() -> i32 { let n := 3; var f := fn(x: i32) -> i32 => x + n; f(1) }\n",
        "TE017",
        "second-class",
    );
}

#[test]
fn alloc_false_rejects_owned_closures_with_captures_only() {
    let owned =
        "fn adder(n: i32) -> fn(i32) -> i32 { fn(x) => x + n }\nfn main() -> i32 { adder(1)(2) }\n";
    let f = Fixture::with(owned, "[build]\nalloc = false\n");
    let output = f.run(&["check"]);
    let stderr = text(&output.stderr);
    assert!(!output.status.success(), "{stderr}");
    assert!(
        stderr.contains("TE033") && stderr.contains("alloc = false"),
        "{stderr}"
    );
    // A closure without captures and plain functions need no heap.
    let plain = "fn inc(x: i32) -> i32 { x + 1 }\nfn pick() -> fn(i32) -> i32 { fn(x) => x * 2 }\nfn main() -> i32 { pick()(inc(20)) }\n";
    verify(
        &Fixture::with(plain, "[build]\nalloc = false\n"),
        0,
        42,
        "plain",
    );
}

// ---------------------------------------------------------------------------
// Environment mutation

#[test]
fn a_closure_mutates_its_own_environment_through_a_mutable_place() {
    // `var` locals and fields of `var` structs, `var` parameters and `share fn`
    // parameters may call a mutating closure; the enclosing variable is not
    // touched (the capture was a copy).
    let source = r#"fn counter(start: i32) -> var fn() -> i32 {
    var c := start;
    fn() -> i32 { c += 1; c }
}
fn twice(var f: var fn() -> i32) -> i32 { f() + f() }
fn shared(f: share fn() -> i32) -> i32 { f() + f() }
type Slot { run: var fn() -> i32 }
fn main() -> i32 {
    var start := 0;
    var a := counter(start);
    a();
    start += 100;
    let after := a();
    let t := twice(counter(10));
    var b := counter(20);
    let s := shared(b) + shared(b);
    var slot := Slot { run: counter(30) };
    let u := (slot.run)() + (slot.run)();
    after + t + s + u + start - 236
}
"#;
    // after = 2; t = 11 + 12 = 23; s = (21 + 22) + (23 + 24) = 90;
    // u = 31 + 32 = 63; start = 100: 2 + 23 + 90 + 63 + 100 - 236 = 42.
    single(source, 0, 42, "mutation through mutable places");
}

#[test]
fn closures_that_only_read_are_called_from_any_place() {
    // A plain `fn` value never changes its environment, so it can be called
    // through an immutable binding, an owned parameter, a `borrow fn`
    // parameter and lent to a `share fn` parameter.
    let source = r#"fn adder(n: i32) -> fn() -> i32 { fn() -> i32 => n }
fn once(f: fn() -> i32) -> i32 { f() }
fn read(f: borrow fn() -> i32) -> i32 { f() }
fn bump(f: share fn() -> i32) -> i32 { f() }
fn main() -> i32 {
    let a := adder(40);
    let b := adder(1);
    once(adder(0)) + read(a) + bump(b) + a() + b() - 41 - 0 + 0 + 0
}
"#;
    // 0 + 40 + 1 + 40 + 1 - 41 = 41.
    single(source, 0, 41, "readers");
}

// ---------------------------------------------------------------------------
// Lending

#[test]
fn owned_closures_lend_to_borrow_and_share_function_parameters() {
    let source = r#"fn adder(n: i32) -> fn(i32) -> i32 { fn(x) => x + n }
fn probe(f: borrow fn(i32) -> i32, x: i32) -> i32 { f(x) }
fn forward(f: borrow fn(i32) -> i32, x: i32) -> i32 { probe(f, x) + 1 }
fn visit(f: share fn(i32), n: i32) { loop i in 0..n { f(i); } }
fn recorder() -> var fn(i32) -> i32 {
    var seen := 0;
    fn(x) { seen += x; seen }
}
fn main() -> i32 {
    let f := adder(10);
    let a := probe(f, 1);
    let b := forward(f, 2);
    let c := probe(adder(20), 3);
    var r := recorder();
    let d := r(5) + r(6);
    let e := f(0);
    a + b + c + d + e - 11 - 13 - 23 - 16 - 10 + 42
}
"#;
    // 11 + 13 + 23 + (5 + 11) + 10 = 73; 73 - 73 + 42 = 42.
    single(source, 0, 42, "lending");
}

// ---------------------------------------------------------------------------
// Release: capped memory, deep chains

const BASE_TEXT: usize = 1_024;

fn capped_closure_program(extra: &str, clear: &str) -> String {
    let text = "x".repeat(BASE_TEXT);
    format!(
        r#"use alloc::List;
type Label {{ text: string, n: u32 }}
type Handler {{ name: string, run: fn() -> u32 }}
fn by_text(text: string) -> fn() -> u32 {{ fn() -> u32 => text.len() }}
fn by_list(items: List<u32>) -> fn() -> u32 {{ fn() -> u32 => items.len() }}
fn by_label(label: Label) -> fn() -> u32 {{ fn() -> u32 => label.text.len() + label.n }}
fn counting(text: string) -> var fn() -> u32 {{
    var seen: u32 = 0;
    fn() -> u32 {{ seen += text.len(); seen }}
}}
fn growing(text: string) -> var fn() -> u32 {{
    var s := text;
    fn() -> u32 {{ s.push_str("ab"); s.len() }}
}}
fn round(keep: share List<fn() -> u32>, early: bool) -> u32 {{
    let text := "{text}".concat("");
    var items: List<u32> = [];
    items.push(1);
    items.push(2);
    let label := Label {{ text: "{text}".concat(""), n: 3 }};
    let a := by_text(text);
    let b := by_list(items);
    var c := counting("{text}".concat(""));
    let h := Handler {{ name: "{text}".concat(""), run: by_label(label) }};
    var fs: List<fn() -> u32> = [];
    fs.push(by_text("{text}".concat("")));
    let option: (fn() -> u32)? = Some(by_text("{text}".concat("")));
    let array := [by_text("{text}".concat("")), by_text("{text}".concat(""))];
    let pair := (by_text("{text}".concat("")), 1);
    var swap := by_text("{text}".concat(""));
    let old := replace(swap, by_text("{text}".concat("")));
    var g := growing("{text}".concat(""));
    {extra}
    let n := a() + b() + c() + c() + (h.run)() + fs[0]();
    let more := match option {{ Some(f) => f(), None => 0 }} + array[1]() + (pair.0)() + old() + swap() + g();
    if early {{ return n + more; }}
    n + more + h.name.len()
}}
fn main() -> u32 {{
    var keep: List<fn() -> u32> = [];
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

fn run_capped_program(source: &str) -> (Fixture, Output) {
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
fn closure_environments_release_exactly_under_capped_memory() {
    // Per round: a() = t, b() = 2, c() = t then 2t, run() = t + 3, fs[0]() = t:
    // 6t + 5; option, array[1], pair.0, old and swap are t each and the growing
    // closure is t + 2: 12t + 7 in all. An early round returns that, the others
    // add the name (t).
    let t = BASE_TEXT as u64;
    let early = 12 * t + 7;
    let late = early + t;
    let rounds = u64::from(ITERATIONS);
    let expected = (rounds / 2) * early + (rounds / 2) * late;
    let source = capped_closure_program("", "");
    let f = Fixture::with(&source, "[build]\nstack_size=4096\n");
    let run = f.run(&["run"]);
    assert!(run.status.success(), "source run: {}", text(&run.stderr));
    assert_eq!(text(&run.stdout), format!("Result: u32({expected})\n"));
    let (f, capped) = run_capped_program(&source);
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
fn mutation_check_keeping_a_closure_per_round_exhausts_the_capped_memory() {
    // The same program, but every round moves a fresh closure with a heap
    // String into a List that is never emptied: the cap must trap, so the
    // clean run above really measures the release of environments.
    let text_value = "x".repeat(BASE_TEXT);
    let keep = format!(r#"keep.push(by_text("{text_value}".concat("")));"#);
    let (_f, kept) = run_capped_program(&capped_closure_program(&keep, ""));
    assert!(!kept.status.success(), "{kept:?}");
    assert!(
        text(&kept.stderr).contains("guest heap allocation failed"),
        "{}",
        text(&kept.stderr)
    );
    // With the clear restored (a List of closures releases every environment)
    // the same shape runs clean.
    let (_f, cleared) = run_capped_program(&capped_closure_program(&keep, "keep.clear();"));
    assert!(
        cleared.status.success() && cleared.stderr.is_empty(),
        "{}",
        text(&cleared.stderr)
    );
}

#[test]
fn a_deep_chain_of_closures_releases_without_recursion() {
    // 100,000 closures, each owning the previous one: dropping the last
    // releases the whole chain iteratively. (Calling a chain this deep would
    // exhaust the call stack, so the chain is only built and dropped.)
    let source = r#"fn adder(n: i32) -> fn(i32) -> i32 { fn(x) => x + n }
fn compose(f: fn(i32) -> i32, g: fn(i32) -> i32) -> fn(i32) -> i32 { fn(x) => g(f(x)) }
fn main() -> i32 {
    var acc := adder(0);
    loop i in 0..100000 {
        let previous := replace(acc, adder(0));
        let next := compose(previous, adder(1));
        let spare := replace(acc, next);
    }
    42
}
"#;
    single(source, 0, 42, "deep chain");
    // A shallow chain also computes.
    let shallow = source
        .replace("100000", "50")
        .replace("    42\n", "    acc(0) - 8\n");
    single(&shallow, 0, 42, "shallow chain");
}
