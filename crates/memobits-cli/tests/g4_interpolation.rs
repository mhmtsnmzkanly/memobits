//! G4: string interpolation `"x = {x}"`.
//!
//! Every runtime check runs from source and from the standalone Wasm
//! artifact. Expected texts are produced by Rust's own formatting.
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
            "memobits-g4-interpolation-{}-{}",
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

/// Lower the memory maximum to the initial size plus one page, keeping every
/// other section. Only released heap blocks can be reused beyond that page.
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
        assert!(section_end <= bytes.len(), "truncated Wasm section");
        if id != 5 {
            module.extend_from_slice(&bytes[section_start..section_end]);
        } else {
            assert!(result.is_none(), "unexpected second Wasm memory section");
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

fn assert_capped_memory(wasm_path: &PathBuf, initial: u32, maximum: u32) {
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(wasm_path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

fn project(f: &Fixture, build: &str, source: &str) {
    let build = if build.is_empty() {
        String::new()
    } else {
        format!("[build]\n{build}\n")
    };
    f.write(
        "project.toml",
        &format!("[package]\nname='g4'\nentry='main::main'\n{build}"),
    );
    f.write("src/main.mb", source);
}

fn build_wasm(f: &Fixture, name: &str) -> PathBuf {
    let build = f.run(&["build", "--output", name]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    f.0.join(name)
}

/// Run from source and from the standalone artifact; both must print
/// `expected` and nothing on stderr.
fn run_source_and_wasm(f: &Fixture, expected: &str) {
    let source = f.run(&["run"]);
    assert!(
        source.status.success() && source.stderr.is_empty(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&source.stdout), expected);
    build_wasm(f, "g4.wasm");
    let wasm = f.run(&["run", "g4.wasm"]);
    assert!(
        wasm.status.success() && wasm.stderr.is_empty(),
        "Wasm failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&wasm.stdout), expected);
}

fn rejects(f: &Fixture, source: &str, code: &str, text: &str) {
    f.write("src/main.mb", source);
    let check = f.run(&["check"]);
    assert!(!check.status.success(), "expected {code} for:\n{source}");
    let stderr = String::from_utf8_lossy(&check.stderr);
    assert!(
        stderr.contains(&format!("error[{code}]")),
        "expected {code}, got: {stderr}"
    );
    assert!(stderr.contains(text), "expected `{text}`, got: {stderr}");
}

const OK: &str = "Result: i32(42)\n";

/// Byte `i` of `s` is `want`.
const AT: &str = r#"fn at(s: borrow string, i: u32, want: u8) -> bool {
    match s.byte_at(i) { Some(b) => b == want, None => false }
}
"#;

/// A check of the form `lets; let s := "template"; <bytes of s == expected>`.
/// The expected bytes come from Rust, never from another literal.
fn expect(lets: &str, template: &str, expected: &str) -> String {
    let mut body = format!(
        "{lets} let s := \"{template}\"; s.len() == {}",
        expected.len()
    );
    for (index, byte) in expected.bytes().enumerate() {
        body.push_str(&format!(" && at(s.borrow(), {index}, {byte})"));
    }
    body
}

/// A program of `fn cN() -> bool` checks plus a `main` that asserts each.
fn checks_program(extra: &str, checks: &[String]) -> String {
    let mut source = format!("{AT}{extra}\n");
    for (index, body) in checks.iter().enumerate() {
        source.push_str(&format!("fn c{index}() -> bool {{ {body} }}\n"));
    }
    source.push_str("fn main() -> i32 {\n");
    for index in 0..checks.len() {
        source.push_str(&format!("    assert(c{index}());\n"));
    }
    source.push_str("    42\n}\n");
    source
}

fn run_checks(extra: &str, checks: &[String]) {
    let f = Fixture::new();
    project(&f, "", &checks_program(extra, checks));
    run_source_and_wasm(&f, OK);
}

#[test]
fn integers_of_every_width_format_like_rust_including_extremes() {
    let mut checks = Vec::new();
    macro_rules! integer_cases {
        ($ty:ty, $name:literal) => {{
            let (min, max) = (i128::from(<$ty>::MIN), i128::from(<$ty>::MAX));
            let mut values = vec![min, min + 1, max, max - 1, 0, 1, 9, 10, 99, 100];
            values.extend([-1, -9, -10, -99, -100]);
            let mut power: i128 = 1;
            while power <= max {
                values.extend([power, power - 1, -power, -power + 1]);
                power *= 10;
            }
            values.sort();
            values.dedup();
            for value in values.into_iter().filter(|v| (min..=max).contains(v)) {
                checks.push(expect(
                    &format!("let v: {} = {value};", $name),
                    "{v}",
                    &value.to_string(),
                ));
            }
        }};
    }
    integer_cases!(i8, "i8");
    integer_cases!(i16, "i16");
    integer_cases!(i32, "i32");
    integer_cases!(i64, "i64");
    integer_cases!(u8, "u8");
    integer_cases!(u16, "u16");
    integer_cases!(u32, "u32");
    integer_cases!(u64, "u64");
    assert!(checks.len() > 150);
    // The text of the two 64-bit extremes is spelled out as well.
    checks.push(expect(
        "let a: i64 = -9223372036854775808; let b: i64 = 9223372036854775807; let c: u64 = 18446744073709551615;",
        "{a}|{b}|{c}",
        "-9223372036854775808|9223372036854775807|18446744073709551615",
    ));
    run_checks("", &checks);
}

#[test]
fn bool_char_and_string_values_use_their_text_and_utf8_bytes() {
    let mut checks = vec![
        expect("let b := true;", "{b}", "true"),
        expect("let b := false;", "{b}", "false"),
        expect(
            "let a := true; let b := false;",
            "{a}/{b}/{a}",
            "true/false/true",
        ),
        expect(
            "let a := false; let b := true;",
            "{a}{b}{a}",
            "falsetruefalse",
        ),
    ];
    // Every UTF-8 width and the boundaries between widths.
    for scalar in [
        'a',
        'Z',
        '0',
        ' ',
        '\u{7f}',
        '\u{80}',
        'é',
        '\u{7ff}',
        '\u{800}',
        '€',
        '\u{ffff}',
        '\u{10000}',
        '😀',
        '\u{10ffff}',
    ] {
        checks.push(expect(
            &format!("let c: char = '{scalar}';"),
            "<{c}>",
            &format!("<{scalar}>"),
        ));
    }
    checks.push(expect("let c: char = '\\n';", "a{c}b", "a\nb"));
    for text in ["", "plain", "café", "é😀€", "😀😀😀", "ünï\u{10ffff}çodé"] {
        checks.push(expect(
            &format!("let t := \"{text}\";"),
            "[{t}]",
            &format!("[{text}]"),
        ));
    }
    run_checks("", &checks);
}

#[test]
fn placeholders_adjacent_empty_repeated_and_many() {
    let checks = [
        // Only a placeholder, leading, trailing and adjacent placeholders.
        expect("let a := \"A\";", "{a}", "A"),
        expect("let a := \"A\";", "{a}x", "Ax"),
        expect("let a := \"A\";", "x{a}", "xA"),
        expect(
            "let a := \"A\"; let b := \"BB\"; let c: u8 = 7;",
            "{a}{b}{c}",
            "ABB7",
        ),
        expect("let a := \"A\";", "{a}{a}{a}-{a}", "AAA-A"),
        // Empty strings are valid parts, even when every part is empty.
        expect("let e := \"\";", "{e}", ""),
        expect("let e := \"\";", "{e}{e}", ""),
        expect("let e := \"\";", "a{e}b{e}c", "abc"),
        // Repeated reads of one identifier, of every kind.
        expect("let n: i32 = -5;", "{n}{n}", "-5-5"),
        expect("let b := true;", "{b}{b}", "truetrue"),
        expect("let c: char = 'é';", "{c}{c}", "éé"),
        // `{{` and `}}` are literal braces, also next to placeholders.
        expect("", "{{", "{"),
        expect("", "}}", "}"),
        expect("", "{{}}", "{}"),
        expect("", "}}{{", "}{"),
        expect("let x: u8 = 1;", "{{{x}}}", "{1}"),
        expect("let x: u8 = 1;", "{{x}} = {x}", "{x} = 1"),
        expect("let x: u8 = 1;", "}}{x}{{", "}1{"),
        expect("let x: u8 = 1;", "{{{{{x}}}}}", "{{1}}"),
        expect("let x: u8 = 1;", "{{{x}{{{x}}}{x}}}", "{1{1}1}"),
        // Identifiers with digits, underscores and non-ASCII letters.
        expect("let my_value2: u16 = 65535;", "v={my_value2};", "v=65535;"),
        expect("let _x: u8 = 3;", "{_x}", "3"),
        expect("let größe: u32 = 9;", "{größe}!", "9!"),
        // Many placeholders of mixed types in one literal.
        expect(
            "let a: i8 = -1; let b: u8 = 2; let c: i16 = -3; let d: u16 = 4; let e: i32 = -5; \
             let f: u32 = 6; let g: i64 = -7; let h: u64 = 8; let i := true; let j: char = 'j'; \
             let k := \"kk\";",
            "{a},{b},{c},{d},{e},{f},{g},{h},{i},{j},{k}|{a}{b}{c}{d}{e}{f}{g}{h}{i}{j}{k}",
            "-1,2,-3,4,-5,6,-7,8,true,j,kk|-12-34-56-78truejkk",
        ),
    ];
    run_checks("", &checks);
}

#[test]
fn identifiers_are_read_without_moving_or_changing_them() {
    let extra = r#"
type Pair { name: string, n: u32 }
fn read(s: borrow string) -> u32 { s.len() }
fn param_text(s: borrow string, n: u32) -> bool {
    let t := "{s}:{n}";
    t.len() == s.len() + 2 && at(t.borrow(), 0, 104)
}
fn share_text(s: share string) -> u32 {
    let t := "<{s}>";
    t.len()
}
"#;
    let checks = [
        // The source String is still usable, and moves afterwards.
        "let s := \"hello\"; let t := \"{s}\"; let u := \"{s}!\"; let moved := s; \
         t.len() == 5 && u.len() == 6 && moved.len() == 5"
            .to_owned(),
        // A live borrow of the owner coexists with a read.
        "let s := \"abc\"; let view := s.borrow(); let t := \"{s}\"; view.len() + t.len() == 6"
            .to_owned(),
        // Primitives are copied and stay usable (and mutable) afterwards.
        "var n: u32 = 4; let t := \"{n}\"; n += 1; let u := \"{n}\"; \
         at(t.borrow(), 0, 52) && at(u.borrow(), 0, 53)"
            .to_owned(),
        // Borrow and share parameters, and an element read through a borrow.
        "let s := \"host\"; param_text(s.borrow(), 7)".to_owned(),
        "var s := \"ab\".concat(\"cd\"); share_text(s.share()) == 6".to_owned(),
        "let p := Pair { name: \"pn\".concat(\"!\"), n: 3 }; \
         let name := p.name.borrow(); let t := \"{name}\"; t.len() == 3 && read(name) == 3"
            .to_owned(),
        // Reassigning from itself reads the old value first.
        "var s := \"x\".concat(\"y\"); s = \"{s}{s}\"; s = \"[{s}]\"; s.len() == 6".to_owned(),
    ];
    run_checks(extra, &checks);
}

#[test]
fn interpolation_is_a_string_expression_in_every_value_position() {
    let extra = r#"use alloc::List;
type Pair { name: string, n: u32 }
fn take(s: string, n: u32) -> u32 { s.len() + n }
fn measure(s: borrow string) -> u32 { s.len() }
fn from_tail(n: u32) -> string { "tail {n}" }
fn from_return(n: u32) -> string { return "return {n}"; }
fn from_branch(flag: bool, n: u32) -> string { if flag { "yes {n}" } else { "no {n}" } }
fn from_match(o: u32?) -> string { match o { Some(x) => "some {x}", None => "none" } }
fn try_it(o: u32?) -> u32 {
    let n := try o else { return 99; };
    "got {n}".len()
}
fn argument_order(flag: bool) -> u32 {
    let n: u32 = 5;
    // The later argument can leave the function after the first is built.
    take("first {n}", if flag { return 1; } else { n })
}
"#;
    let checks = [
        // let, tail, return, branch and match values.
        expect("let n: u32 = 7;", "item {n}", "item 7"),
        "let s := from_tail(3); at(s.borrow(), 5, 51) && s.len() == 6".to_owned(),
        "let s := from_return(42); s.len() == 9 && at(s.borrow(), 7, 52) && at(s.borrow(), 8, 50)"
            .to_owned(),
        "let a := from_branch(true, 1); let b := from_branch(false, 2); a.len() == 5 && b.len() == 4"
            .to_owned(),
        "from_match(Some(10)).len() == 7 && from_match(None).len() == 4".to_owned(),
        "try_it(Some(3)) == 5 && try_it(None) == 99".to_owned(),
        // Arguments: owned, temporary borrow, and an early exit in a later argument.
        "let n: u32 = 12; take(\"v{n}\", 1) == 4".to_owned(),
        "let n: u32 = 12; measure(\"v{n}\".borrow()) == 3".to_owned(),
        "argument_order(false) == 12 && argument_order(true) == 1".to_owned(),
        // Struct fields (several, with an early exit between them), tuples,
        // arrays, collections and a replaced variable.
        "let i: u32 = 3; let p := Pair { name: \"a{i}\", n: i }; p.name.len() == 2 && p.n == 3"
            .to_owned(),
        "let i: u32 = 3; let p := Pair { name: \"n{i}\", n: { if i == 4 { return false; } i } }; \
         p.name.len() == 2"
            .to_owned(),
        "let i: u32 = 4; let p := Pair { name: \"n{i}\", n: { if i == 4 { return true; } i } }; false"
            .to_owned(),
        "let i: u32 = 3; let t := (\"x{i}\", \"y{i}\"); let (a, b) := t; a.len() + b.len() == 4"
            .to_owned(),
        "let i: u32 = 3; let arr: array<string, 2> = [\"x{i}\", \"yy{i}\"]; \
         arr[0].len() + arr[1].len() == 5"
            .to_owned(),
        "let i: u32 = 3; var xs: List<string> = []; xs.push(\"a{i}\"); xs.push(\"b{i}\"); \
         xs[0].len() + xs[1].len() == 4"
            .to_owned(),
        "let i: u32 = 3; let xs: List<string> = [\"a{i}\", \"bb{i}\"]; xs.len() == 2".to_owned(),
        "let i: u32 = 3; let o := Some(\"z{i}\"); match o { Some(s) => s.len() == 2, None => false }"
            .to_owned(),
        "var s := \"seed\"; var i: u32 = 0; loop { if i == 3 { break; } s = \"{s}{i}\"; i += 1; } \
         s.len() == 7"
            .to_owned(),
        // Used and discarded as a statement.
        "let i: u32 = 3; \"unused {i}\"; true".to_owned(),
        // Inside a short-circuit branch that is not taken.
        "let flag := false; let i: u32 = 3; flag && measure(\"never {i}\".borrow()) == 7 || true"
            .to_owned(),
    ];
    run_checks(extra, &checks);
}

#[test]
fn interpolation_in_a_guest_test_function_runs_under_mb_test() {
    let f = Fixture::new();
    project(
        &f,
        "",
        &format!(
            "{AT}fn main() -> i32 {{ 42 }}\n\
             test fn formats_values() {{\n    let n: i32 = -12;\n    let s := \"n={{n}}!\";\n    \
             assert(s.len() == 6);\n    assert(at(s.borrow(), 2, 45));\n}}\n"
        ),
    );
    let out = f.run(&["test"]);
    assert!(out.status.success(), "{out:?}");
    assert!(
        String::from_utf8_lossy(&out.stdout).contains("1 passed"),
        "{out:?}"
    );
}

#[test]
fn a_literal_without_placeholders_stays_a_static_literal() {
    // Brace escapes alone do not allocate: the program builds without the
    // alloc layer and without any allocator in the artifact.
    let f = Fixture::new();
    project(
        &f,
        "alloc = false",
        "fn main() -> i32 { let s := \"{{}}\"; let t := \"a}}b{{c\"; if s.len() == 2 && t.len() == 5 { 42 } else { 1 } }\n",
    );
    run_source_and_wasm(&f, OK);
    let wasm = fs::read(f.0.join("g4.wasm")).unwrap();
    let memory = wasmparser::Parser::new(0)
        .parse_all(&wasm)
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("literal data needs a memory")
        .unwrap();
    assert_eq!(memory.maximum, Some(memory.initial), "no heap growth");
    // The same program through the default (alloc) layer is also fine.
    project(
        &f,
        "",
        "fn main() -> i32 { let s := \"{{}}\"; if s.len() == 2 { 42 } else { 1 } }\n",
    );
    run_source_and_wasm(&f, OK);
}

#[test]
fn interpolation_needs_the_alloc_layer() {
    let f = Fixture::new();
    project(
        &f,
        "alloc = false",
        "fn main() -> i32 { let n: i32 = 1; let s := \"n={n}\"; s.len() as i32 }\n",
    );
    for command in ["check", "build", "run"] {
        let out = f.run(&[command]);
        assert!(!out.status.success(), "{command}: {out:?}");
        let text = String::from_utf8_lossy(&out.stderr);
        assert!(text.contains("error[TE033]"), "{command}: {text}");
        assert!(text.contains("string interpolation"), "{command}: {text}");
        assert!(text.contains("[build] alloc = false"), "{command}: {text}");
    }
}

#[test]
fn brace_and_identifier_errors_are_lexical_diagnostics() {
    let f = Fixture::new();
    project(&f, "", "fn main() {}\n");
    for (literal, message) in [
        ("{", "unterminated `{`"),
        ("a{b", "unterminated `{`"),
        ("{{{", "unterminated `{`"),
        ("{}", "empty `{}`"),
        ("a}", "unmatched `}`"),
        ("}", "unmatched `}`"),
        ("}{", "unmatched `}`"),
        ("{n}}", "unmatched `}`"),
        ("{ n }", "only a plain identifier"),
        ("{n.len}", "only a plain identifier"),
        ("{n + 1}", "only a plain identifier"),
        ("{f(n)}", "only a plain identifier"),
        ("{n:x}", "only a plain identifier"),
        ("{1}", "only a plain identifier"),
        ("{a b}", "only a plain identifier"),
        ("{n{m}}", "only a plain identifier"),
    ] {
        rejects(
            &f,
            &format!("fn main() -> i32 {{ let n: i32 = 1; let m: i32 = 2; let s := \"{literal}\"; 0 }}\n"),
            "SE001",
            message,
        );
    }
    // The span points at the offending braces, not at the whole literal.
    let line = "fn main() -> i32 { let n: i32 = 1; let s := \"ab {n.len} cd\"; 0 }\n";
    f.write("src/main.mb", line);
    let out = f.run(&["check"]);
    let text = String::from_utf8_lossy(&out.stderr);
    let column = line.find("{n.len").unwrap() + 1;
    assert!(text.contains(&format!("src/main.mb:1:{column}")), "{text}");
    assert!(
        text.contains("^^^^^^^\n") && !text.contains("^^^^^^^^"),
        "{text}"
    );
}

#[test]
fn unsupported_and_unknown_values_are_clear_diagnostics() {
    let f = Fixture::new();
    project(&f, "", "fn main() {}\n");
    let prelude = "use alloc::List;\ntype P { x: i32 }\ntype E [ A, B ]\n";
    for (lets, name, message) in [
        // Aggregates and other types.
        (
            "let v := P { x: 1 };",
            "v",
            "cannot interpolate a value of type 'P'",
        ),
        (
            "let v := E::A;",
            "v",
            "cannot interpolate a value of type 'E'",
        ),
        (
            "let v: u32? = Some(1);",
            "v",
            "cannot interpolate a value of type",
        ),
        (
            "let v: array<u8, 2> = [1, 2];",
            "v",
            "cannot interpolate a value of type 'array<u8, 2>'",
        ),
        (
            "let v: List<u8> = [];",
            "v",
            "cannot interpolate a value of type 'List<u8>'",
        ),
        (
            "let v := (1, 2);",
            "v",
            "cannot interpolate a value of type",
        ),
    ] {
        rejects(
            &f,
            &format!("{prelude}fn main() -> i32 {{ {lets} let s := \"[{{{name}}}]\"; 0 }}\n"),
            "TE017",
            message,
        );
    }
    rejects(
        &f,
        "fn main() -> i32 { let s := \"[{missing}]\"; 0 }\n",
        "NE001",
        "unknown name 'missing'",
    );
    // A function name is not a value.
    rejects(
        &f,
        "fn helper() {}\nfn main() -> i32 { let s := \"[{helper}]\"; 0 }\n",
        "TE017",
        "cannot interpolate",
    );
}

#[test]
fn reading_for_interpolation_respects_loans_and_moves() {
    let f = Fixture::new();
    project(&f, "", "fn main() {}\n");
    // An exclusive share of a String or a primitive blocks the read.
    rejects(
        &f,
        "fn main() -> i32 {\n    var s := \"a\".concat(\"b\");\n    let w := s.share();\n    let t := \"{s}\";\n    w.len() as i32 + t.len() as i32\n}\n",
        "BE005",
        "cannot borrow `s` while it is shared",
    );
    rejects(
        &f,
        "fn main() -> i32 {\n    var n: i32 = 3;\n    let w := n.share();\n    let t := \"{n}\";\n    w.copy() + t.len() as i32\n}\n",
        "BE005",
        "cannot read `n` while it is shared",
    );
    // A moved String cannot be read.
    rejects(
        &f,
        "fn main() -> i32 {\n    let s := \"a\".concat(\"b\");\n    let moved := s;\n    let t := \"{s}\";\n    moved.len() as i32 + t.len() as i32\n}\n",
        "BE001",
        "local 's' is unavailable after a move",
    );
    // The same reads are fine without the conflicting share.
    run_checks(
        "",
        &[
            "var s := \"a\".concat(\"b\"); let w := s.share(); let k := w.len(); let t := \"{s}\"; k == 2 && t.len() == 2"
                .to_owned(),
        ],
    );
}

const STRESS_TEXT_BYTES: usize = 1_024;
const STRESS_ITERATIONS: u32 = 4_096;

fn digits(value: u32) -> u64 {
    value.to_string().len() as u64
}

/// Rust mirror of the stress program's result for one iteration.
fn stress_expected(i: u32) -> u64 {
    let t = STRESS_TEXT_BYTES as u64;
    let d = digits(i);
    let i64v = u64::from(i);
    let a = t + 1 + d;
    let b = 2 * t + 5 + 2 * d;
    let early = match i % 5 {
        1 => a,
        2 => b,
        3 => 7,
        _ => b + a + i64v,
    };
    let conditional = u64::from(i % 2 == 0);
    let fields = if i % 7 == 0 {
        11
    } else if i % 3 == 0 {
        5
    } else {
        d + (1 + d)
    };
    let loops = 2 * (t + 3);
    let list = if i % 4 == 0 {
        3
    } else {
        (t + 1 + d) + (t + 1) + d
    };
    let reassign = t + 1 + 4 * d;
    early + conditional + fields + loops + list + reassign
}

#[test]
fn building_strings_in_loops_with_early_exits_runs_in_capped_memory() {
    let big = "x".repeat(STRESS_TEXT_BYTES);
    let source = format!(
        r#"use alloc::List;
type Pair {{ name: string, other: string, n: u32 }}
fn take(s: string, n: u32) -> u32 {{ s.len() + n }}
fn long(s: borrow string) -> bool {{ s.len() > {STRESS_TEXT_BYTES} }}
fn early(i: u32, flag: u32) -> u32 {{
    let big := "{big}";
    let a := "{{big}}#{{i}}";
    if flag == 1 {{ return a.len(); }}
    let b := "[{{a}}|{{i}}|{{big}}]";
    if flag == 2 {{ return b.len(); }}
    let c := take("{{b}}{{a}}", if flag == 3 {{ return 7; }} else {{ i }});
    c
}}
fn conditional(i: u32) -> u32 {{
    let big := "{big}";
    if i % 2 == 0 && long("{{big}}{{i}}".borrow()) {{ 1 }} else {{ 0 }}
}}
fn fields(i: u32) -> u32 {{
    let big := "{big}";
    let p := Pair {{ name: "{{big}}{{i}}", other: "n{{i}}", n: {{ if i % 7 == 0 {{ return 11; }} i }} }};
    if i % 3 == 0 {{ return 5; }}
    p.name.len() - {STRESS_TEXT_BYTES} + p.other.len()
}}
fn loops() -> u32 {{
    let big := "{big}";
    var j: u32 = 0;
    var acc: u32 = 0;
    loop {{
        if j == 3 {{ break; }}
        let s := "{{big}}-{{j}}";
        j += 1;
        if j == 2 {{ continue; }}
        let t := "{{s}}!";
        acc += t.len();
    }}
    acc
}}
fn list(i: u32) -> u32 {{
    let big := "{big}";
    var xs: List<string> = [];
    xs.push("{{big}}a{{i}}");
    xs.push("{{big}}b");
    xs.push("{{i}}");
    if i % 4 == 0 {{ return 3; }}
    let n := xs[0].len() + xs[1].len() + xs[2].len();
    xs.clear();
    n
}}
fn reassign(i: u32) -> u32 {{
    let big := "{big}";
    var s := "{{big}}0";
    var k: u32 = 0;
    loop {{
        if k == 4 {{ break; }}
        s = "{{s}}{{i}}";
        k += 1;
    }}
    s.len()
}}
fn main() -> u32 {{
    var i: u32 = 0;
    var total: u32 = 0;
    loop {{
        if i == {STRESS_ITERATIONS} {{ break; }}
        total += early(i, i % 5);
        total += conditional(i);
        total += fields(i);
        total += loops();
        total += list(i);
        total += reassign(i);
        i += 1;
    }}
    total
}}
"#
    );
    let expected: u64 = (0..STRESS_ITERATIONS).map(stress_expected).sum();
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='g4-stress'\nentry='main::main'\n[build]\nstack_size=4096\n",
    );
    f.write("src/main.mb", &source);
    let source_run = f.run(&["run", "--no-fuel-limit"]);
    assert!(
        source_run.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source_run.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&source_run.stdout),
        format!("Result: u32({expected})\n")
    );
    let wasm_path = build_wasm(&f, "g4-stress.wasm");
    let wasm = f.run(&["run", "g4-stress.wasm", "--no-fuel-limit"]);
    assert!(
        wasm.status.success() && wasm.stderr.is_empty(),
        "Wasm failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&wasm.stdout),
        format!("Result: i32({expected})\n")
    );
    let (capped, initial, maximum) = cap_memory(&fs::read(&wasm_path).unwrap());
    fs::write(&wasm_path, capped).unwrap();
    let capped_run = f.run(&["run", "g4-stress.wasm", "--no-fuel-limit"]);
    assert!(
        capped_run.status.success(),
        "capped Wasm run failed: {}",
        String::from_utf8_lossy(&capped_run.stderr)
    );
    assert!(capped_run.stderr.is_empty());
    assert_eq!(
        String::from_utf8_lossy(&capped_run.stdout),
        format!("Result: i32({expected})\n")
    );
    assert_capped_memory(&wasm_path, initial, maximum);
}

#[test]
fn allocation_failure_is_a_controlled_trap() {
    // Doubling a String until the one extra page is exhausted must trap with
    // the heap-allocation reason, never corrupt memory.
    let f = Fixture::new();
    project(
        &f,
        "",
        "fn main() -> u32 {\n    var s := \"0123456789abcdef\";\n    var i: u32 = 0;\n    loop {\n        if i == 30 { break; }\n        s = \"{s}{s}\";\n        i += 1;\n    }\n    s.len()\n}\n",
    );
    let wasm_path = build_wasm(&f, "g4-oom.wasm");
    let (capped, _, _) = cap_memory(&fs::read(&wasm_path).unwrap());
    fs::write(&wasm_path, capped).unwrap();
    let out = f.run(&["run", "g4-oom.wasm", "--no-fuel-limit"]);
    assert!(!out.status.success(), "{out:?}");
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("guest heap allocation failed"),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}
