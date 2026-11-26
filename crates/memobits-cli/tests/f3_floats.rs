//! F3: floating-point values in string interpolation print Rust's `Display`
//! text (shortest round-trip digits, no exponent). Expected texts come from
//! Rust's own `format!("{}", v)`; every run is from source and standalone Wasm.
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
            "memobits-f3-floats-{}-{}",
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
        &format!("[package]\nname='f3'\nentry='main::main'\n{build}"),
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
    build_wasm(f, "f3.wasm");
    let wasm = f.run(&["run", "f3.wasm"]);
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

/// The guest hashes a string with two independent polynomial hashes and the
/// length; Rust computes the same from `format!("{}", v)`, so a large table
/// is checked without spelling out every byte.
const MIX: &str = r#"fn mix(s: borrow string) -> u64 {
    var a: u64 = 7;
    var b: u64 = 11;
    loop i in 0..s.len() {
        let c: u64 = match s.byte_at(i) { Some(x) => x as u64, None => 0 };
        a = (a * 131 + c) % 1000000007;
        b = (b * 257 + c) % 998244353;
    }
    a * 1000000000 + b
}
fn chk(s: borrow string, n: u32, h: u64) -> bool { s.len() == n && mix(s) == h }
"#;

fn mix(text: &str) -> u64 {
    let (mut a, mut b) = (7u64, 11u64);
    for byte in text.bytes() {
        a = (a * 131 + u64::from(byte)) % 1_000_000_007;
        b = (b * 257 + u64::from(byte)) % 998_244_353;
    }
    a * 1_000_000_000 + b
}

/// Source text of a float literal that reads back as exactly `text`.
fn literal(text: &str) -> String {
    match text {
        "NaN" => "(0.0 / 0.0)".into(),
        "inf" => "(1.0 / 0.0)".into(),
        "-inf" => "(-1.0 / 0.0)".into(),
        _ if text.contains('.') => text.to_string(),
        _ => format!("{text}.0"),
    }
}

struct Xorshift(u64);

impl Xorshift {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

/// One value of the table: its source literal and the text Rust prints.
struct Case {
    literal: String,
    expected: String,
}

fn f64_case(value: f64) -> Case {
    let expected = format!("{value}");
    Case {
        literal: literal(&expected),
        expected,
    }
}

fn f32_case(value: f32) -> Case {
    let expected = format!("{value}");
    Case {
        literal: literal(&expected),
        expected,
    }
}

/// `fn cN() -> bool` with eight checks each, and a `main` asserting every one.
fn table_program(ty: &str, cases: &[Case]) -> String {
    let mut source = String::from(MIX);
    let groups: Vec<&[Case]> = cases.chunks(8).collect();
    for (group, chunk) in groups.iter().enumerate() {
        source.push_str(&format!("fn c{group}() -> bool {{\n"));
        for (index, case) in chunk.iter().enumerate() {
            source.push_str(&format!(
                "    let v{index}: {ty} = {};\n    let s{index} := \"{{v{index}}}\";\n",
                case.literal
            ));
        }
        let checks: Vec<String> = chunk
            .iter()
            .enumerate()
            .map(|(index, case)| {
                format!(
                    "chk(s{index}.borrow(), {}, {})",
                    case.expected.len(),
                    mix(&case.expected)
                )
            })
            .collect();
        source.push_str(&format!("    {}\n}}\n", checks.join(" && ")));
    }
    source.push_str("fn main() -> i32 {\n");
    for group in 0..groups.len() {
        source.push_str(&format!("    assert(c{group}());\n"));
    }
    source.push_str("    42\n}\n");
    source
}

fn run_program(source: &str) {
    let f = Fixture::new();
    project(&f, "", source);
    let source_run = f.run(&["run", "--no-fuel-limit"]);
    assert!(
        source_run.status.success() && source_run.stderr.is_empty(),
        "source failed: {}",
        String::from_utf8_lossy(&source_run.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&source_run.stdout), OK);
    build_wasm(&f, "f3.wasm");
    let wasm = f.run(&["run", "f3.wasm", "--no-fuel-limit"]);
    assert!(
        wasm.status.success() && wasm.stderr.is_empty(),
        "Wasm failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&wasm.stdout), OK);
}

fn f64_table() -> Vec<f64> {
    let mut values = vec![
        0.0,
        -0.0,
        1.0,
        -1.0,
        0.5,
        0.1,
        0.2,
        0.1 + 0.2,
        1.0 / 3.0,
        2.0 / 3.0,
        std::f64::consts::PI,
        std::f64::consts::E,
        f64::MAX,
        f64::MIN,
        f64::MIN_POSITIVE,
        -f64::MIN_POSITIVE,
        f64::EPSILON,
        1.0 + f64::EPSILON,
        1.0 - f64::EPSILON / 2.0,
        f64::from_bits(1),
        f64::from_bits(2),
        f64::from_bits(3),
        f64::from_bits(0x000f_ffff_ffff_ffff),
        f64::from_bits(0x0010_0000_0000_0001),
        f64::from_bits(0x8000_0000_0000_0001),
        9007199254740992.0,
        9007199254740993.0,
        4503599627370497.5,
        123456789.0,
        1e15,
        1e16,
        1e17,
        1.5e300,
        2.5e-300,
        4.9e-324,
        1.7976931348623157e308,
    ];
    // Powers of ten across the whole range and both neighbors of each.
    for exponent in -323..=308 {
        let value: f64 = format!("1e{exponent}").parse().unwrap();
        let bits = value.to_bits();
        values.extend([
            f64::from_bits(bits - 1),
            value,
            f64::from_bits(bits + 1),
            -value,
        ]);
    }
    // Powers of two: the asymmetric-gap boundaries.
    for exponent in -1074..=1023 {
        values.push(2f64.powi(exponent));
    }
    // Seeded pseudo-random bit patterns: 2,500 finite values of any exponent.
    let mut random = Xorshift(0x9E37_79B9_7F4A_7C15);
    while values.len() < 36 + 4 * 632 + 2098 + 2500 {
        let value = f64::from_bits(random.next());
        if value.is_finite() {
            values.push(value);
        }
    }
    values
}

#[test]
fn f64_formats_exactly_like_rust_display_for_a_large_table() {
    let values = f64_table();
    assert!(values.len() > 7_000, "{}", values.len());
    let cases: Vec<Case> = values.into_iter().map(f64_case).collect();
    run_program(&table_program("f64", &cases));
}

#[test]
fn f32_formats_exactly_like_rust_display_for_a_large_table() {
    let mut values: Vec<f32> = vec![
        0.0,
        -0.0,
        1.0,
        -1.0,
        0.5,
        0.1,
        0.2,
        0.1 + 0.2,
        1.0 / 3.0,
        std::f32::consts::PI,
        f32::MAX,
        f32::MIN,
        f32::MIN_POSITIVE,
        f32::EPSILON,
        1.0 + f32::EPSILON,
        f32::from_bits(1),
        f32::from_bits(2),
        f32::from_bits(0x007f_ffff),
        f32::from_bits(0x0080_0001),
        16777216.0,
        16777217.0,
        33554432.0,
        1e10,
        3.4028235e38,
        1.17549435e-38,
        1.4e-45,
    ];
    for exponent in -45..=38 {
        let value: f32 = format!("1e{exponent}").parse().unwrap();
        let bits = value.to_bits();
        values.extend([
            f32::from_bits(bits - 1),
            value,
            f32::from_bits(bits + 1),
            -value,
        ]);
    }
    for exponent in -149..=127 {
        values.push(2f32.powi(exponent));
    }
    let mut random = Xorshift(0xD1B5_4A32_D192_ED03);
    let target = values.len() + 2500;
    while values.len() < target {
        let value = f32::from_bits(random.next() as u32);
        if value.is_finite() {
            values.push(value);
        }
    }
    assert!(values.len() > 3_000, "{}", values.len());
    let cases: Vec<Case> = values.into_iter().map(f32_case).collect();
    run_program(&table_program("f32", &cases));
}

#[test]
fn non_finite_zero_integral_and_negative_values_use_rusts_text() {
    let cases: Vec<Case> = [
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        0.0,
        -0.0,
        1.0,
        -2.0,
        1e20,
        -1e20,
        1e-7,
        123456789012345680000.0,
    ]
    .into_iter()
    .map(f64_case)
    .collect();
    run_program(&table_program("f64", &cases));
    let cases: Vec<Case> = [
        f32::NAN,
        f32::INFINITY,
        f32::NEG_INFINITY,
        0.0,
        -0.0,
        1.0,
        1e20,
        1e-7,
    ]
    .into_iter()
    .map(f32_case)
    .collect();
    run_program(&table_program("f32", &cases));
}

#[test]
fn floats_mix_with_other_placeholders_widths_and_parameter_forms() {
    // `f32` values keep their own shortest text; widening to `f64` exposes
    // the exact binary value, which prints differently.
    let widened = f64::from(0.1f32);
    let mixed = format!("a=1 b={} c=true d={} e=x f={} g=é", 0.1f32, 2.5f64, widened);
    let source = format!(
        r#"{MIX}
fn show(x: f64, y: borrow f32) -> bool {{
    let s := "{{x}}/{{y}}";
    chk(s.borrow(), {len}, {hash})
}}
fn main() -> i32 {{
    let n: i32 = 1;
    let t: bool = true;
    let g: f32 = 0.1;
    let h: f64 = 2.5;
    let w: f64 = 0.1 as f32 as f64;
    let s := "a={{n}} b={{g}} c={{t}} d={{h}} e=x f={{w}} g=é";
    assert(chk(s.borrow(), {mixed_len}, {mixed_hash}));
    assert(show(1e21, g.borrow()));
    42
}}
"#,
        len = format!("{}/{}", 1e21f64, 0.1f32).len(),
        hash = mix(&format!("{}/{}", 1e21f64, 0.1f32)),
        mixed_len = mixed.len(),
        mixed_hash = mix(&mixed),
    );
    run_program(&source);
}

fn has_operator(wasm: &[u8], wanted: fn(&wasmparser::Operator) -> bool) -> bool {
    let mut found = false;
    for payload in wasmparser::Parser::new(0).parse_all(wasm) {
        if let wasmparser::Payload::CodeSectionEntry(body) = payload.unwrap() {
            let mut reader = body.get_operators_reader().unwrap();
            while !reader.eof() {
                found |= wanted(&reader.read().unwrap());
            }
        }
    }
    found
}

fn builds_with_float_formatter(source: &str) -> bool {
    let f = Fixture::new();
    project(&f, "", source);
    let path = build_wasm(&f, "probe.wasm");
    // `f64.ceil` appears only in the float formatter's scale estimate.
    has_operator(&fs::read(path).unwrap(), |op| {
        matches!(op, wasmparser::Operator::F64Ceil)
    })
}

#[test]
fn the_formatter_is_emitted_only_when_a_float_placeholder_is_reachable() {
    let integers =
        "fn main() -> i32 {\n    let n: i32 = 7;\n    let s := \"n={n}\";\n    s.len() as i32\n}\n";
    let floats = "fn main() -> i32 {\n    let x: f64 = 7.5;\n    let s := \"x={x}\";\n    s.len() as i32\n}\n";
    let unreachable = "fn unused() -> u32 {\n    let x: f64 = 7.5;\n    let s := \"x={x}\";\n    s.len()\n}\nfn main() -> i32 {\n    let n: i32 = 7;\n    let s := \"n={n}\";\n    s.len() as i32\n}\n";
    // A float local that is not interpolated does not pull it in either.
    let plain_float = "fn main() -> i32 {\n    let x: f64 = 7.5;\n    let n: i32 = 7;\n    let s := \"n={n}\";\n    s.len() as i32 + (x as i32)\n}\n";
    assert!(!builds_with_float_formatter(integers));
    assert!(builds_with_float_formatter(floats));
    assert!(!builds_with_float_formatter(unreachable));
    assert!(!builds_with_float_formatter(plain_float));
}

#[test]
fn constants_fold_with_the_same_text_and_need_no_formatter() {
    let f64_constants = [
        ("A", "0.1 + 0.2", 0.1f64 + 0.2),
        ("B", "1.0 / 3.0", 1.0f64 / 3.0),
        ("C", "1e300", 1e300),
        ("D", "5e-324", 5e-324),
        ("E", "0.0 / 0.0", f64::NAN),
        ("F", "1.0 / 0.0", f64::INFINITY),
        ("G", "-0.0", -0.0),
        ("H", "123456.0", 123456.0),
        ("I", "-1e20", -1e20),
    ];
    let f32_constants = [
        ("J", "0.1", 0.1f32),
        ("K", "1.0 / 3.0", 1.0f32 / 3.0),
        ("L", "3.4028235e38", f32::MAX),
        ("M", "1e-45", 1e-45f32),
    ];
    let mut source = String::from(MIX);
    for (name, expr, _) in f64_constants {
        source.push_str(&format!("const {name}: f64 = {expr};\n"));
    }
    for (name, expr, _) in f32_constants {
        source.push_str(&format!("const {name}: f32 = {expr};\n"));
    }
    source.push_str("fn main() -> i32 {\n");
    let mut expected = Vec::new();
    for (name, _, value) in f64_constants {
        expected.push((name, format!("{value}")));
    }
    for (name, _, value) in f32_constants {
        expected.push((name, format!("{value}")));
    }
    for (name, text) in &expected {
        source.push_str(&format!(
            "    let s{name} := \"{{{name}}}\";\n    assert(chk(s{name}.borrow(), {}, {}));\n",
            text.len(),
            mix(text)
        ));
    }
    // Folding leaves no formatter in the artifact.
    assert!(!builds_with_float_formatter(&format!(
        "{source}    42\n}}\n"
    )));
    // Constants and runtime values mix in one literal.
    let runtime: f64 = 2.5;
    let mixed = format!("{}|{}|{}", 0.1f64 + 0.2, runtime, 0.1f32);
    source.push_str(&format!(
        "    let r: f64 = 2.5;\n    let m := \"{{A}}|{{r}}|{{J}}\";\n    assert(chk(m.borrow(), {}, {}));\n    42\n}}\n",
        mixed.len(),
        mix(&mixed)
    ));
    run_program(&source);
}

#[test]
fn float_strings_in_loops_run_in_capped_memory_and_a_leak_would_trap() {
    const ITERATIONS: u32 = 4_096;
    let source = format!(
        r#"fn main() -> u32 {{
    var i: u32 = 0;
    var total: u32 = 0;
    loop {{
        if i == {ITERATIONS} {{ break; }}
        let k := i;
        i += 1;
        let x: f64 = (k as f64) * 1.1 / 7.0;
        let y: f32 = (k as f32) * 0.37;
        let s := "x={{x}} y={{y}} k={{k}}";
        total += s.len();
        if k % 3 == 0 {{ continue; }}
        let t := "{{s}}|{{x}}";
        if k % 5 == 0 {{ return total + t.len(); }}
        total += t.len();
    }}
    total
}}
"#
    );
    // The program returns early at the first k with k % 3 != 0 and
    // k % 5 == 0 (k = 5); use a loop-only variant for the long run instead.
    let source = source.replace("        if k % 5 == 0 { return total + t.len(); }\n", "");
    let mut expected: u64 = 0;
    for k in 0..ITERATIONS {
        let x = f64::from(k) * 1.1 / 7.0;
        let y = (k as f32) * 0.37;
        let s = format!("x={x} y={y} k={k}");
        expected += s.len() as u64;
        if k % 3 == 0 {
            continue;
        }
        expected += format!("{s}|{x}").len() as u64;
    }
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='f3-stress'\nentry='main::main'\n[build]\nstack_size=4096\n",
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
    let wasm_path = build_wasm(&f, "f3-stress.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&wasm_path).unwrap());
    fs::write(&wasm_path, capped).unwrap();
    let capped_run = f.run(&["run", "f3-stress.wasm", "--no-fuel-limit"]);
    assert!(
        capped_run.status.success() && capped_run.stderr.is_empty(),
        "capped Wasm run failed: {}",
        String::from_utf8_lossy(&capped_run.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&capped_run.stdout),
        format!("Result: i32({expected})\n")
    );
    assert_capped_memory(&wasm_path, initial, maximum);

    // Mutation: keep every formatted string alive in a list that is never
    // emptied. The same cap must now be exhausted and trap in the allocator.
    let leaking = r#"use alloc::List;
fn main() -> u32 {
    var kept: List<string> = [];
    var i: u32 = 0;
    loop {
        if i == 4096 { break; }
        let x: f64 = (i as f64) * 1.1 / 7.0;
        kept.push("x={x} i={i}");
        i += 1;
    }
    kept.len()
}
"#;
    f.write("src/main.mb", leaking);
    let leak_path = build_wasm(&f, "f3-leak.wasm");
    let (capped, _, _) = cap_memory(&fs::read(&leak_path).unwrap());
    fs::write(&leak_path, capped).unwrap();
    let leak_run = f.run(&["run", "f3-leak.wasm", "--no-fuel-limit"]);
    assert!(!leak_run.status.success());
    let stderr = String::from_utf8_lossy(&leak_run.stderr);
    assert!(stderr.contains("guest heap allocation failed"), "{stderr}");
}

#[test]
fn float_placeholders_need_the_alloc_layer_and_other_types_stay_rejected() {
    let f = Fixture::new();
    project(&f, "alloc = false", "fn main() {}\n");
    rejects(
        &f,
        "fn main() -> u32 {\n    let x: f64 = 1.5;\n    let s := \"{x}\";\n    s.len()\n}\n",
        "TE033",
        "alloc",
    );
    // Types other than the supported scalars keep the generic diagnostic,
    // which now names floats among the supported ones.
    let g = Fixture::new();
    project(&g, "", "fn main() {}\n");
    rejects(
        &g,
        "type P { x: f64 }\nfn main() -> u32 {\n    let p := P { x: 1.5 };\n    let s := \"{p}\";\n    s.len()\n}\n",
        "TE017",
        "supports integers, floats, bool, char and string",
    );
}

const TRANSPORT_ITERATIONS: u32 = 4_096;

/// A struct with a String and a List field plus an enum and a tuple that own
/// heap storage, moved by value into calls (consumed, ignored, returned and
/// dropped on an early return) in a loop.
fn transport_program(leak: bool) -> String {
    let leak_line = if leak {
        "        kept.push(\"{i}{i}{i}{i}{i}{i}{i}{i}{i}{i}{i}{i}{i}{i}{i}{i}{i}{i}{i}{i}\");\n"
    } else {
        ""
    };
    format!(
        r#"use alloc::List;
type Kind [ Word(string), Num(i32), Many(i32, string) ]
type M {{ name: string, k: Kind, t: (string, i32), l: List<i32>, n: u32 }}
fn mk(i: u32) -> M {{
    let kind := if i % 3 == 0 {{
        Kind::Word("w{{i}}")
    }} else if i % 3 == 1 {{
        Kind::Num(i as i32)
    }} else {{
        Kind::Many(i as i32, "m{{i}}")
    }};
    var l: List<i32> = [];
    var j: u32 = 0;
    loop {{
        if j == i % 4 + 1 {{ break; }}
        l.push(j as i32);
        j += 1;
    }}
    M {{ name: "n{{i}}", k: kind, t: ("t{{i}}", 1), l: l, n: i }}
}}
fn size(m: M) -> u32 {{
    let base := m.name.len() + m.t.0.len() + m.n + m.l.len();
    match m.k {{
        Word(w) => base + w.len(),
        Num(n) => base + (n as u32),
        Many(a, b) => base + b.len() + (a as u32),
    }}
}}
fn ignore(m: M, flag: u32) -> u32 {{
    if flag == 1 {{ return 7; }}
    3
}}
fn early(m: M, flag: u32) -> u32 {{
    if flag == 1 {{ return 5; }}
    size(m) + 1
}}
fn pass(m: M) -> M {{ m }}
fn main() -> u32 {{
    var kept: List<string> = [];
    var i: u32 = 0;
    var total: u32 = 0;
    loop {{
        if i == {TRANSPORT_ITERATIONS} {{ break; }}
{leak_line}        total += size(mk(i));
        total += ignore(mk(i), i % 2);
        total += early(mk(i), i % 5);
        let back := pass(mk(i));
        total += size(back);
        i += 1;
    }}
    total + kept.len()
}}
"#
    )
}

fn transport_expected() -> u64 {
    let digits = |i: u32| i.to_string().len() as u64;
    let size = |i: u32| {
        let d = digits(i);
        let base = (1 + d) + (1 + d) + u64::from(i) + u64::from(i % 4 + 1);
        base + match i % 3 {
            0 => 1 + d,
            1 => u64::from(i),
            _ => (1 + d) + u64::from(i),
        }
    };
    (0..TRANSPORT_ITERATIONS)
        .map(|i| {
            let ignore = if i % 2 == 1 { 7 } else { 3 };
            let early = if i % 5 == 1 { 5 } else { size(i) + 1 };
            size(i) + ignore + early + size(i)
        })
        .sum()
}

#[test]
fn a_struct_with_string_list_enum_and_tuple_fields_moves_into_calls_in_capped_memory() {
    let expected = transport_expected();
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='f3-transport'\nentry='main::main'\n[build]\nstack_size=8192\n",
    );
    f.write("src/main.mb", &transport_program(false));
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
    let wasm_path = build_wasm(&f, "f3-transport.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&wasm_path).unwrap());
    fs::write(&wasm_path, capped).unwrap();
    let capped_run = f.run(&["run", "f3-transport.wasm", "--no-fuel-limit"]);
    assert!(
        capped_run.status.success() && capped_run.stderr.is_empty(),
        "capped Wasm run failed: {}",
        String::from_utf8_lossy(&capped_run.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&capped_run.stdout),
        format!("Result: i32({expected})\n")
    );
    assert_capped_memory(&wasm_path, initial, maximum);

    // Mutation: the same loop that also keeps one 20-digit String per
    // iteration alive must exhaust the one extra page and trap.
    f.write("src/main.mb", &transport_program(true));
    let leak_path = build_wasm(&f, "f3-transport-leak.wasm");
    let (capped, _, _) = cap_memory(&fs::read(&leak_path).unwrap());
    fs::write(&leak_path, capped).unwrap();
    let leak_run = f.run(&["run", "f3-transport-leak.wasm", "--no-fuel-limit"]);
    assert!(!leak_run.status.success());
    let stderr = String::from_utf8_lossy(&leak_run.stderr);
    assert!(stderr.contains("guest heap allocation failed"), "{stderr}");
}

#[test]
fn plain_enum_and_tuple_fields_do_not_block_transport_and_enum_only_structs_stay_out() {
    let f = Fixture::new();
    project(
        &f,
        "",
        "type Kind [ Num(i32), Other ]\ntype M { name: string, k: Kind, t: (i32, bool), n: u32 }\n\
fn size(m: M) -> u32 {\n    match m.k { Num(n) => m.name.len() + (n as u32) + (m.t.0 as u32), Other => 9 }\n}\n\
fn main() -> i32 {\n    let s := size(M { name: \"a\".concat(\"b\"), k: Kind::Num(3), t: (4, true), n: 1 });\n    assert(s == 9);\n    42\n}\n",
    );
    run_source_and_wasm(&f, OK);
}
