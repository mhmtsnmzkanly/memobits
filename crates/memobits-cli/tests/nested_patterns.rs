//! Nested `match` patterns end to end: constructor patterns at any depth over
//! enums, built-in `T?` / `T ! E` and tuples, with `_` and bindings in any
//! position. Covers source and standalone Wasm results, coverage diagnostics,
//! in-place matches, and exactly-once release of owned heap Strings under a
//! capped Wasm memory.
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
            "memobits-nested-patterns-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let fixture = Self(path);
        fixture.write(
            "project.toml",
            "[package]\nname='nested-patterns'\nentry='app::main'\n[build]\nstack_size=4096\n",
        );
        fixture
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

    /// Run from source and from the built artifact; both must agree and the
    /// artifact run must leave stderr empty. Returns the printed result.
    fn result(&self, source: &str) -> String {
        self.write("src/app.mb", source);
        let from_source = self.run(&["run"]);
        assert!(
            from_source.status.success(),
            "{source}: {}",
            String::from_utf8_lossy(&from_source.stderr)
        );
        let built = self.run(&["build"]);
        assert!(
            built.status.success(),
            "{source}: {}",
            String::from_utf8_lossy(&built.stderr)
        );
        let from_artifact = self.run(&["run", "target/memobits/app.wasm"]);
        assert!(from_artifact.status.success());
        assert!(from_artifact.stderr.is_empty());
        assert_eq!(from_source.stdout, from_artifact.stdout, "{source}");
        String::from_utf8(from_source.stdout).unwrap().trim().into()
    }

    /// The diagnostic text of a program that must fail to compile with `code`.
    fn error(&self, source: &str, code: &str) -> String {
        self.write("src/app.mb", source);
        let output = self.run(&["run"]);
        assert_eq!(output.status.code(), Some(1), "{source}");
        assert!(output.stdout.is_empty());
        let text = String::from_utf8(output.stderr).unwrap();
        assert!(text.contains(code), "{source}: {text}");
        text
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn optional_fallible_values_match_nested_variants() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "fn classify(r: u32? ! Error) -> u32 {
                 match r {
                     Ok(Some(v)) => v + 100,
                     Ok(None) => 7,
                     Err(e) => e.code,
                 }
             }
             fn main() -> i32 {
                 let a: u32? ! Error = Ok(Some(5));
                 let b: u32? ! Error = Ok(None);
                 let c: u32? ! Error = Err(Error { code: 9 });
                 (classify(a) + classify(b) + classify(c)) as i32
             }"
        ),
        "Result: i32(121)"
    );
}

#[test]
fn user_enums_nest_three_levels_with_wildcards_and_bindings() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "type Point [ Origin, At(i32, i32) ]
             type Inner [ Leaf(i32), Pair(Point, Point), Empty ]
             type Mid [ Wrap(Inner), Two(Inner, u32), Nothing ]
             type Outer [ Top(Mid), Other(u32) ]
             fn score(o: Outer) -> i32 {
                 match o {
                     Outer::Top(Mid::Wrap(Inner::Leaf(n))) => n,
                     Outer::Top(Mid::Wrap(Inner::Pair(Point::Origin, Point::At(x, y)))) => x + y + 1000,
                     Outer::Top(Mid::Wrap(Inner::Pair(Point::At(x, _), other))) => x + 2000,
                     Outer::Top(Mid::Wrap(Inner::Pair(Point::Origin, Point::Origin))) => 3000,
                     Outer::Top(Mid::Wrap(Inner::Empty)) => 4000,
                     Outer::Top(Mid::Two(Inner::Leaf(a), b)) => a + (b as i32) + 5000,
                     Outer::Top(Mid::Two(_, b)) => (b as i32) + 6000,
                     Outer::Top(Mid::Nothing) => 7000,
                     Outer::Other(n) => n as i32 + 8000,
                 }
             }
             fn main() -> i32 {
                 score(Outer::Top(Mid::Wrap(Inner::Leaf(1))))
                   + score(Outer::Top(Mid::Wrap(Inner::Pair(Point::Origin, Point::At(2, 3)))))
                   + score(Outer::Top(Mid::Wrap(Inner::Pair(Point::At(4, 5), Point::Origin))))
                   + score(Outer::Top(Mid::Wrap(Inner::Pair(Point::Origin, Point::Origin))))
                   + score(Outer::Top(Mid::Wrap(Inner::Empty)))
                   + score(Outer::Top(Mid::Two(Inner::Leaf(10), 20)))
                   + score(Outer::Top(Mid::Two(Inner::Empty, 30)))
                   + score(Outer::Top(Mid::Nothing))
                   + score(Outer::Other(40))
             }"
        ),
        "Result: i32(36110)"
    );
}

#[test]
fn tuple_patterns_nest_in_payloads_and_match_tuple_scrutinees() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "type Cell [ Pair((i32, i32)), Triple((i32, (u32, bool))), Nope ]
             type Holder { c: Cell, k: u32 }
             fn owned(c: Cell) -> i32 {
                 match c {
                     Cell::Pair((a, b)) => a * 10 + b,
                     Cell::Triple((a, (b, flag))) => if flag { a + (b as i32) + 100 } else { a + 200 },
                     Cell::Nope => 300,
                 }
             }
             fn tuples(a: i32?, b: i32?) -> i32 {
                 match (a, b) {
                     (Some(x), Some(y)) => x + y,
                     (Some(x), None) => x,
                     (None, Some(y)) => y * 2,
                     (None, None) => 0,
                 }
             }
             fn main() -> i32 {
                 let h := Holder { c: Cell::Triple((5, (6, false))), k: 1 };
                 let r := match h.c {
                     Cell::Triple((a, (b, _))) => a * 1000 + (b as i32),
                     _ => 0,
                 };
                 owned(Cell::Pair((3, 4))) + owned(Cell::Triple((1, (2, true))))
                   + owned(Cell::Triple((1, (2, false)))) + owned(Cell::Nope) + r
                   + tuples(Some(1), Some(2)) + tuples(Some(5), None)
                   + tuples(None, Some(7)) + tuples(None, None)
             }"
        ),
        "Result: i32(5666)"
    );
}

#[test]
fn wildcard_heavy_arms_select_the_first_matching_arm() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "fn pick(a: i32? ! Error, b: u32?) -> i32 {
                 match (a, b) {
                     (Ok(Some(x)), Some(y)) => x + (y as i32),
                     (Ok(Some(_)), _) => 100,
                     (Ok(None), Some(_)) => 200,
                     (Err(_), Some(y)) => 300 + (y as i32),
                     (_, None) => 400,
                 }
             }
             fn deep(r: i32?? ! Error) -> i32 {
                 match r {
                     Ok(Some(Some(v))) => v,
                     Ok(Some(_)) => 10,
                     Ok(_) => 20,
                     _ => 30,
                 }
             }
             fn main() -> i32 {
                 let e: i32? ! Error = Err(Error { code: 1 });
                 let n: i32? ! Error = Ok(None);
                 let s: i32? ! Error = Ok(Some(1));
                 let s2: i32? ! Error = Ok(Some(1));
                 let some_some: i32?? ! Error = Ok(Some(Some(4)));
                 let some_none: i32?? ! Error = Ok(Some(None));
                 let none: i32?? ! Error = Ok(None);
                 let err: i32?? ! Error = Err(Error { code: 2 });
                 pick(s, Some(2)) + pick(s2, None) + pick(n, Some(1)) + pick(e, Some(5))
                   + deep(some_some) + deep(some_none) + deep(none) + deep(err)
             }"
        ),
        // pick: 3 + 100 + 200 + 305; deep: 4 + 10 + 20 + 30
        "Result: i32(672)"
    );
}

#[test]
fn in_place_matches_copy_primitives_and_lend_nested_aggregates() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "type Msg [ Pair(u32, (u32, u32)), Nil ]
             type Env [ Full(Msg, u32), Part(Msg), Gone ]
             type Hold { e: Env }
             fn look(e: borrow Env) -> u32 {
                 match e {
                     Env::Full(Msg::Pair(k, (a, _)), n) => k + a + n,
                     Env::Full(Msg::Nil, n) => n + 200,
                     Env::Part(Msg::Pair(_, p)) => 300,
                     Env::Part(m) => 400,
                     Env::Gone => 500,
                 }
             }
             fn shared(e: share Env) -> u32 {
                 match e {
                     Env::Part(Msg::Nil) => 1,
                     _ => 2,
                 }
             }
             fn main() -> i32 {
                 var e1 := Env::Full(Msg::Pair(1, (2, 3)), 4);
                 let e2 := Env::Part(Msg::Nil);
                 let h := Hold { e: Env::Part(Msg::Pair(5, (6, 7))) };
                 let inner := match h.e {
                     Env::Part(Msg::Pair(a, (b, c))) => a + b + c,
                     _ => 0,
                 };
                 (look(e1.borrow()) + look(e2.borrow()) + shared(e1.share()) + inner) as i32
             }"
        ),
        "Result: i32(427)"
    );
}

#[test]
fn nested_patterns_work_inside_attempt_and_option_containers() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "fn att(a: Attempt<u32, Error>?) -> u32 {
                 match a {
                     Some(Done(v)) => v,
                     Some(Skipped) => 1000,
                     Some(Failed(e)) => e.code + 2000,
                     None => 3000,
                 }
             }
             fn main() -> i32 {
                 (att(Some(Done(5))) + att(Some(Skipped)) + att(None)) as i32
             }"
        ),
        "Result: i32(4005)"
    );
}

#[test]
fn flat_matches_behave_as_before() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "type Shape [ Empty, Circle(i32), Rect(i32, i32) ]
             fn area(s: Shape) -> i32 {
                 match s { Shape::Empty => 0, Shape::Circle(r) => r * 3, Shape::Rect(w, h) => w * h }
             }
             fn main() -> i32 {
                 let o: i32? = Some(4);
                 area(Shape::Empty) + area(Shape::Circle(2)) + area(Shape::Rect(3, 5))
                   + match o { Some(v) => v, None => 0 }
             }"
        ),
        "Result: i32(25)"
    );
}

const FALLIBLE: &str = "fn r(c: u32) -> u32? ! Error { Ok(Some(c)) }\n";

#[test]
fn missing_nested_cases_are_named_with_an_example_pattern() {
    let f = Fixture::new();
    let text = f.error(
        &format!("{FALLIBLE}fn f(x: u32? ! Error) -> u32 {{ match x {{ Ok(Some(v)) => v, Err(e) => e.code }} }}\nfn main() -> i32 {{ 0 }}"),
        "TE031",
    );
    assert!(text.contains("missing `Ok(None)`"), "{text}");
    let text = f.error(
        "type Leaf [ A, B(u32) ]\ntype Mid [ X(Leaf), Y ]\n\
         fn f(m: Mid) -> u32 { match m { Mid::X(Leaf::A) => 1, Mid::Y => 2 } }\nfn main() -> i32 { 0 }",
        "TE031",
    );
    assert!(text.contains("missing `Mid::X(Leaf::B(_))`"), "{text}");
    let text = f.error(
        "fn f(x: u32? ! Error) -> u32 { match x { Ok(Some(v)) => v } }\nfn main() -> i32 { 0 }",
        "TE031",
    );
    assert!(
        text.contains("`Ok(None)`") && text.contains("`Err(_)`"),
        "{text}"
    );
    let text = f.error(
        "fn f(a: u32?, b: u32?) -> u32 { match (a, b) { (Some(x), _) => x, (None, Some(y)) => y } }\nfn main() -> i32 { 0 }",
        "TE031",
    );
    assert!(text.contains("`(None, None)`"), "{text}");
}

#[test]
fn unreachable_nested_arms_are_rejected() {
    let f = Fixture::new();
    let text = f.error(
        "fn f(x: u32? ! Error) -> u32 { match x { Ok(Some(v)) => v, Ok(None) => 1, Ok(None) => 2, Err(_) => 3 } }\nfn main() -> i32 { 0 }",
        "TE032",
    );
    assert!(text.contains("`Ok(None)` is already matched"), "{text}");
    let text = f.error(
        "fn f(x: u32? ! Error) -> u32 { match x { Ok(_) => 1, Ok(Some(v)) => v, Err(_) => 3 } }\nfn main() -> i32 { 0 }",
        "TE032",
    );
    assert!(text.contains("`Ok(Some(v))`"), "{text}");
    f.error(
        "fn f(x: u32? ! Error) -> u32 { match x { Ok(Some(v)) => v, Ok(None) => 1, Err(_) => 3, _ => 4 } }\nfn main() -> i32 { 0 }",
        "TE032",
    );
}

#[test]
fn malformed_nested_patterns_keep_their_codes() {
    let f = Fixture::new();
    f.error(
        "fn f(x: u32? ! Error) -> u32 { match x { Ok(Some(a, b)) => a, _ => 0 } }\nfn main() -> i32 { 0 }",
        "TE030",
    );
    f.error(
        "fn f(x: u32? ! Error) -> u32 { match x { Ok((a, b)) => a, _ => 0 } }\nfn main() -> i32 { 0 }",
        "TE030",
    );
    f.error(
        "fn f(x: u32? ! Error) -> u32 { match x { Ok(Some(a)) => a, Ok(a) => 1, Ok(None) => 2, Err(e) => e.code, Err(a, a) => 0 } }\nfn main() -> i32 { 0 }",
        "TE030",
    );
    f.error(
        "type T [ A(u32, u32), B ]\nfn f(x: T) -> u32 { match x { T::A(a, a) => a, T::B => 0 } }\nfn main() -> i32 { 0 }",
        "TE030",
    );
    f.error(
        "fn f(x: u32? ! Error) -> u32 { match x { Ok(Some(1)) => 1, _ => 0 } }\nfn main() -> i32 { 0 }",
        "SE002",
    );
}

// ---- release of owned heap Strings under a capped Wasm memory ----

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

/// Lower the memory maximum to one page above the initial size, so a program
/// that leaked heap blocks across 8,192 iterations cannot finish.
fn cap_memory(bytes: &[u8]) -> Vec<u8> {
    assert_eq!(&bytes[..8], b"\0asm\x01\0\0\0");
    let mut module = bytes[..8].to_vec();
    let mut section_start = 8;
    let mut capped = false;
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
            assert!(initial < old_maximum);
            let mut payload = bytes[payload_start..maximum_start].to_vec();
            write_uleb(initial + 1, &mut payload);
            payload.extend_from_slice(&bytes[cursor..section_end]);
            module.push(id);
            write_uleb(payload.len() as u32, &mut module);
            module.extend_from_slice(&payload);
            capped = true;
        }
        section_start = section_end;
    }
    assert!(capped, "Wasm memory section");
    module
}

/// Run `source` from source and from a memory-capped artifact.
fn assert_capped_result(source: &str, expected: &str) {
    let f = Fixture::new();
    f.write("src/app.mb", source);
    let from_source = f.run(&["run"]);
    assert!(
        from_source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&from_source.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&from_source.stdout).trim(),
        expected
    );
    let build = f.run(&["build", "--output", "capped.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let path = f.0.join("capped.wasm");
    let original = fs::read(&path).unwrap();
    fs::write(&path, cap_memory(&original)).unwrap();
    let wasm = f.run(&["run", "capped.wasm"]);
    assert!(
        wasm.status.success(),
        "capped Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert!(wasm.stderr.is_empty());
    assert_eq!(
        String::from_utf8_lossy(&wasm.stdout).trim(),
        expected.replace("u32", "i32")
    );
}

#[test]
fn nested_string_payloads_release_exactly_once_on_every_arm_and_early_return() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let mut expected = 0;
    for i in 0..ITERATIONS {
        let (early, kind) = (i % 2 == 0, i % 3);
        expected += if early {
            1
        } else {
            [4096, 7, 4][kind as usize]
        };
        expected += if early { 2 } else { [5, 6, 8][kind as usize] };
        expected += if early {
            3
        } else {
            [4097, 10, 10][kind as usize]
        };
    }
    assert_capped_result(
        &format!(
            "fn pack(text: string, kind: u32) -> string? ! Error {{
                 if kind == 2 {{ return Err(Error {{ code: 4 }}); }}
                 if kind == 1 {{ return Ok(None); }}
                 let some: string? = Some(text);
                 let result: string? ! Error = Ok(some);
                 result
             }}
             fn bound(r: string? ! Error, early: bool) -> u32 {{
                 if early {{ return 1; }}
                 match r {{
                     Ok(Some(s)) => s.len(),
                     Ok(None) => 7,
                     Err(e) => e.code,
                 }}
             }}
             fn ignored(r: string? ! Error, early: bool) -> u32 {{
                 if early {{ return 2; }}
                 match r {{
                     Ok(Some(_)) => 5,
                     Ok(None) => 6,
                     Err(_) => 8,
                 }}
             }}
             fn mixed(r: string? ! Error, early: bool) -> u32 {{
                 if early {{ return 3; }}
                 match r {{
                     Ok(Some(s)) => s.len() + 1,
                     _ => 10,
                 }}
             }}
             fn main() -> u32 {{
                 var i: u32 = 0;
                 var total: u32 = 0;
                 loop {{
                     if i == {ITERATIONS} {{ break; }}
                     let kind := i % 3;
                     let early := i % 2 == 0;
                     let first := pack(\"{text}\".concat(\"\"), kind);
                     total += bound(first, early);
                     let second := pack(\"{text}\".concat(\"\"), kind);
                     total += ignored(second, early);
                     let third := pack(\"{text}\".concat(\"\"), kind);
                     total += mixed(third, early);
                     i += 1;
                 }}
                 total
             }}"
        ),
        &format!("Result: u32({expected})"),
    );
}

#[test]
fn nested_enum_and_tuple_string_payloads_release_unbound_parts_under_the_cap() {
    const ITERATIONS: u32 = 8_192;
    const TEXT_BYTES: usize = 4_096;
    let text = "y".repeat(TEXT_BYTES);
    let mut expected = 0;
    for i in 0..ITERATIONS {
        let (early, kind) = (i % 2 == 0, i % 4);
        expected += if early {
            1
        } else {
            [
                TEXT_BYTES as u32 + i % 7,
                2 * TEXT_BYTES as u32 + 100,
                2 + 300,
                500,
            ][kind as usize]
        };
    }
    assert_capped_result(
        &format!(
            "type Msg [ Text(string), Pair((string, string)), Nil ]
             type Env [ Full(Msg, u32), Part(Msg), Gone ]
             fn inspect(e: Env, early: bool) -> u32 {{
                 if early {{ return 1; }}
                 match e {{
                     Env::Full(Msg::Text(s), n) => s.len() + n,
                     Env::Full(Msg::Pair((a, b)), _) => a.len() + b.len() + 100,
                     Env::Full(Msg::Nil, n) => n + 200,
                     Env::Part(Msg::Pair((_, b))) => b.len() + 300,
                     Env::Part(_) => 500,
                     Env::Gone => 600,
                 }}
             }}
             fn main() -> u32 {{
                 var i: u32 = 0;
                 var total: u32 = 0;
                 loop {{
                     if i == {ITERATIONS} {{ break; }}
                     let early := i % 2 == 0;
                     let a := \"{text}\".concat(\"\");
                     let b := \"{text}\".concat(\"\");
                     if i % 4 == 0 {{
                         let msg := Msg::Text(a);
                         let env := Env::Full(msg, i % 7);
                         total += inspect(env, early);
                     }} else if i % 4 == 1 {{
                         let msg := Msg::Pair((a, b));
                         let env := Env::Full(msg, 0);
                         total += inspect(env, early);
                     }} else if i % 4 == 2 {{
                         let c := \"zz\".concat(\"\");
                         let msg := Msg::Pair((a, c));
                         let env := Env::Part(msg);
                         total += inspect(env, early);
                     }} else {{
                         let msg := Msg::Text(a);
                         let env := Env::Part(msg);
                         total += inspect(env, early);
                     }}
                     i += 1;
                 }}
                 total
             }}"
        ),
        &format!("Result: u32({expected})"),
    );
}
