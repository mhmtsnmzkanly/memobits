//! End-to-end nested aggregate programs (package A3): source runs, built
//! artifacts and the diagnostics users see for nesting.
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
            "memobits-nesting-cli-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let fixture = Self(path);
        fixture.write(
            "project.toml",
            "[package]\nname='nesting'\nentry='app::main'\n",
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
    /// Run a program from source and again from its built artifact; both must agree.
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
        assert_eq!(from_source.stdout, from_artifact.stdout, "{source}");
        String::from_utf8(from_source.stdout).unwrap().trim().into()
    }
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

const TYPES: &str = "type P { x: i32, y: i32 }\n\
    type Line { a: P, b: P }\n\
    type Poly { n: u8, pts: array<i32, 4>, c: P }\n";

#[test]
fn a_particle_system_mutates_nested_arrays_and_sums_through_a_borrow() {
    let f = Fixture::new();
    // Three polygons of four points each; a nested loop bumps every point by
    // its polygon index, then a borrow parameter sums all of them.
    assert_eq!(
        f.result(
            "type Pt { x: i32, y: i32 }\n\
             type Poly { id: u8, pts: array<Pt, 4> }\n\
             fn make() -> Poly { Poly { id: 0, pts: [Pt { x: 1, y: 2 }; 4] } }\n\
             fn total(polys: borrow array<Poly, 3>) -> i32 {\n\
                 var sum := 0;\n\
                 var i := 0;\n\
                 loop {\n\
                     if i == 3 { break; }\n\
                     var j := 0;\n\
                     loop {\n\
                         if j == 4 { break; }\n\
                         sum += polys[i].pts[j].x + polys[i].pts[j].y;\n\
                         j += 1;\n\
                     }\n\
                     i += 1;\n\
                 }\n\
                 sum\n\
             }\n\
             fn main() -> i32 {\n\
                 var polys := [make(), make(), make()];\n\
                 var i := 0;\n\
                 loop {\n\
                     if i == 3 { break; }\n\
                     polys[i].id = 7;\n\
                     var j := 0;\n\
                     loop {\n\
                         if j == 4 { break; }\n\
                         polys[i].pts[j].x += i;\n\
                         polys[i].pts[j].y = polys[i].pts[j].y * 2;\n\
                         j += 1;\n\
                     }\n\
                     i += 1;\n\
                 }\n\
                 total(polys.borrow())\n\
             }"
        ),
        // Per point: x = 1 + i, y = 4; per polygon 4 * (5 + i); i = 0, 1, 2: 20 + 24 + 28.
        "Result: i32(72)"
    );
}

#[test]
fn nested_structs_and_array_fields_read_write_and_replace() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{TYPES}\
             fn make_p() -> P {{ P {{ x: 7, y: 8 }} }}\n\
             fn main() -> i32 {{\n\
                 var l := Line {{ a: P {{ x: 1, y: 2 }}, b: make_p() }};\n\
                 l.a.x = 10;\n\
                 l.b.y += 5;\n\
                 l.a = P {{ x: 100, y: 200 }};\n\
                 let o := P {{ x: 3, y: 4 }};\n\
                 l.b = o;\n\
                 var poly := Poly {{ n: 1, pts: [1, 2, 3, 4], c: P {{ x: 5, y: 6 }} }};\n\
                 poly.pts[2] += 10;\n\
                 poly.pts = [4, 3, 2, 1];\n\
                 var arr := [P {{ x: 0, y: 0 }}; 3];\n\
                 arr[1].x = 9;\n\
                 arr[2] = P {{ x: 1, y: 1 }};\n\
                 l.a.x + l.a.y + l.b.x + poly.pts[0] + poly.c.x + arr[1].x + arr[2].y\n\
             }}"
        )),
        "Result: i32(322)"
    );
}

#[test]
fn mixed_widths_nest_inside_structs_inside_arrays() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "type Q { a: u8, b: i64, f: f32, ok: bool }\n\
             type R { tag: u8, q: Q, xs: array<Q, 2>, last: i16 }\n\
             fn bump(r: share R) { r.xs[1].b += 5; r.xs[0].ok = true; r.last = -3; r.q.f = 2.5; }\n\
             fn mk() -> R {\n\
                 R { tag: 1, q: Q { a: 1, b: 2, f: 0.5, ok: false },\n\
                     xs: [Q { a: 7, b: 8, f: 1.0, ok: true }, Q { a: 9, b: 10, f: 1.5, ok: false }],\n\
                     last: 11 }\n\
             }\n\
             fn score(r: borrow R) -> i32 {\n\
                 var s := 0;\n\
                 if r.tag == 1 { s += 1; }\n\
                 if r.q.a == 1 { s += 2; }\n\
                 if r.q.b == 2 { s += 4; }\n\
                 if r.q.f == 2.5 { s += 8; }\n\
                 if r.q.ok { s += 100000; }\n\
                 if r.xs[0].a == 7 { s += 16; }\n\
                 if r.xs[0].b == 8 { s += 32; }\n\
                 if r.xs[0].ok { s += 64; }\n\
                 if r.xs[1].a == 9 { s += 128; }\n\
                 if r.xs[1].b == 15 { s += 256; }\n\
                 if r.xs[1].ok { s += 200000; }\n\
                 if r.last == -3 { s += 512; }\n\
                 s\n\
             }\n\
             fn main() -> i32 { var r := mk(); bump(r.share()); score(r.borrow()) }"
        ),
        "Result: i32(1023)"
    );
}

#[test]
fn evaluation_order_is_indices_then_value_then_the_bounds_checked_store() {
    let f = Fixture::new();
    let log = "type P { pts: array<i32, 2> }\n\
        fn step(log: share i32, tag: i32, out: i32) -> i32 { log = log * 10 + tag; out }\n";
    // f, g, then h; the log records 1, 2, 3 and the value 42 lands at [1][1].
    assert_eq!(
        f.result(&format!(
            "{log}fn main() -> i32 {{\n\
                 var log := 0;\n\
                 var a := [P {{ pts: [0, 0] }}, P {{ pts: [0, 0] }}];\n\
                 a[step(log.share(), 1, 1)].pts[step(log.share(), 2, 1)] = step(log.share(), 3, 42);\n\
                 log * 1000 + a[1].pts[1]\n\
             }}"
        )),
        "Result: i32(123042)"
    );
    // An out-of-range inner index still evaluates the right-hand side first,
    // and the trap happens before any store.
    f.write(
        "src/app.mb",
        &format!(
            "{log}fn main() -> i32 {{\n\
                 var log := 0;\n\
                 var a := [P {{ pts: [0, 0] }}, P {{ pts: [0, 0] }}];\n\
                 a[step(log.share(), 1, 1)].pts[step(log.share(), 2, 5)] = step(log.share(), 3, 42);\n\
                 log\n\
             }}"
        ),
    );
    let output = f.run(&["run"]);
    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stderr).contains("RE007"));
}

#[test]
fn bounds_traps_fire_at_each_level() {
    let f = Fixture::new();
    for access in [
        "a[i].pts[0]",
        "a[0].pts[j]",
        "a[0].pts[j] = 1; 0",
        "a[i].c.x",
        "l.a.x + b[j].x",
    ] {
        f.write(
            "src/app.mb",
            &format!(
                "{TYPES}fn main() -> i32 {{\n\
                 var a := [Poly {{ n: 1, pts: [1, 2, 3, 4], c: P {{ x: 5, y: 6 }} }}; 2];\n\
                 var b := [P {{ x: 1, y: 1 }}; 2];\n\
                 var l := Line {{ a: P {{ x: 1, y: 2 }}, b: P {{ x: 3, y: 4 }} }};\n\
                 var i := 2; var j := 4;\n\
                 {access}\n}}"
            ),
        );
        let output = f.run(&["run"]);
        assert_eq!(output.status.code(), Some(1), "{access}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("RE007"),
            "{access}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn zero_length_arrays_of_structs_and_per_element_repetition() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "type P { x: i32 }\n\
             type Z { e: array<P, 0>, n: i32 }\n\
             fn main() -> i32 { let a: array<P, 0> = [P { x: 1 }; 0]; let z := Z { e: a, n: 5 }; z.n }"
        ),
        "Result: i32(5)"
    );
    assert_eq!(
        f.result(
            "type P { x: i32, y: i32 }\n\
             fn next(c: share i32) -> i32 { c += 1; c + 0 }\n\
             fn main() -> i32 {\n\
                 var c := 0;\n\
                 let a := [P { x: next(c.share()), y: 0 }; 4];\n\
                 a[0].x * 1000 + a[1].x * 100 + a[2].x * 10 + a[3].x + c * 10000\n\
             }"
        ),
        "Result: i32(41234)"
    );
}

#[test]
fn sub_aggregates_can_be_lent_and_disjoint_fields_are_independent() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{TYPES}\
             fn read(p: borrow P) -> i32 {{ p.x * 10 + p.y }}\n\
             fn bump(p: share P) {{ p.x += 1; }}\n\
             fn first(a: borrow array<i32, 4>) -> i32 {{ a[0] }}\n\
             fn main() -> i32 {{\n\
                 var l := Line {{ a: P {{ x: 1, y: 2 }}, b: P {{ x: 3, y: 4 }} }};\n\
                 bump(l.a.share());\n\
                 bump(l.b.share());\n\
                 var arr := [P {{ x: 5, y: 6 }}; 2];\n\
                 bump(arr[1].share());\n\
                 var poly := Poly {{ n: 1, pts: [9, 8, 7, 6], c: P {{ x: 0, y: 0 }} }};\n\
                 read(l.a.borrow()) + read(l.b.borrow()) + read(arr[1].borrow()) + first(poly.pts.borrow())\n\
             }}"
        )),
        // 22 + 44 + 66 + 9
        "Result: i32(141)"
    );
    // A4: a live reference to l.a does not block writing l.b.
    assert_eq!(
        f.result(&format!(
            "{TYPES}fn main() -> i32 {{\n\
                 var l := Line {{ a: P {{ x: 1, y: 2 }}, b: P {{ x: 3, y: 4 }} }};\n\
                 let r := l.a.borrow();\n\
                 l.b.x = 5;\n\
                 r.x * 10 + l.b.x\n\
             }}"
        )),
        "Result: i32(15)"
    );
    // ... but writing the same field, or the whole root, still conflicts.
    for write in [
        "l.a.x = 5;",
        "l = Line { a: P { x: 0, y: 0 }, b: P { x: 0, y: 0 } };",
    ] {
        let message = f.error(
            &format!(
                "{TYPES}fn main() -> i32 {{\n\
                     var l := Line {{ a: P {{ x: 1, y: 2 }}, b: P {{ x: 3, y: 4 }} }};\n\
                     let r := l.a.borrow();\n\
                     {write}\n\
                     r.x\n\
                 }}"
            ),
            "BE005",
        );
        assert!(message.contains(write), "{message}");
    }
}

#[test]
fn moving_a_sub_aggregate_out_is_te022() {
    let f = Fixture::new();
    for (statement, what) in [
        ("let q := l.a;", "field"),
        ("let q := a[1];", "element"),
        ("let q := p.pts;", "field"),
        ("take(l.a);", "field"),
        ("take(a[0]);", "element"),
        ("l.b = l.a;", "field"),
        ("a[0] = a[1];", "element"),
        ("let q := [a[0], a[1]];", "element"),
    ] {
        let source = format!(
            "{TYPES}fn take(p: P) {{}}\n\
             fn main() -> i32 {{\n\
                 var l := Line {{ a: P {{ x: 1, y: 2 }}, b: P {{ x: 3, y: 4 }} }};\n\
                 var a := [P {{ x: 0, y: 0 }}; 2];\n\
                 var p := Poly {{ n: 1, pts: [1, 2, 3, 4], c: P {{ x: 5, y: 6 }} }};\n\
                 {statement}\n\
                 0\n\
             }}"
        );
        let message = f.error(&source, "TE022");
        assert!(message.contains("partial moves are deferred"), "{message}");
        assert!(
            message.contains(&format!("{what} cannot be moved out")),
            "{statement}: {message}"
        );
    }
    for source in [
        format!("{TYPES}fn f(l: Line) -> P {{ return l.a; }}\nfn main() -> i32 {{ 0 }}"),
        format!("{TYPES}fn f(l: Line) -> P {{ l.a }}\nfn main() -> i32 {{ 0 }}"),
        format!("{TYPES}fn f(a: array<P, 2>) -> P {{ a[0] }}\nfn main() -> i32 {{ 0 }}"),
    ] {
        f.error(&source, "TE022");
    }
}

#[test]
fn recursive_containment_through_arrays_is_rejected() {
    let f = Fixture::new();
    for source in [
        "type A { xs: array<A, 2> }\nfn main() -> i32 { 0 }",
        "type A { b: array<B, 2> }\ntype B { a: A }\nfn main() -> i32 { 0 }",
    ] {
        let message = f.error(source, "TE026");
        assert!(message.contains("recursive struct"), "{message}");
    }
}

#[test]
fn field_level_primitive_references_stay_gated_like_array_elements() {
    let f = Fixture::new();
    for statement in [
        "let r := l.a.x.share();",
        "let r := l.a.x.borrow();",
        "let r := a[0].x.share();",
    ] {
        let message = f.error(
            &format!(
                "{TYPES}fn main() -> i32 {{\n\
                 var l := Line {{ a: P {{ x: 1, y: 2 }}, b: P {{ x: 3, y: 4 }} }};\n\
                 var a := [P {{ x: 0, y: 0 }}; 2];\n\
                 {statement}\n\
                 0\n}}"
            ),
            "TE017",
        );
        assert!(
            message.contains("references to primitive elements"),
            "{message}"
        );
    }
}

#[test]
fn nested_aggregates_in_exported_signatures_are_le900() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='nesting'\nentry='app::main'\n[export]\nf='app::f'\ng='app::g'\n",
    );
    f.write(
        "src/app.mb",
        "pub type P { pub x: i32 }\npub type L { pub a: P, pub xs: array<P, 2> }\n\
         pub fn f(l: L) -> i32 { 0 }\npub fn g() -> L { L { a: P { x: 1 }, xs: [P { x: 2 }; 2] } }\n\
         fn main() -> i32 { 0 }",
    );
    let output = f.run(&["build", "--lib"]);
    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stderr).contains("LE900"));
}

#[test]
fn oversized_nested_frames_use_the_configured_stack_diagnostic() {
    let f = Fixture::new();
    let message = f.error(
        "type P { x: i32 }\ntype Big { a: array<P, 400000> }\n\
         fn main() -> i32 { let b := Big { a: [P { x: 1 }; 400000] }; b.a[0].x }",
        "LE900",
    );
    assert!(message.contains("configured stack size"), "{message}");
    assert!(message.contains("[build].stack_size"), "{message}");
}
