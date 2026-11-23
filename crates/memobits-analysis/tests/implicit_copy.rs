//! Implicit primitive copy: primitives never move, aggregates still do, and an
//! implicit copy is an ordinary read for loan checking.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_syntax::parse;

fn pipeline(source: &str) -> Vec<String> {
    let parsed = parse(SourceId(51), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let program = lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"));
    program.validate().unwrap();
    memobits_ownership::check_ownership(&program)
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

fn accepted(source: &str) {
    let found = pipeline(source);
    assert!(found.is_empty(), "{source}: {found:?}");
}

fn rejected(source: &str, code: &str) {
    let found = pipeline(source);
    assert!(found.contains(&code.to_string()), "{source}: {found:?}");
}

#[test]
fn primitive_uses_never_move() {
    for source in [
        "fn main() -> i32 { let x := 1; let y := x; x + y }",
        "fn f(n: i32) {} fn main() { var i := 0; loop { if i >= 3 { break; } f(i); i += 1; } }",
        "fn mk(v: i32) -> array<i32, 3> { [v, v + 1, v + 2] } fn main() {}",
        "fn main() { let x := 2; let a := [x; 3]; let b := [x; 3]; }",
        "fn main() -> i32 { let x := 1.5; let y := x; let z := x; 0 }",
        "fn main() -> bool { let b := true; let c := b; b && c }",
        "fn main() -> i32 { var a := [1, 2, 3]; let t := a[0]; a[0] = a[2]; a[2] = t; a[0] }",
        "type P { x: i32, y: i32 } fn f(v: i32) -> i32 { v } \
         fn main() -> i32 { let p := P { x: 1, y: 2 }; f(p.x) + f(p.x) + p.y }",
        "fn get(r: borrow i32) -> i32 { r }",
        "fn get(r: share i32) -> i32 { let a: i32 = r; a }",
        "fn main() -> bool { let flags := [false, true]; let on := flags[1]; on }",
        "fn pick(c: bool) -> i32 { let a := [1, 2]; if c { a[0] } else { a[1] } }",
    ] {
        accepted(source);
    }
}

#[test]
fn implicit_copies_are_reads_that_respect_live_shares() {
    for source in [
        "fn main() -> i32 { var x := 1; var s := x.share(); let y := x; s += 1; y }",
        "fn f(n: i32) {} fn main() { var x := 1; var s := x.share(); f(x); s += 1; }",
        "fn main() -> i32 { var a := [1, 2]; var s := a.share(); let t := a[0]; s[1] = 3; t }",
    ] {
        rejected(source, "BE005");
    }
    // Once the share is dead the copy is fine.
    accepted("fn main() -> i32 { var x := 1; var s := x.share(); s += 1; let y := x; y }");
}

#[test]
fn aggregates_still_move() {
    for source in [
        "fn main() -> i32 { let a := [1, 2]; let b := a; a[0] }",
        "fn f(a: array<i32, 2>) {} fn main() { let a := [1, 2]; f(a); f(a); }",
        "fn main() { let x := [1, 2]; let a := [x; 3]; }",
        "fn main() { var x := [1]; loop { let y := x; } }",
    ] {
        rejected(source, "BE001");
    }
}
