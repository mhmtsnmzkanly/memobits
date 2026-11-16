//! Move and loan rules for arrays across calls, checked from source form.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_syntax::parse;

fn ownership_codes(source: &str) -> Vec<String> {
    let parsed = parse(SourceId(33), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let program = lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"));
    memobits_ownership::check_ownership(&program)
        .iter()
        .map(|diagnostic| diagnostic.code.to_string())
        .collect()
}
fn accepted(source: &str) {
    let codes = ownership_codes(source);
    assert!(codes.is_empty(), "{source}: {codes:?}");
}
fn rejected(source: &str, code: &str) {
    let codes = ownership_codes(source);
    assert!(codes.iter().any(|c| c == code), "{source}: {codes:?}");
}

const DECLARATIONS: &str = "fn read(a: borrow Array<i32, 3>) -> i32 { a[0] + 0 } \
    fn write(a: share Array<i32, 3>) { a[0] = 1; } \
    fn two(a: share Array<i32, 3>, b: share Array<i32, 3>) {} \
    fn mixed(a: share Array<i32, 3>, b: borrow Array<i32, 3>) {} \
    fn both(a: borrow Array<i32, 3>, b: borrow Array<i32, 3>) -> i32 { a[0] + b[1] } \
    fn own(a: Array<i32, 3>) -> i32 { a[0] + 0 } ";

fn main_body(body: &str) -> String {
    format!("{DECLARATIONS}fn main() {{ {body} }}")
}

#[test]
fn owned_array_arguments_move_the_source() {
    accepted(&main_body("let a := [1, 2, 3]; own(a);"));
    rejected(&main_body("let a := [1, 2, 3]; own(a); a[0] + 0;"), "BE001");
    rejected(&main_body("let a := [1, 2, 3]; own(a); own(a);"), "BE001");
    rejected(
        &main_body("let a := [1, 2, 3]; own(a); read(a.borrow());"),
        "BE001",
    );
    // Reassigning a moved `var` array makes it available again.
    accepted(&main_body(
        "var a := [1, 2, 3]; own(a); a = [4, 5, 6]; own(a);",
    ));
    // Argument order: the move happens when the argument is evaluated.
    rejected(
        "fn f(a: Array<i32, 2>, n: i32) {} fn main() { var a := [1, 2]; f(a, { a[0] = 5; 1 }); }",
        "BE001",
    );
}

#[test]
fn borrows_of_one_array_may_overlap_and_repeat() {
    accepted(&main_body(
        "let a := [1, 2, 3]; read(a.borrow()); read(a.borrow());",
    ));
    accepted(&main_body(
        "let a := [1, 2, 3]; both(a.borrow(), a.borrow());",
    ));
    accepted(&main_body(
        "var a := [1, 2, 3]; let r := a.borrow(); let q := a.borrow(); r[0] + q[1]; a[2] = 9;",
    ));
}

#[test]
fn two_share_arguments_of_the_same_array_conflict() {
    rejected(
        &main_body("var a := [1, 2, 3]; two(a.share(), a.share());"),
        "BE005",
    );
    rejected(
        &main_body("var a := [1, 2, 3]; mixed(a.share(), a.borrow());"),
        "BE005",
    );
    rejected(
        "fn mixed(a: borrow Array<i32, 3>, b: share Array<i32, 3>) {} fn main() { var a := [1, 2, 3]; mixed(a.borrow(), a.share()); }",
        "BE005",
    );
    accepted(&main_body(
        "var a := [1, 2, 3]; var b := [4, 5, 6]; two(a.share(), b.share());",
    ));
    rejected(
        &main_body("var a := [1, 2, 3]; var r := a.share(); two(r, r);"),
        "BE005",
    );
}

#[test]
fn element_access_overlaps_the_whole_array_while_a_reference_is_live() {
    // A write to any element conflicts with a live borrow or share.
    rejected(
        &main_body("var a := [1, 2, 3]; let r := a.borrow(); a[2] = 9; r[0] + 0;"),
        "BE005",
    );
    rejected(
        &main_body("var a := [1, 2, 3]; var r := a.share(); a[2] = 9; r[0] + 0;"),
        "BE005",
    );
    rejected(
        &main_body("var a := [1, 2, 3]; var r := a.share(); a[2] + 0; r[0] = 1;"),
        "BE005",
    );
    rejected(
        &main_body("var a := [1, 2, 3]; let r := a.borrow(); own(a); r[0] + 0;"),
        "BE005",
    );
    rejected(
        &main_body("var a := [1, 2, 3]; let r := a.borrow(); a[0] += 1; r[1] + 0;"),
        "BE005",
    );
    // Reading while only borrowed is fine; writing after the last use is fine.
    accepted(&main_body(
        "var a := [1, 2, 3]; let r := a.borrow(); a[0] + r[1]; a[2] = 9;",
    ));
    accepted(&main_body(
        "var a := [1, 2, 3]; var r := a.share(); r[0] = 4; a[1] = 5; a[2] + 0;",
    ));
    // A share argument is live for the whole call, including its other arguments.
    rejected(
        "fn f(a: share Array<i32, 2>, n: i32) {} fn main() { var a := [1, 2]; f(a.share(), { a[0] = 1; 2 }); }",
        "BE005",
    );
}

#[test]
fn reborrowing_a_reference_parameter_keeps_loans_and_availability() {
    accepted(
        "fn r(a: borrow Array<i32, 2>) -> i32 { a[0] + 0 } \
         fn w(a: share Array<i32, 2>) { a[0] = 1; } \
         fn f(a: borrow Array<i32, 2>) -> i32 { r(a) + r(a) } \
         fn g(a: share Array<i32, 2>) { w(a); w(a); a[1] = 3; r(a.borrow()); }",
    );
    rejected(
        "fn w(a: share Array<i32, 2>, b: share Array<i32, 2>) {} \
         fn f(a: share Array<i32, 2>) { w(a, a); }",
        "BE005",
    );
    // Moving a reference binding away makes the original unavailable.
    rejected(
        "fn f(a: borrow Array<i32, 2>) { let b := a; a[0] + b[0]; }",
        "BE001",
    );
}

#[test]
fn share_through_a_local_binding_requires_a_mutable_owner() {
    accepted(&main_body(
        "var a := [1, 2, 3]; var r := a.share(); r[0] = 1; r[1] += 2;",
    ));
    let parsed = parse(
        SourceId(33),
        "fn main() { let a := [1, 2]; var r := a.share(); }",
    );
    assert!(lower_module(&parsed.module, "test", &["main".into()]).is_err());
}
