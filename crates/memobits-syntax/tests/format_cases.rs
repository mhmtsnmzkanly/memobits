//! Targeted formatter cases: each input is formatted, compared with the
//! expected canonical text, and checked for idempotence and for an unchanged
//! syntax tree (`format_source` itself verifies both before returning).
use memobits_diagnostics::SourceId;
use memobits_syntax::format::{format_source, same_syntax, FormatError};
use memobits_syntax::parse;

fn fmt(source: &str) -> String {
    let once = format_source(SourceId(0), source)
        .unwrap_or_else(|error| panic!("{error:?} for:\n{source}"));
    let twice = format_source(SourceId(0), &once).unwrap();
    assert_eq!(once, twice, "not idempotent");
    let (before, after) = (parse(SourceId(0), source), parse(SourceId(0), &once));
    assert!(
        same_syntax(&before.module, &after.module),
        "syntax tree changed"
    );
    once
}

#[test]
fn comments_between_tokens_stay_in_place() {
    let source = "fn /* name */ main /* after name */ ( ) /* before arrow */ -> /* ty */ i32 // end of header\n{\n    let x /* a */ := /* b */ 1 /* c */ + /* d */ 2; // tail\n    // dangling before close\n}\n";
    assert_eq!(
        fmt(source),
        "fn /* name */ main /* after name */() /* before arrow */ -> /* ty */ i32 { // end of header\n    let x /* a */ := /* b */ 1 /* c */ + /* d */ 2; // tail\n    // dangling before close\n}\n"
    );
}

#[test]
fn doc_style_and_nested_block_comments_survive() {
    let source = "/// Doc comment\n/* outer /* nested */ still outer */\nfn f() {}\n";
    assert_eq!(fmt(source), source);
}

#[test]
fn comment_only_and_empty_files() {
    assert_eq!(
        fmt("// only a comment\n\n\n// another"),
        "// only a comment\n\n// another\n"
    );
    assert_eq!(fmt(""), "");
    assert_eq!(fmt("\n\n  \n"), "");
}

#[test]
fn crlf_input_is_normalized() {
    assert_eq!(fmt("fn f() {\r\n    1\r\n}\r\n"), "fn f() {\n    1\n}\n");
}

#[test]
fn comments_in_lists_keep_their_lines() {
    let source = "fn f() {\n    let items := [\n        1, // one\n        2,\n        // three comes last\n        3,\n    ];\n    let point := Point { x: 1, // x axis\n        y: 2 };\n    foo(a, b, /* inline */ c);\n}\n";
    assert_eq!(
        fmt(source),
        "fn f() {\n    let items := [\n        1, // one\n        2,\n        // three comes last\n        3,\n    ];\n    let point := Point {\n        x: 1, // x axis\n        y: 2,\n    };\n    foo(a, b, /* inline */ c);\n}\n"
    );
}

#[test]
fn long_calls_break_one_argument_per_line_with_a_trailing_comma() {
    let source = "fn f() -> i32 {\n    let total := combine(first_value_long_name, second_value_long_name, third_value_long_name, 4, 5);\n    total\n}\n";
    assert_eq!(
        fmt(source),
        "fn f() -> i32 {\n    let total := combine(\n        first_value_long_name,\n        second_value_long_name,\n        third_value_long_name,\n        4,\n        5,\n    );\n    total\n}\n"
    );
}

#[test]
fn long_parameter_lists_and_conditions_break() {
    let source = "fn many(first_parameter_name: i32, second_parameter_name: i32, third_parameter_name: i32, fourth: i32) -> i32 {\n    if first_condition_is_long(a) && second_condition_is_long(b) && third_condition_is_long(c) && fourth(d) { 1 } else { 0 }\n}\n";
    let formatted = fmt(source);
    assert_eq!(
        formatted,
        "fn many(\n    first_parameter_name: i32,\n    second_parameter_name: i32,\n    third_parameter_name: i32,\n    fourth: i32,\n) -> i32 {\n    if first_condition_is_long(a)\n        && second_condition_is_long(b)\n        && third_condition_is_long(c)\n        && fourth(d) {\n        1\n    } else {\n        0\n    }\n}\n"
    );
    assert!(formatted.lines().all(|line| line.chars().count() <= 100));
}

#[test]
fn match_arms_guards_alternatives_and_block_bodies() {
    let source = "fn arms(x: i32?) -> i32 { match x { Some(n) if n > 0 && n < 10 => n, Some(-1) | Some(0) => 0, Some(_) => { 1 } None => 2 } }\n";
    assert_eq!(
        fmt(source),
        "fn arms(x: i32?) -> i32 {\n    match x {\n        Some(n) if n > 0 && n < 10 => n,\n        Some(-1) | Some(0) => 0,\n        Some(_) => { 1 }\n        None => 2,\n    }\n}\n"
    );
    // A short match written on one line stays on one line.
    assert_eq!(
        fmt("fn f(x: i32?) -> i32 { match x { Some(n) => n, None => 0 } }\n"),
        "fn f(x: i32?) -> i32 { match x { Some(n) => n, None => 0 } }\n"
    );
    // A match written over several lines keeps one arm per line, a trailing
    // comma after expression arms, and none after block arms.
    let spread = "fn arms(x: i32?) -> i32 {\n    match x {\n        Some(n) if n > 0 => n,\n        Some(_) => {\n            1\n        },\n        None => 2\n    }\n}\n";
    assert_eq!(
        fmt(spread),
        "fn arms(x: i32?) -> i32 {\n    match x {\n        Some(n) if n > 0 => n,\n        Some(_) => {\n            1\n        }\n        None => 2,\n    }\n}\n"
    );
}

#[test]
fn nested_closures_and_function_types() {
    let source = "fn closures() { let f := fn(a: i32) -> fn(i32) -> i32 { fn(b: i32) -> i32 => a + b }; let g := fn(x) => fn(y) => fn(z) => x + y + z; let h: var fn(borrow string, share u32) -> i32 ! E = k; apply(fn(v) { v + 1 }, 2) }\n";
    assert_eq!(
        fmt(source),
        "fn closures() {\n    let f := fn(a: i32) -> fn(i32) -> i32 { fn(b: i32) -> i32 => a + b };\n    let g := fn(x) => fn(y) => fn(z) => x + y + z;\n    let h: var fn(borrow string, share u32) -> i32 ! E = k;\n    apply(fn(v) { v + 1 }, 2)\n}\n"
    );
}

#[test]
fn closure_with_a_long_body_hugs_its_call() {
    let source = "fn f() {\n    apply(fn(value: i32) -> i32 {\n        let doubled := value * 2;\n        doubled + 1\n    }, 3);\n}\n";
    assert_eq!(
        fmt(source),
        "fn f() {\n    apply(fn(value: i32) -> i32 {\n        let doubled := value * 2;\n        doubled + 1\n    }, 3);\n}\n"
    );
}

#[test]
fn string_literals_and_interpolation_are_byte_for_byte() {
    let source = "fn f() { let a := \"{{literal}} {name}  é  \"; let b := \"{x}{y}\"; let c := ' '; let d := '\\n'; }\n";
    let formatted = fmt(source);
    for literal in ["\"{{literal}} {name}  é  \"", "\"{x}{y}\"", "' '", "'\\n'"] {
        assert!(formatted.contains(literal), "{literal} in {formatted}");
    }
}

#[test]
fn numeric_literals_keep_their_spelling() {
    let source = "fn f() { let a := 0xFF_FF; let b := 0b1010; let c := 0o777; let d := 1_000.5e-3; let e := 0XAB; let g := 1_0; }\n";
    let formatted = fmt(source);
    for literal in ["0xFF_FF", "0b1010", "0o777", "1_000.5e-3", "0XAB", "1_0"] {
        assert!(formatted.contains(literal), "{literal} in {formatted}");
    }
}

#[test]
fn user_parentheses_are_neither_added_nor_removed() {
    let source = "fn f() { let a := (1 + 2) * 3; let b := -(a); let c := !(a == b); let d := ((a)); let e := (a as i64) << 3 >> 1; let g := a + b * c; let h := (a + b) + c; }\n";
    assert_eq!(
        fmt(source),
        "fn f() {\n    let a := (1 + 2) * 3;\n    let b := -(a);\n    let c := !(a == b);\n    let d := ((a));\n    let e := (a as i64) << 3 >> 1;\n    let g := a + b * c;\n    let h := (a + b) + c;\n}\n"
    );
}

#[test]
fn empty_bodies_stay_empty() {
    let source = "fn empty() {}\ntype Empty {}\nextend Empty {}\ninterface Nothing {}\nfn blocks() { {} loop {} if a {} else {} match x {} }\n";
    assert_eq!(
        fmt(source),
        "fn empty() {}\ntype Empty {}\nextend Empty {}\ninterface Nothing {}\nfn blocks() { {} loop {} if a {} else {} match x {} }\n"
    );
}

#[test]
fn trailing_commas_follow_the_layout() {
    // Flat lists drop a trailing comma; broken lists gain one.
    assert_eq!(
        fmt("fn f(a: i32,) { g(a, b,); }\n"),
        "fn f(a: i32) { g(a, b); }\n"
    );
    // A one-element tuple keeps its comma; a grouping never gains one.
    assert_eq!(
        fmt("fn t() -> (i32,) { let a := (1,); let b := (1); let c := ((1, 2),); (a.0,) }\n"),
        "fn t() -> (i32,) { let a := (1,); let b := (1); let c := ((1, 2),); (a.0,) }\n"
    );
    // An index and a repeat array never take a comma, however they break.
    assert_eq!(
        fmt("fn f() { let a := [0; 8]; let b := values[\n index\n]; }\n"),
        "fn f() {\n    let a := [0; 8];\n    let b := values[index];\n}\n"
    );
}

#[test]
fn items_use_forms_and_extensions() {
    let source = "use a::b::{c, d as e};\npub use x::y;\nconst LIMIT: u32 = 0xFF;\npub type Point<T> where T: Copy { pub x: T, y:T } extend {\n    pub fn norm(borrow self, scale: T) -> Point<T> { Point { x: self.x, y: self.y } }\n    fn sum(borrow self) -> T => self.x + self.y;\n}\ntype Alias = array<i32, 4>;\ntype Opaque;\ntype Choice [ A, B(i32, (string, u32)), C ] extend { fn id(self) -> i32 => 1; }\ninterface Shape { type Item; fn area(borrow self) -> u32; }\nextend Foo of Shape { type Item = i32; fn area(borrow self) -> u32 { 1 } }\nextern fn write_i32(value: i32);\ntest fn t() { assert(1 == 1); }\nfn gen<T, const N: u32>(a: array<T, N>) -> T? ! Err where T: A + B { a[0] }\n";
    let formatted = fmt(source);
    assert!(formatted.contains("use a::b::{c, d as e};\npub use x::y;\nconst LIMIT: u32 = 0xFF;\n\npub type Point<T> where T: Copy"));
    assert!(formatted.contains("type Choice [A, B(i32, (string, u32)), C] extend {"));
    assert!(formatted
        .contains("extend Foo of Shape { type Item = i32; fn area(borrow self) -> u32 { 1 } }"));
    assert!(formatted
        .contains("fn gen<T, const N: u32>(a: array<T, N>) -> T? ! Err where T: A + B { a[0] }"));
    assert!(formatted.contains("extern fn write_i32(value: i32);\ntest fn t() { assert(1 == 1); }"));
}

#[test]
fn a_where_clause_on_its_own_line_stays_there() {
    let source = "fn gen<T>(a: T) -> T\n    where T: A + B {\n    a\n}\n";
    assert_eq!(fmt(source), source);
}

#[test]
fn optional_and_fallible_type_spellings() {
    let source =
        "type A = i32? ?! E;\ntype B = u32!E;\ntype C = i32?!E;\ntype D = Result<i32?, E>;\n";
    let formatted = fmt(source);
    assert!(formatted.contains("type A = i32? ?! E;"));
    assert!(formatted.contains("type B = u32 ! E;"));
    assert!(formatted.contains("type C = i32?! E;"));
}

#[test]
fn blank_lines_are_collapsed_and_kept() {
    let source = "fn f() {\n\n\n    let a := 1;\n\n\n\n    let b := 2;\n    let c := 3;\n\n}\n\n\n\nfn g() {}\n";
    assert_eq!(
        fmt(source),
        "fn f() {\n    let a := 1;\n\n    let b := 2;\n    let c := 3;\n}\n\nfn g() {}\n"
    );
}

#[test]
fn consecutive_one_line_items_stay_together_others_get_a_blank_line() {
    let source = "use a::b;\nuse a::c;\nfn one() -> i32 { 1 }\nfn two() -> i32 { 2 }\nfn big() {\n    let x := 1;\n}\nfn after() {}\n";
    assert_eq!(
        fmt(source),
        "use a::b;\nuse a::c;\nfn one() -> i32 { 1 }\nfn two() -> i32 { 2 }\n\nfn big() {\n    let x := 1;\n}\n\nfn after() {}\n"
    );
}

#[test]
fn generic_comparisons_and_shifts_are_not_confused() {
    let source = "fn f<T>(a: array<T, 3>, b: i32) -> bool { let c := b < 3 && b > 1; let d := b << 2 >> 1; let e := Pair<i32, i32> { first: 1, second: 2 }; c }\n";
    assert_eq!(
        fmt(source),
        "fn f<T>(a: array<T, 3>, b: i32) -> bool {\n    let c := b < 3 && b > 1;\n    let d := b << 2 >> 1;\n    let e := Pair<i32, i32> { first: 1, second: 2 };\n    c\n}\n"
    );
}

#[test]
fn syntax_errors_are_reported_not_formatted() {
    match format_source(SourceId(0), "fn main( {") {
        Err(FormatError::Syntax(diagnostics)) => assert!(!diagnostics.is_empty()),
        other => panic!("{other:?}"),
    }
}

#[test]
fn same_syntax_ignores_positions_but_not_content() {
    let a = parse(SourceId(0), "fn f() -> i32 { 1 + 2 }");
    let b = parse(SourceId(0), "fn   f ( ) -> i32 {\n  1 +\n 2 }");
    let c = parse(SourceId(0), "fn f() -> i32 { 1 + 3 }");
    let d = parse(SourceId(0), "fn f() -> i32 { 0x1 + 2 }");
    let e = parse(SourceId(0), "fn f() -> i32 { (1) + 2 }");
    assert!(same_syntax(&a.module, &b.module));
    assert!(!same_syntax(&a.module, &c.module));
    assert!(
        !same_syntax(&a.module, &d.module),
        "literal spelling is part of the tree"
    );
    // The tree has no parenthesis node, so a redundant pair compares equal;
    // the formatter keeps user parentheses anyway (see the test above).
    assert!(same_syntax(&a.module, &e.module));
}
