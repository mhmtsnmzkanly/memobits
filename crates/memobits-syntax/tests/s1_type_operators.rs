//! Built-in type spelling: `bool`, `char`, `array<T, N>` and the `T ! E` /
//! `T?` / `T ?! E` type operators.
use memobits_diagnostics::SourceId;
use memobits_syntax::{parse, ItemKind, Type, TypeArgument};

fn render(ty: &Type) -> String {
    let name = ty.path.join("::");
    if ty.arguments.is_empty() {
        return name;
    }
    let args: Vec<String> = ty
        .arguments
        .iter()
        .map(|a| match a {
            TypeArgument::Type(t) => render(t),
            TypeArgument::Integer(i) => i.raw.clone(),
            TypeArgument::Reference {
                access, referent, ..
            } => format!("{access:?} {}", render(referent)),
            TypeArgument::TupleField { ty, .. } => render(ty),
            other => format!("{other:?}"),
        })
        .collect();
    format!("{name}<{}>", args.join(", "))
}

fn result_type(source: &str) -> String {
    let parsed = parse(SourceId(0), source);
    assert!(
        parsed.diagnostics.is_empty(),
        "{source}: {:?}",
        parsed.diagnostics
    );
    let ItemKind::Function { result, .. } = &parsed.module.items[0].kind else {
        panic!("expected function");
    };
    render(result.as_ref().expect("result type"))
}

fn same(left: &str, right: &str) {
    let a = result_type(&format!("fn f() -> {left} {{ x }}"));
    let b = result_type(&format!("fn f() -> {right} {{ x }}"));
    assert_eq!(a, b, "{left} vs {right}");
}

fn shape(source: &str, expected: &str) {
    assert_eq!(
        result_type(&format!("fn f() -> {source} {{ x }}")),
        expected
    );
}

#[test]
fn builtin_spellings_are_lowercase() {
    shape("bool", "bool");
    shape("char", "char");
    shape("array<u8, 4>", "array<u8, 4>");
    shape("array<array<i32, 2>, 3>", "array<array<i32, 2>, 3>");
}

#[test]
fn operators_parse_onto_the_template_shapes() {
    shape("i32 ! Error", "!<i32, Error>");
    shape("u32?", "?<u32>");
    shape("u32? ! Error", "!<?<u32>, Error>");
    shape("(u32 ! Error)?", "?<!<u32, Error>>");
    shape("(borrow Text)?", "?<Borrow Text>");
    shape("i32 ! (borrow Error)", "!<i32, Borrow Error>");
}

#[test]
fn old_spellings_parse_as_ordinary_names_and_fail_later() {
    shape("Option<u32>", "Option<u32>");
    shape("Result<u32, Error>", "Result<u32, Error>");
    shape("Attempt<u32, Error>", "Attempt<u32, Error>");
    shape("bool", "bool");
}

#[test]
fn question_bang_is_question_then_bang() {
    for spelling in [
        "u32?! Error",
        "u32 ?! Error",
        "u32? ! Error",
        "u32 ? ! Error",
    ] {
        shape(spelling, "!<?<u32>, Error>");
    }
    same("u32 ?! Error", "(u32?) ! Error");
    shape("(u32 ! Error) ?! Error", "!<?<!<u32, Error>>, Error>");
    shape("u32?? ?! Error", "!<?<?<?<u32>>>, Error>");
    shape("(borrow Text) ?! Error", "!<?<Borrow Text>, Error>");
    shape("array<u32 ?! Error, 2>", "array<!<?<u32>, Error>, 2>");
    shape("(u32 ?! Error, bool)", "\0tuple<!<?<u32>, Error>, bool>");
}

#[test]
fn bang_nests_in_type_arguments_and_elements() {
    shape("array<i32 ! Error, 2>", "array<!<i32, Error>, 2>");
    shape("(i32 ! Error, bool)", "\0tuple<!<i32, Error>, bool>");
    shape("List<u8? ! Error>", "List<!<?<u8>, Error>>");
}

#[test]
fn expression_not_and_not_equal_are_unaffected() {
    let source = "fn f(a: bool, b: i32 ! Error) -> bool {
        let c: bool = !a;
        let d := 3 as i64 != 4 as i64;
        let e := a as bool;
        !c && d != e
    }";
    let parsed = parse(SourceId(0), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
}
