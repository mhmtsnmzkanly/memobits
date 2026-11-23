//! Built-in type spelling: `bool`, `char`, `array<T, N>` and the `T ! E` /
//! `T?` type operators parse onto the existing built-in type shapes.
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

fn same(new: &str, old: &str) {
    let a = result_type(&format!("fn f() -> {new} {{ x }}"));
    let b = result_type(&format!("fn f() -> {old} {{ x }}"));
    assert_eq!(a, b, "{new} vs {old}");
}

#[test]
fn lowercase_builtins_match_existing_types() {
    same("bool", "Bool");
    same("char", "Char");
    same("array<u8, 4>", "Array<u8, 4>");
    same("array<array<i32, 2>, 3>", "Array<Array<i32, 2>, 3>");
}

#[test]
fn bang_is_result_and_question_binds_tighter() {
    same("i32 ! Error", "Result<i32, Error>");
    same("u32? ! Error", "Result<Option<u32>, Error>");
    same("(u32 ! Error)?", "Option<Result<u32, Error>>");
    same("(borrow Text)?", "Option<borrow Text>");
    same("bool ! Error", "Result<Bool, Error>");
}

#[test]
fn bang_nests_in_type_arguments_and_elements() {
    same("Option<i32 ! Error>", "Option<Result<i32, Error>>");
    same(
        "Result<(i32 ! Error)?, Error>",
        "Result<Option<Result<i32, Error>>, Error>",
    );
    same("array<i32 ! Error, 2>", "Array<Result<i32, Error>, 2>");
    same("(i32 ! Error, bool)", "(Result<i32, Error>, Bool)");
    same("List<u8? ! Error>", "List<Result<Option<u8>, Error>>");
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
