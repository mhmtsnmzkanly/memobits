//! H1 grammar: function types, anonymous functions and `=>` bodies.
use memobits_diagnostics::SourceId;
use memobits_syntax::{parse, Access, ExprKind, ItemKind, StatementKind, TypeArgument};

fn first_function(source: &str) -> (ItemKind, Vec<String>) {
    let parsed = parse(SourceId(0), source);
    let messages = parsed
        .diagnostics
        .iter()
        .map(|d| d.message.clone())
        .collect();
    let item = parsed
        .module
        .items
        .into_iter()
        .find(|item| matches!(item.kind, ItemKind::Function { .. }))
        .expect("a function");
    (item.kind, messages)
}

#[test]
fn function_types_carry_access_modes_and_a_final_result() {
    let (kind, messages) = first_function(
        "fn f(a: fn(i32, borrow string) -> bool, b: fn(share u32), c: (fn() -> i32)?) {}",
    );
    assert!(messages.is_empty(), "{messages:?}");
    let ItemKind::Function { parameters, .. } = kind else {
        unreachable!()
    };
    let a = &parameters[0].ty;
    assert_eq!(a.path, ["\0fn"]);
    assert!(matches!(a.arguments[0], TypeArgument::Type(_)));
    assert!(matches!(
        a.arguments[1],
        TypeArgument::Reference {
            access: Access::Borrow,
            ..
        }
    ));
    assert!(matches!(&a.arguments[2], TypeArgument::Type(result) if result.path == ["bool"]));
    // An omitted result is the Unit marker, last.
    let b = &parameters[1].ty;
    assert_eq!(b.arguments.len(), 2);
    assert!(matches!(&b.arguments[1], TypeArgument::Type(result) if result.path == ["\0unit"]));
    assert_eq!(parameters[2].ty.path, ["?"]);
}

#[test]
fn anonymous_functions_parse_in_expression_position() {
    let (kind, messages) = first_function(
        "fn main() { let a := fn(x: i32) -> i32 => x * 2; let b := fn(x) { x }; \
         let c := fn() => 1; apply(fn(var n: i32) -> i32 { n }, 1); }",
    );
    assert!(messages.is_empty(), "{messages:?}");
    let ItemKind::Function { body, .. } = kind else {
        unreachable!()
    };
    let function = |index: usize| {
        let StatementKind::Binding { value, .. } = &body.statements[index].kind else {
            panic!("expected a binding")
        };
        let ExprKind::Function(function) = &value.kind else {
            panic!("expected an anonymous function")
        };
        function.clone()
    };
    let a = function(0);
    assert!(a.expression && a.result.is_some());
    assert_eq!(a.parameters[0].name, "x");
    assert!(a.parameters[0].ty.is_some());
    assert!(a.body.tail.is_some() && a.body.statements.is_empty());
    let b = function(1);
    assert!(!b.expression && b.result.is_none());
    assert!(b.parameters[0].ty.is_none());
    let c = function(2);
    assert!(c.parameters.is_empty());
}

#[test]
fn expression_bodies_on_functions_and_methods() {
    let parsed = parse(
        SourceId(0),
        "fn double(x: i32) -> i32 => x * 2\nfn triple(x: i32) -> i32 => x * 3;\n\
         test fn t() => assert(true)\ntype P { v: i32 } extend P { fn get(borrow self) -> i32 => self.v }",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let functions = parsed
        .module
        .items
        .iter()
        .filter_map(|item| match &item.kind {
            ItemKind::Function { name, body, .. } => Some((name.as_str(), body)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(functions.len(), 3);
    for (_, body) in &functions {
        assert!(body.tail.is_some() && body.statements.is_empty());
    }
    let methods = parsed
        .module
        .items
        .iter()
        .find_map(|item| match &item.kind {
            ItemKind::InherentExtension { methods, .. } => Some(methods),
            _ => None,
        })
        .expect("an inherent extension");
    assert!(methods[0].body.as_ref().unwrap().tail.is_some());
}

#[test]
fn malformed_anonymous_functions_are_rejected() {
    for source in [
        "fn main() { let f := fn(x: i32) x; }",
        "fn main() { let f := fn(: i32) => 1; }",
        "fn main() { let f := fn(x: i32) -> => 1; }",
    ] {
        let parsed = parse(SourceId(0), source);
        assert!(!parsed.diagnostics.is_empty(), "accepted: {source}");
    }
}
