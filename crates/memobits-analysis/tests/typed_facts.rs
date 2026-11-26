use std::collections::HashSet;

use memobits_analysis::{check_typed_module, PathTarget};
use memobits_diagnostics::SourceId;
use memobits_ir::{Access, FunctionId, LocalId, Primitive, Type};
use memobits_syntax::parse;

fn typed(source: &str) -> memobits_analysis::TypedModule {
    let parsed = parse(SourceId(12), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    check_typed_module(&parsed.module).unwrap()
}

#[test]
fn records_shadowed_locals_and_expression_types_once() {
    let source = "fn f(x: i64) -> i64 { let x := x + 1; x }";
    let result = typed(source);
    let function = &result.functions[0];
    assert_eq!(function.id, FunctionId(0));
    assert_eq!(function.locals.len(), 2);
    assert_eq!(function.locals[0].id, LocalId(0));
    assert_eq!(function.locals[1].id, LocalId(1));
    assert_eq!(function.locals[0].ty, Type::Primitive(Primitive::I64));
    assert_eq!(function.locals[1].ty, Type::Primitive(Primitive::I64));
    assert_eq!(function.signature.parameters[0].access, Access::Owned);
    assert_eq!(function.locals[0].access, Access::Owned);
    assert_eq!(function.locals[1].access, Access::Owned);
    let uses: Vec<_> = function.path_uses.iter().map(|u| u.target).collect();
    assert_eq!(
        uses,
        [PathTarget::Local(LocalId(0)), PathTarget::Local(LocalId(1))]
    );
    assert!(function
        .path_uses
        .iter()
        .all(|use_| use_.access == Some(Access::Owned)));
    let ids: HashSet<_> = function.expressions.iter().map(|f| f.id).collect();
    assert_eq!(ids.len(), function.expressions.len());
    let literal = function
        .expressions
        .iter()
        .find(|fact| &source[fact.span.start..fact.span.end] == "1")
        .unwrap();
    assert_eq!(literal.ty, Some(Type::Primitive(Primitive::I64)));
}

#[test]
fn reference_parameters_and_computations_keep_handle_facts() {
    for access in ["borrow", "share"] {
        let source = format!("fn read(value: {access} i64) -> i64 {{ value + 1 }}");
        let result = typed(&source);
        let function = &result.functions[0];
        assert!(matches!(function.locals[0].ty, Type::Reference { .. }));
        let path = function
            .expressions
            .iter()
            .find(|fact| &source[fact.span.start..fact.span.end] == "value")
            .unwrap();
        assert!(matches!(path.ty, Some(Type::Reference { .. })));
        let sum = function
            .expressions
            .iter()
            .find(|fact| &source[fact.span.start..fact.span.end] == "value + 1")
            .unwrap();
        assert_eq!(sum.ty, Some(Type::Primitive(Primitive::I64)));
    }
}

#[test]
fn rebinding_mutability_is_retained_separately_from_access() {
    let result = typed("fn update(var value: i32) -> i32 { value = 2; value }");
    let local = &result.functions[0].locals[0];
    assert!(local.mutable);
    assert_eq!(local.access, Access::Owned);
    assert_eq!(
        result.functions[0].signature.parameters[0].access,
        Access::Owned
    );
}

#[test]
fn function_references_use_function_ids_and_local_ids_restart() {
    let result = typed("fn id(x: i32) -> i32 { x } fn main() -> i32 { let y := id(1); y }");
    assert_eq!(result.functions.len(), 2);
    assert_eq!(result.functions[1].id, FunctionId(1));
    assert_eq!(result.functions[1].locals[0].id, LocalId(0));
    assert!(result.functions[1]
        .path_uses
        .iter()
        .any(|use_| use_.target == PathTarget::Function(FunctionId(0))));
}

#[test]
fn no_typed_facts_escape_on_diagnostics() {
    for source in ["fn f() -> i32 { true }", "fn f() -> i32 { break; 1 }"] {
        let parsed = parse(SourceId(12), source);
        assert!(parsed.diagnostics.is_empty());
        assert!(check_typed_module(&parsed.module).is_err());
    }
}
