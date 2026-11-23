use memobits_diagnostics::SourceId;
use memobits_syntax::{parse, ItemKind};

#[test]
fn parses_external_function_declaration_and_calls() {
    let parsed = parse(
        SourceId(0),
        "extern fn write_i32(value: i32); fn main() -> i32 { write_i32(42); 7 }",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function {
        external: true,
        name,
        parameters,
        body,
        ..
    } = &parsed.module.items[0].kind
    else {
        panic!("expected external function declaration");
    };
    assert_eq!(name, "write_i32");
    assert_eq!(parameters.len(), 1);
    assert!(body.statements.is_empty());
    assert!(body.tail.is_none());

    let ItemKind::Function {
        external: false,
        body,
        ..
    } = &parsed.module.items[1].kind
    else {
        panic!("expected function definition");
    };
    assert_eq!(body.statements.len(), 1);
}
