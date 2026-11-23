use memobits_diagnostics::SourceId;
use memobits_syntax::{parse, ExprKind, ItemKind, StatementKind, TypeDefinition};

#[test]
fn anonymous_record_and_enum_types_and_record_values_parse_without_reclassifying_blocks() {
    let parsed = parse(
        SourceId(93),
        r#"
        type Shape = { right: u32, left: i32 };
        type Phase = enum [Ready, Waiting];
        type Payload = enum [Number(i32), Pair(i32, Bool), Empty];
        fn make() -> Phase {
            let record := { right: 2, left: 40 };
            let empty := {};
            Ready
        }
        "#,
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Type {
        definition: TypeDefinition::Alias(record_type),
        ..
    } = &parsed.module.items[0].kind
    else {
        panic!("expected inline record alias")
    };
    assert_eq!(record_type.path, ["\0record"]);
    let ItemKind::Type {
        definition: TypeDefinition::Alias(enum_type),
        ..
    } = &parsed.module.items[1].kind
    else {
        panic!("expected inline enum alias")
    };
    assert_eq!(enum_type.path, ["\0enum", "Ready", "Waiting"]);
    let ItemKind::Type {
        definition: TypeDefinition::Alias(payload_type),
        ..
    } = &parsed.module.items[2].kind
    else {
        panic!("expected inline payload enum alias")
    };
    assert_eq!(payload_type.path, ["\0enum", "Number", "Pair", "Empty"]);
    assert_eq!(payload_type.arguments.len(), 2);
    let memobits_syntax::TypeArgument::TupleField {
        label: Some(number),
        ty: number_payload,
    } = &payload_type.arguments[0]
    else {
        panic!("expected payload metadata for Number")
    };
    assert_eq!(number, "Number");
    assert_eq!(number_payload.path, ["\0tuple"]);
    assert_eq!(number_payload.arguments.len(), 1);
    let memobits_syntax::TypeArgument::TupleField {
        label: Some(pair),
        ty: pair_payload,
    } = &payload_type.arguments[1]
    else {
        panic!("expected payload metadata for Pair")
    };
    assert_eq!(pair, "Pair");
    assert_eq!(pair_payload.arguments.len(), 2);

    let ItemKind::Function { body, .. } = &parsed.module.items[3].kind else {
        panic!("expected function")
    };
    let StatementKind::Binding { value, .. } = &body.statements[0].kind else {
        panic!("expected record binding")
    };
    assert!(matches!(&value.kind, ExprKind::Struct { path, .. } if path.is_empty()));
    let StatementKind::Binding { value, .. } = &body.statements[1].kind else {
        panic!("expected empty block binding")
    };
    assert!(matches!(value.kind, ExprKind::Block(_)));
}

#[test]
fn field_shaped_braces_are_rejected_in_condition_positions_without_parentheses() {
    let parsed = parse(SourceId(94), "fn main() { if { value: 1 } { } }");
    assert_eq!(parsed.diagnostics.len(), 1, "{:?}", parsed.diagnostics);
    assert!(parsed.diagnostics[0]
        .message
        .contains("wrap it in parentheses"));
}
