use memobits_diagnostics::SourceId;
use memobits_syntax::{parse, ItemKind, TypeDefinition};

#[test]
fn derived_error_retains_qualified_base_and_source_span() {
    let source = "pub type ParseError: errors::Base { pub line: u32 }";
    let parsed = parse(SourceId(12), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Type {
        public,
        base: Some(base),
        definition,
        ..
    } = &parsed.module.items[0].kind
    else {
        panic!("expected derived type");
    };
    assert!(*public);
    assert_eq!(base.path, ["errors", "Base"]);
    assert_eq!(&source[base.span.start..base.span.end], "errors::Base");
    assert!(matches!(definition, TypeDefinition::Struct(fields) if fields.len() == 1));
}

#[test]
fn derivation_requires_fields_not_alias_or_enum_body() {
    for source in ["type E: Error = i32;", "type E: Error [ A, B ]"] {
        let parsed = parse(SourceId(12), source);
        assert!(!parsed.diagnostics.is_empty(), "{source}");
    }
}
