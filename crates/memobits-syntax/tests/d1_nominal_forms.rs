use memobits_diagnostics::SourceId;
use memobits_syntax::{ItemKind, TypeDefinition, parse};

#[test]
fn nominal_body_forms_parse_with_and_without_trailing_extensions() {
    let cases = [
        ("type Token;", "Token", "bodyless"),
        ("type Empty {}", "Empty", "struct"),
        ("type Point { value: i32 }", "Point", "struct"),
        ("type State [Ready, Waiting]", "State", "enum"),
        (
            "type Token; extend { fn kind(borrow self) -> i32 { 1 } }",
            "Token",
            "bodyless",
        ),
        (
            "type Empty {} extend { fn kind(borrow self) -> i32 { 1 } }",
            "Empty",
            "struct",
        ),
        (
            "type Point { value: i32 } extend { fn kind(borrow self) -> i32 { self.value } }",
            "Point",
            "struct",
        ),
        (
            "type State [Ready, Waiting] extend { fn kind(borrow self) -> i32 { match self { State::Ready => 1, State::Waiting => 2 } } }",
            "State",
            "enum",
        ),
        (
            "type Box<T> { value: T } extend { fn get(borrow self) -> T { self.value } }",
            "Box",
            "struct",
        ),
    ];

    for (source, expected_name, expected_body) in cases {
        let parsed = parse(SourceId(0), source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
        let expected_items = if source.contains(" extend ") { 2 } else { 1 };
        assert_eq!(parsed.module.items.len(), expected_items, "{source}");
        let ItemKind::Type {
            name, definition, ..
        } = &parsed.module.items[0].kind
        else {
            panic!("first item was not a type declaration: {source}");
        };
        assert_eq!(name, expected_name, "{source}");
        assert!(
            matches!(
                (expected_body, definition),
                ("bodyless", TypeDefinition::Bodyless)
                    | ("struct", TypeDefinition::Struct(_))
                    | ("enum", TypeDefinition::Enum(_))
            ),
            "unexpected body for {source}: {definition:?}"
        );

        if expected_items == 2 {
            let ItemKind::InherentExtension {
                target, methods, ..
            } = &parsed.module.items[1].kind
            else {
                panic!("second item was not a trailing inherent extension: {source}");
            };
            assert_eq!(target.path, [expected_name], "{source}");
            assert_eq!(
                methods[0].name,
                if expected_name == "Box" {
                    "get"
                } else {
                    "kind"
                },
                "{source}"
            );
            if expected_name == "Box" {
                assert_eq!(target.arguments.len(), 1, "{source}");
                let ItemKind::InherentExtension {
                    generic_parameters, ..
                } = &parsed.module.items[1].kind
                else {
                    unreachable!()
                };
                assert_eq!(generic_parameters.len(), 1, "{source}");
            }
        }
    }
}
