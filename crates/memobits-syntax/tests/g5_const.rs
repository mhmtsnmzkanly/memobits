use memobits_diagnostics::SourceId;
use memobits_syntax::{parse, ExprKind, ItemKind};

#[test]
fn const_items_keep_visibility_name_type_and_initializer() {
    let parsed = parse(
        SourceId(3),
        "const A: u8 = 1 + 2; pub const B: string = \"x\"; const C: f64 = -1.5;",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_eq!(parsed.module.items.len(), 3);
    let ItemKind::Const {
        public,
        name,
        ty,
        value,
    } = &parsed.module.items[0].kind
    else {
        panic!("const")
    };
    assert!(!public);
    assert_eq!(name, "A");
    assert_eq!(ty.path, ["u8"]);
    assert!(matches!(&value.kind, ExprKind::Binary { operator, .. } if operator == "+"));
    assert!(matches!(
        &parsed.module.items[1].kind,
        ItemKind::Const { public: true, name, .. } if name == "B"
    ));
}

#[test]
fn a_const_needs_a_type_annotation_and_a_semicolon() {
    for (source, message) in [
        ("const A = 1;", "needs a type annotation"),
        ("const A: u8 = 1", "expected ';'"),
        ("const A: u8;", "expected '='"),
        ("const: u8 = 1;", "expected identifier"),
    ] {
        let parsed = parse(SourceId(0), source);
        assert!(
            parsed
                .diagnostics
                .iter()
                .any(|d| d.message.contains(message)),
            "{source}: {:?}",
            parsed.diagnostics
        );
    }
}

#[test]
fn const_is_reserved_but_generic_const_parameters_still_parse() {
    let parsed = parse(
        SourceId(0),
        "type Lane<const N: u32> { width: i32 } fn f<const N: u32>(a: array<u8, N>) {}",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let parsed = parse(SourceId(0), "fn main() { let const := 1; }");
    assert!(!parsed.diagnostics.is_empty());
}

#[test]
fn a_repeat_count_may_name_a_constant() {
    let parsed = parse(
        SourceId(0),
        "fn main() { let a := [0; SIZE]; let b := [0; 4]; }",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let parsed = parse(SourceId(0), "fn main() { let a := [0; size]; }");
    assert!(!parsed.diagnostics.is_empty());
}
