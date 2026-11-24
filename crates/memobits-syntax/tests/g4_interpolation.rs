use memobits_diagnostics::SourceId;
use memobits_syntax::{parse, ExprKind, InterpolationPart, ItemKind, StatementKind};

fn initializer(literal: &str) -> (ExprKind, Vec<String>) {
    let source = format!("fn main() {{ let s := \"{literal}\"; }}");
    let parsed = parse(SourceId(7), &source);
    let messages = parsed
        .diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect();
    let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
        panic!("function")
    };
    let StatementKind::Binding { value, .. } = &body.statements[0].kind else {
        panic!("binding")
    };
    (value.kind.clone(), messages)
}

fn shape(literal: &str) -> Vec<String> {
    let (kind, messages) = initializer(literal);
    assert!(messages.is_empty(), "{messages:?}");
    let ExprKind::Interpolation(parts) = kind else {
        panic!("expected an interpolation for {literal:?}")
    };
    parts
        .iter()
        .map(|part| match part {
            InterpolationPart::Text(text) => format!("text:{text}"),
            InterpolationPart::Value(value) => match &value.kind {
                ExprKind::Path(path) => format!("name:{}", path.join("::")),
                other => panic!("{other:?}"),
            },
        })
        .collect()
}

#[test]
fn placeholders_split_text_and_keep_source_order() {
    assert_eq!(shape("{a}"), ["name:a"]);
    assert_eq!(shape("x = {x}!"), ["text:x = ", "name:x", "text:!"]);
    assert_eq!(shape("{a}{b}{a}"), ["name:a", "name:b", "name:a"]);
    assert_eq!(shape("{{{a}}}"), ["text:{", "name:a", "text:}"]);
    assert_eq!(shape("é{größe}😀"), ["text:é", "name:größe", "text:😀"]);
}

#[test]
fn escaped_braces_alone_make_a_plain_literal_with_unescaped_text() {
    for (literal, text) in [
        ("{{}}", "{}"),
        ("a}}b{{c", "a}b{c"),
        ("", ""),
        ("plain", "plain"),
    ] {
        let (kind, messages) = initializer(literal);
        assert!(messages.is_empty(), "{messages:?}");
        assert_eq!(kind, ExprKind::StringLiteral(text.into()), "{literal:?}");
    }
}

#[test]
fn placeholder_spans_cover_the_identifier() {
    let source = "fn main() { let s := \"ab {name} cd\"; }";
    let parsed = parse(SourceId(7), source);
    assert!(parsed.diagnostics.is_empty());
    let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
        panic!("function")
    };
    let StatementKind::Binding { value, .. } = &body.statements[0].kind else {
        panic!("binding")
    };
    let ExprKind::Interpolation(parts) = &value.kind else {
        panic!("interpolation")
    };
    let InterpolationPart::Value(name) = &parts[1] else {
        panic!("name")
    };
    assert_eq!(&source[name.span.start..name.span.end], "name");
}

#[test]
fn malformed_braces_are_lexical_errors() {
    for (literal, message) in [
        ("{", "unterminated `{`"),
        ("{}", "empty `{}`"),
        ("}", "unmatched `}`"),
        ("{a.b}", "only a plain identifier"),
        ("{ a }", "only a plain identifier"),
        ("{a}}", "unmatched `}`"),
    ] {
        let (_, messages) = initializer(literal);
        assert_eq!(messages.len(), 1, "{literal:?}: {messages:?}");
        assert!(messages[0].starts_with("SE001"), "{messages:?}");
        assert!(messages[0].contains(message), "{literal:?}: {messages:?}");
    }
}
