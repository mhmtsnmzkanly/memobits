use memobits_analysis::check_control_flow;
use memobits_diagnostics::{render, SourceFile, SourceId};
use memobits_syntax::parse;

fn check(source: &str) -> Vec<memobits_diagnostics::Diagnostic> {
    let parsed = parse(SourceId(7), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    check_control_flow(&parsed.module)
}

#[test]
fn reports_both_keywords_with_source_spans_in_order() {
    let source = "fn main() {\n  break;\n  continue;\n}";
    let diagnostics = check(source);
    assert_eq!(diagnostics.len(), 2);
    assert_eq!(diagnostics[0].code.to_string(), "TE020");
    assert_eq!(diagnostics[1].code.to_string(), "TE021");
    let first = render(
        &diagnostics[0],
        Some(SourceFile {
            id: SourceId(7),
            name: "main.mb",
            text: source,
        }),
    );
    assert!(first.contains("main.mb:2:3"), "{first}");
    assert!(first.contains("break;"));
    let second = render(
        &diagnostics[1],
        Some(SourceFile {
            id: SourceId(7),
            name: "main.mb",
            text: source,
        }),
    );
    assert!(second.contains("main.mb:3:3"), "{second}");
}

#[test]
fn loop_scope_applies_to_nested_branches_then_ends() {
    let diagnostics = check(
        "fn main() { loop { if true { break; } else { continue; } loop { break; } } break; }",
    );
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code.to_string(), "TE020");
}

#[test]
fn visits_nested_expression_positions() {
    for source in [
        "fn main() { let x := { break; 1 }; }",
        "fn main() { x = { continue; 1 }; }",
        "fn main() { { break; x } = 1; }",
        "fn main() { return { continue; 1 }; }",
        "fn main() { f({ break; 1 }); }",
        "fn main() { ({ continue; f })(1); }",
        "fn main() { if { break; true } { 1 } else { continue; 2 }; }",
        "fn main() { -{ break; 1 } + { continue; 2 }; }",
        "fn main() { ({ break; x }).field; }",
    ] {
        let diagnostics = check(source);
        assert!(!diagnostics.is_empty(), "missed: {source}");
    }
}

#[test]
fn valid_nested_expressions_inside_loop_have_no_errors() {
    let diagnostics =
        check("fn main() { loop { f({ if true { break; } else { continue; } 1 }); } }");
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
}
