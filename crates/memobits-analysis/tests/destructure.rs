//! Whole-value destructuring (package A4): `let P { x, y: alias } := value;`.
use memobits_analysis::lower_module;
use memobits_diagnostics::{Diagnostic, SourceId};
use memobits_ir::{InstructionKind, Program, UseMode};
use memobits_syntax::parse;

const DECLS: &str = "type P { x: i32, y: u8 } \
    type Line { a: P, b: P, n: i32 } \
    type Grid { cells: Array<i32, 3>, k: i32 } \
    type Named { text: string, count: u32 } \
    type U {} \
    fn make() -> Line { Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 }, n: 5 } } ";

fn parsed(source: &str) -> memobits_syntax::Module {
    let parsed = parse(SourceId(53), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    parsed.module
}

fn lower(body: &str) -> Program {
    let source = format!("{DECLS} fn main() {{ {body} }}");
    let program = lower_module(&parsed(&source), "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{body}: {errors:?}"));
    program.validate().unwrap();
    program
}

fn diagnostics(body: &str) -> Vec<Diagnostic> {
    let source = format!("{DECLS} fn main() {{ {body} }}");
    lower_module(&parsed(&source), "test", &["main".into()]).expect_err(body)
}

fn rejected(body: &str, code: &str, text: &str) {
    let found = diagnostics(body);
    assert!(
        found
            .iter()
            .any(|d| d.code.to_string() == code && d.message.contains(text)),
        "{body}: expected {code} containing {text:?}, found {found:?}"
    );
    assert!(found.iter().all(|d| d.span.is_some()), "{found:?}");
}

fn ownership(body: &str) -> Vec<String> {
    memobits_ownership::check_ownership(&lower(body))
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

#[test]
fn destructuring_binds_primitive_and_aggregate_fields() {
    for body in [
        "let p := P { x: 1, y: 2 }; let P { x, y } := p; let s := x + 1;",
        "let P { x, y: alias } := P { x: 1, y: 2 }; let s := alias.copy() + 0;",
        "let Line { a, b: other, n } := make(); let s := a.x + other.x + n;",
        "let l := make(); let Line { a, b, n } := l; let P { x, y } := a; let P { x: bx, y: by } := b;",
        "let Grid { cells, k } := Grid { cells: [1, 2, 3], k: 4 }; let s := cells[2] + k;",
        "var P { x, y } := P { x: 1, y: 2 }; x += 1; let s := x;",
        "let U {} := U {};",
        "let u := U {}; let U {} := u;",
    ] {
        let codes = ownership(body);
        assert!(codes.is_empty(), "{body}: {codes:?}");
    }
}

#[test]
fn destructuring_lowers_to_extractions_with_one_consuming_read() {
    let program = lower("let p := P { x: 1, y: 2 }; let P { x, y: w } := p;");
    let function = program.functions.last().unwrap();
    let modes: Vec<UseMode> = function
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match &instruction.kind {
            InstructionKind::Extract { base, .. } => Some(base.mode),
            _ => None,
        })
        .collect();
    assert_eq!(modes, vec![UseMode::Read, UseMode::Consume]);
}

#[test]
fn the_destructured_value_is_consumed_exactly_once() {
    for body in [
        "let p := P { x: 1, y: 2 }; let P { x, y } := p; let s := p.x;",
        "let p := P { x: 1, y: 2 }; let P { x, y } := p; let q := p;",
        "let l := make(); let Line { a, b, n } := l; let m := l.n;",
        "let u := U {}; let U {} := u; let v := u;",
        "let p := P { x: 1, y: 2 }; let P { x, y } := p; let P { x: x2, y: y2 } := p;",
    ] {
        assert!(ownership(body).contains(&"BE001".into()), "{body}");
    }
    // A moved `var` source can be assigned again and destructured once more.
    let codes = ownership(
        "var p := P { x: 1, y: 2 }; let P { x, y } := p; p = P { x: 3, y: 4 }; let s := p.x;",
    );
    assert!(codes.is_empty(), "{codes:?}");
}

#[test]
fn bindings_follow_the_binding_mutability() {
    rejected(
        "let P { x, y } := P { x: 1, y: 2 }; x = 5;",
        "TE004",
        "immutable binding 'x'",
    );
    rejected("let Line { a, b, n } := make(); a.x = 5;", "TE004", "'a'");
    let codes = ownership("var Line { a, b, n } := make(); a.x = 5; b = P { x: 0, y: 0 };");
    assert!(codes.is_empty(), "{codes:?}");
}

#[test]
fn pattern_mistakes_have_clear_diagnostics() {
    rejected("let P { x } := P { x: 1, y: 2 };", "TE023", "missing: y");
    rejected("let Line { a } := make();", "TE023", "missing: b, n");
    rejected(
        "let P { x, y, z } := P { x: 1, y: 2 };",
        "TE023",
        "no field 'z'",
    );
    rejected(
        "let P { x, x: x2, y } := P { x: 1, y: 2 };",
        "TE023",
        "more than once",
    );
    rejected(
        "let P { x, y: x } := P { x: 1, y: 2 };",
        "TE023",
        "introduced more than once",
    );
    rejected(
        "let Missing { x } := P { x: 1, y: 2 };",
        "TE001",
        "type 'Missing'",
    );
    rejected("let i32 { x } := 1;", "TE023", "not a struct type");
    rejected(
        "let P { x, y } := Line { a: P { x: 1, y: 2 }, b: P { x: 1, y: 2 }, n: 1 };",
        "TE002",
        "expected",
    );
    rejected(
        "let l := make(); let P { x, y } := l.a;",
        "TE022",
        "cannot be moved out",
    );
    rejected(
        "var l := make(); let r := l.borrow(); let P { x, y } := r;",
        "TE002",
        "cannot destructure a reference",
    );
}

#[test]
fn nested_patterns_omission_and_rest_are_gated_by_the_parser() {
    for (source, expected) in [
        (
            "fn main() { let Line { a: P { x, y }, b, n } := make(); }",
            "nested destructuring",
        ),
        ("fn main() { let Line { a, b, .. } := make(); }", "`..`"),
        ("fn main() { let Line { .. } := make(); }", "`..`"),
        (
            "fn main() { let Line { a, b, n } = make(); }",
            "expected ':='",
        ),
    ] {
        let result = parse(SourceId(54), source);
        assert!(
            result
                .diagnostics
                .iter()
                .any(|d| d.message.contains(expected)),
            "{source}: {:?}",
            result.diagnostics
        );
    }
}

#[test]
fn tuple_destructuring_binds_positional_elements_and_consumes_the_source_once() {
    for body in [
        "let pair := (40, true); let (number, flag) := pair; let result := if flag { number + 2 } else { 0 };",
        "var (number, flag) := (40, true); number += 2; let result := if flag { number } else { 0 };",
        "let nested := ((40, true), 2); let (inner, count) := nested; let (number, flag) := inner; let result := if flag { number + count } else { 0 };",
        "let nested := ((40, true), 2); let ((number, flag), _) := nested; let result := if flag { number + 2 } else { 0 };",
        "let text := \"xy\".concat(\"!\"); let pair := (text, 40 as u32); let (moved, count) := pair; let result := moved.len() + count;",
        "let text := \"xy\".concat(\"!\"); let pair := (40 as u32, text); let (count, moved) := pair; let result := moved.len() + count;",
        "let text := \"xy\".concat(\"!\"); let pair := (text, 40 as u32); let (_, count) := pair; let result := count;",
        "let () := ();",
    ] {
        let codes = ownership(body);
        assert!(codes.is_empty(), "{body}: {codes:?}");
    }

    let program = lower("let pair := (40, true); let (number, flag) := pair;");
    let function = program.functions.last().unwrap();
    let modes: Vec<UseMode> = function
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match &instruction.kind {
            InstructionKind::Extract { base, .. } => Some(base.mode),
            _ => None,
        })
        .collect();
    assert_eq!(modes, vec![UseMode::Read, UseMode::Consume]);
}

#[test]
fn tuple_destructuring_rejects_invalid_patterns_and_accepts_nested_string_tuples() {
    rejected(
        "let text := \"xy\".concat(\"!\"); let (moved, count) := (text, 40 as u32);",
        "TE017",
        "requires a named owned tuple local",
    );
    rejected(
        "let named := Named { text: \"xy\".concat(\"!\"), count: 40 }; let Named { text, count } := named;",
        "TE018",
        "a struct owning a heap String can only move directly into a new local",
    );
    rejected(
        "let pair := (1, true); let (same, same) := pair;",
        "TE023",
        "introduced more than once",
    );
    rejected(
        "let pair := (1, true); let (only, second, third) := pair;",
        "TE023",
        "expects 2 bindings",
    );
    rejected("let (first, second) := 42;", "TE023", "not a tuple type");
    lower("let text := \"xy\"; let inner := (text, 40 as u32); let outer := (inner, true); let (nested, enabled) := outer;");
    assert!(
        ownership("let pair := (1, true); let (number, flag) := pair; let later := pair.0;")
            .contains(&"BE001".into())
    );
    assert!(
        ownership("let text := \"xy\".concat(\"!\"); let pair := (text, 40 as u32); let (moved, count) := pair; let later := pair.1;")
            .contains(&"BE001".into())
    );
}

#[test]
fn only_owned_string_tuple_parameters_enter_heap_cleanup_tracking() {
    let source = parsed(
        "fn discard(pair: ((string, string), u32)) {} fn scalar(value: u32) {} fn borrowed(value: borrow i32) {} fn borrowed_tuple(pair: borrow ((string, string), u32)) {} fn main() {}",
    );
    let program = lower_module(&source, "test", &["main".into()]).unwrap();
    program.validate().unwrap();
    let facts = program.heap_strings();
    let parameter_fact = |name: &str| {
        let (index, function) = program
            .functions
            .iter()
            .enumerate()
            .find(|(_, function)| function.path.name == name)
            .unwrap();
        (index, function.parameter_locals[0])
    };

    let (discard, tuple_parameter) = parameter_fact("discard");
    assert!(facts[discard].locals.contains(&tuple_parameter));
    assert!(program.functions[discard].blocks[0]
        .instructions
        .iter()
        .any(|instruction| matches!(instruction.kind, InstructionKind::EndStructLocal { local } if local == tuple_parameter)));

    let (scalar, scalar_parameter) = parameter_fact("scalar");
    assert!(!facts[scalar].locals.contains(&scalar_parameter));
    assert!(!program.functions[scalar].blocks[0]
        .instructions
        .iter()
        .any(|instruction| matches!(instruction.kind, InstructionKind::EndStructLocal { .. })));

    let (borrowed, reference_parameter) = parameter_fact("borrowed");
    assert!(!facts[borrowed].locals.contains(&reference_parameter));
    assert!(!program.functions[borrowed].blocks[0]
        .instructions
        .iter()
        .any(|instruction| matches!(instruction.kind, InstructionKind::EndStructLocal { .. })));

    let (borrowed_tuple, reference_tuple) = parameter_fact("borrowed_tuple");
    assert!(!facts[borrowed_tuple].locals.contains(&reference_tuple));
    assert!(!program.functions[borrowed_tuple].blocks[0]
        .instructions
        .iter()
        .any(|instruction| matches!(instruction.kind, InstructionKind::EndStructLocal { .. })));
}
