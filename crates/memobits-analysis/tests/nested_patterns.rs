//! Nested `match` patterns: typing of sub-patterns, coverage diagnostics from
//! the pattern matrix, and the lowered decision tree (one `Switch` per tested
//! level, one body per arm, no new IR operation).
use memobits_analysis::lower_module;
use memobits_diagnostics::{Diagnostic, SourceId};
use memobits_ir::{InstructionKind, Program, TerminatorKind};
use memobits_syntax::parse;

const DECLS: &str = "type Leaf [ A, B(u32), C(u32, u32) ] \
    type Mid [ X(Leaf), Y(Leaf, Leaf), Z ] \
    type Pt { x: i32, y: i32 } \
    fn mid(n: u32) -> Mid { if n > 0 { Mid::X(Leaf::B(n)) } else { Mid::Z } } \
    fn res(n: u32) -> u32? ! Error { Ok(Some(n)) } \
    fn look(m: borrow Mid) {} ";

fn parsed(source: &str) -> memobits_syntax::ParseResult {
    let parsed = parse(SourceId(71), source);
    assert!(
        parsed.diagnostics.is_empty(),
        "{source}: {:?}",
        parsed.diagnostics
    );
    parsed
}

fn lower(body: &str) -> Program {
    let source = format!("{DECLS} fn main() -> u32 {{ {body} }}");
    let program = lower_module(&parsed(&source).module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{body}: {errors:?}"));
    program.validate().unwrap();
    assert!(
        memobits_ownership::check_ownership(&program).is_empty(),
        "{body}"
    );
    program
}

fn diagnostics(body: &str) -> Vec<Diagnostic> {
    let source = format!("{DECLS} fn main() -> u32 {{ {body} }}");
    lower_module(&parsed(&source).module, "test", &["main".into()]).expect_err(body)
}

fn rejected(body: &str, code: &str, text: &str) {
    let found = diagnostics(body);
    assert!(
        found
            .iter()
            .any(|d| d.code.to_string() == code && d.message.contains(text)),
        "{body}: expected {code} containing {text:?}, found {found:?}"
    );
}

fn main_function(program: &Program) -> &memobits_ir::Function {
    program
        .functions
        .iter()
        .find(|function| function.path.name == "main")
        .expect("main")
}

fn switches(program: &Program) -> usize {
    main_function(program)
        .blocks
        .iter()
        .filter(|block| matches!(block.terminator.kind, TerminatorKind::Switch { .. }))
        .count()
}

#[test]
fn nested_patterns_lower_to_one_switch_per_tested_level() {
    let program = lower(
        "match mid(1) { Mid::X(Leaf::A) => 1, Mid::X(Leaf::B(n)) => n, Mid::X(Leaf::C(a, _)) => a, \
         Mid::Y(Leaf::A, _) => 4, Mid::Y(_, _) => 5, Mid::Z => 6 }",
    );
    // The outer tag, then the inner tag under `X` and under `Y`'s first slot.
    assert_eq!(switches(&program), 3);
    let main = main_function(&program);
    let extracts = main
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter(|instruction| matches!(instruction.kind, InstructionKind::VariantExtract { .. }))
        .count();
    assert!(extracts > 0);
}

#[test]
fn every_arm_body_is_lowered_exactly_once() {
    // The wildcard arm is reached from several leaves; its body is one block.
    let program = lower("match res(1) { Ok(Some(v)) => v, _ => 99 }");
    let main = main_function(&program);
    let constants = main
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter(|instruction| {
            matches!(&instruction.kind, InstructionKind::Constant(c)
                if format!("{c:?}").contains("99"))
        })
        .count();
    assert_eq!(constants, 1);
}

#[test]
fn sub_patterns_are_typed_against_their_payload() {
    for body in [
        "match res(1) { Ok(Some(v)) => v, Ok(None) => 0, Err(e) => e.code }",
        "match mid(1) { Mid::Y(Leaf::C(a, b), other) => a + b, _ => 0 }",
        "match (mid(1), res(2)) { (Mid::Z, _) => 1, (_, Ok(Some(v))) => v, (_, _) => 2 }",
    ] {
        lower(body);
    }
}

#[test]
fn coverage_names_an_uncovered_example_pattern() {
    rejected(
        "match res(1) { Ok(Some(v)) => v, Err(e) => e.code }",
        "TE031",
        "missing `Ok(None)`",
    );
    rejected(
        "match mid(1) { Mid::X(Leaf::A) => 1, Mid::X(Leaf::B(_)) => 2, Mid::Y(_, _) => 3, Mid::Z => 4 }",
        "TE031",
        "missing `Mid::X(Leaf::C(_, _))`",
    );
    lower("match mid(1) { Mid::Y(Leaf::A, Leaf::A) => 1, _ => 2 }");
    // A wildcard arm covers the rest, however deep the earlier arms go.
    lower("match mid(1) { Mid::X(Leaf::B(n)) => n, Mid::Y(Leaf::C(a, _), _) => a, _ => 0 }");
}

#[test]
fn unreachable_arms_include_patterns_covered_by_earlier_nested_arms() {
    rejected(
        "match mid(1) { Mid::Y(_, Leaf::A) => 1, Mid::Y(Leaf::B(_), Leaf::A) => 2, _ => 3 }",
        "TE032",
        "`Mid::Y(Leaf::B(_), Leaf::A)` is already matched",
    );
    rejected(
        "match mid(1) { Mid::X(_) => 1, Mid::X(Leaf::A) => 2, Mid::Y(_, _) => 3, Mid::Z => 4 }",
        "TE032",
        "already matched",
    );
}

#[test]
fn binding_names_are_unique_across_the_whole_pattern() {
    rejected(
        "match mid(1) { Mid::Y(Leaf::B(n), Leaf::B(n)) => n, _ => 0 }",
        "TE030",
        "more than once",
    );
}

#[test]
fn a_binding_that_names_a_variant_of_the_matched_enum_is_that_variant() {
    // `None` is the optional's variant, not a new binding.
    lower("match res(1) { Ok(Some(v)) => v, Ok(None) => 1, Err(_) => 2 }");
    // A fresh name in the same position binds the whole payload.
    lower("match res(1) { Ok(whole) => match whole { Some(v) => v, None => 0 }, Err(_) => 2 }");
}

#[test]
fn borrowed_nested_matches_lower_without_moves() {
    let program = lower(
        "var m := mid(2); look(m.borrow()); \
         match m.borrow() { Mid::X(Leaf::B(n)) => n, Mid::Y(_, Leaf::C(a, _)) => a, _ => 0 }",
    );
    let main = main_function(&program);
    assert!(main
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .any(|instruction| matches!(instruction.kind, InstructionKind::VariantAddr { .. })));
}
