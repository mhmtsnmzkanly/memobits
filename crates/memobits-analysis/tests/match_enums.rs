//! `match` on owned enum values (package B2): typing, exhaustiveness, pattern
//! diagnostics, the lowered tag read / `Switch` / payload extraction shape, and
//! the ownership consequences (the scrutinee is consumed, payloads are owned).
use memobits_analysis::lower_module;
use memobits_diagnostics::{Diagnostic, SourceId};
use memobits_ir::{InstructionKind, Program, TerminatorKind, UseMode};
use memobits_syntax::parse;

const DECLS: &str = "type P { x: i32, y: i32 } \
    type Shape [ Empty, Circle(f64), Rect(i32, i32), Poly(P, Array<u8, 3>) ] \
    type Wrap [ Plain, Boxed(Shape) ] \
    type H { s: Shape, n: i32 } \
    fn make(n: i32) -> Shape { if n > 0 { Shape::Rect(n, 2) } else { Shape::Empty } } \
    fn peek(s: borrow Shape) {} \
    fn eat(s: Shape) {} ";

fn lower(source: &str) -> Program {
    let parsed = parse(SourceId(70), source);
    assert!(
        parsed.diagnostics.is_empty(),
        "{source}: {:?}",
        parsed.diagnostics
    );
    let program = lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"));
    program.validate().unwrap();
    program
}

fn diagnostics(source: &str) -> Vec<Diagnostic> {
    let parsed = parse(SourceId(70), source);
    assert!(
        parsed.diagnostics.is_empty(),
        "{source}: {:?}",
        parsed.diagnostics
    );
    lower_module(&parsed.module, "test", &["main".into()]).expect_err(source)
}

fn rejected(body: &str, code: &str, text: &str) {
    let source = format!("{DECLS} fn main() -> i32 {{ {body} }}");
    let found = diagnostics(&source);
    assert!(
        found
            .iter()
            .any(|d| d.code.to_string() == code && d.message.contains(text)),
        "{body}: expected {code} containing {text:?}, found {found:?}"
    );
    assert!(found.iter().all(|d| d.span.is_some()), "{found:?}");
}

fn accepted(body: &str) -> Program {
    let program = lower(&format!("{DECLS} fn main() -> i32 {{ {body} }}"));
    let codes: Vec<String> = memobits_ownership::check_ownership(&program)
        .iter()
        .map(|d| d.code.to_string())
        .collect();
    assert!(codes.is_empty(), "{body}: {codes:?}");
    program
}

fn owned_error(body: &str, code: &str) {
    let program = lower(&format!("{DECLS} fn main() -> i32 {{ {body} }}"));
    let codes: Vec<String> = memobits_ownership::check_ownership(&program)
        .iter()
        .map(|d| d.code.to_string())
        .collect();
    assert!(codes.iter().any(|c| c == code), "{body}: {codes:?}");
}

const FULL: &str = "match s { Shape::Empty => 0, Shape::Circle(r) => 1, \
    Shape::Rect(w, h) => w + h, Shape::Poly(p, a) => p.x }";

#[test]
fn exhaustive_matches_check_and_unify_arm_types() {
    accepted(&format!("let s := make(2); {FULL}"));
    accepted("let s := make(2); match s { Shape::Rect(w, _) => w, _ => 0 }");
    accepted("let s := make(2); match s { _ => 7 }");
    accepted("let r := match make(1) { Shape::Circle(r) => r, _ => 0.5 }; 1");
    // Arms of Unit type in statement position; the value is not used.
    accepted("var n := 0; match make(1) { Shape::Empty => { n = 1; } _ => { n = 2; } } n");
    // A literal in the first arm takes its type from the expected result.
    accepted("let a: u8 = match make(1) { Shape::Empty => 1, _ => 2 }; 0");
}

#[test]
fn arm_results_must_agree_and_may_diverge() {
    rejected(
        "match make(1) { Shape::Empty => 1, _ => 2.5 }",
        "TE013",
        "match arms have incompatible types",
    );
    rejected(
        "let n: i32 = match make(1) { Shape::Empty => 1, _ => 2.5 }; n",
        "TE013",
        "i32 and f64",
    );
    accepted("match make(1) { Shape::Empty => return 5, _ => 1 }");
    accepted("loop { let n := match make(1) { Shape::Empty => break, _ => 3 }; return n; } 9");
    accepted("match make(1) { Shape::Empty => return 1, _ => return 2 }");
}

#[test]
fn wrong_enum_arity_and_unsupported_patterns_are_reported() {
    rejected(
        "match make(1) { Wrap::Plain => 1, _ => 2 }",
        "TE030",
        "belongs to enum 'Wrap'",
    );
    rejected(
        "match make(1) { Shape::Circle => 1, _ => 2 }",
        "TE030",
        "has 1 payload value(s) but the pattern binds 0",
    );
    rejected(
        "match make(1) { Shape::Rect(a) => 1, _ => 2 }",
        "TE030",
        "has 2 payload value(s) but the pattern binds 1",
    );
    rejected(
        "match make(1) { Shape::Empty(a) => 1, _ => 2 }",
        "TE030",
        "has 0 payload value(s) but the pattern binds 1",
    );
    rejected(
        "match make(1) { Shape::Rect(a, a) => 1, _ => 2 }",
        "TE030",
        "more than once",
    );
    rejected(
        "match make(1) { other => 1 }",
        "TE030",
        "binding patterns are not supported",
    );
    rejected(
        "match make(1) { Shape::Cube => 1, _ => 2 }",
        "TE030",
        "no variant 'Cube'",
    );
    rejected(
        "match make(1) { P::x => 1, _ => 2 }",
        "TE030",
        "does not name an enum variant",
    );
}

#[test]
fn exhaustiveness_names_the_missing_variants() {
    rejected(
        "match make(1) { Shape::Empty => 1, Shape::Circle(_) => 2 }",
        "TE031",
        "missing Shape::Rect, Shape::Poly",
    );
    rejected(
        "match make(1) { Shape::Empty => 1, Shape::Rect(_, _) => 2, Shape::Poly(_, _) => 3 }",
        "TE031",
        "missing Shape::Circle;",
    );
    rejected("match make(1) { }", "TE031", "missing Shape::Empty");
}

#[test]
fn duplicate_and_unreachable_arms_are_errors() {
    rejected(
        "match make(1) { Shape::Empty => 1, Shape::Empty => 2, _ => 3 }",
        "TE032",
        "variant 'Shape::Empty' is already matched",
    );
    rejected(
        "match make(1) { _ => 1, Shape::Empty => 2 }",
        "TE032",
        "earlier `_` arm",
    );
    rejected(
        "match make(1) { _ => 1, _ => 2 }",
        "TE032",
        "earlier `_` arm",
    );
    rejected(
        "match make(1) { Shape::Empty => 1, Shape::Circle(_) => 1, Shape::Rect(_, _) => 1, \
         Shape::Poly(_, _) => 1, _ => 2 }",
        "TE032",
        "every variant is already matched",
    );
}

#[test]
fn scrutinee_must_be_an_enum() {
    rejected(
        "match 1 { _ => 1 }",
        "TE029",
        "requires an enum value, found i32",
    );
    rejected(
        "let p := P { x: 1, y: 2 }; match p { _ => 1 }",
        "TE029",
        "found P",
    );
}

#[test]
fn enum_equality_is_gated_and_points_at_match() {
    rejected(
        "let a := make(1); let b := make(2); if a == b { 1 } else { 2 }",
        "TE007",
        "use `match`",
    );
    rejected("let a := 1 == make(1); 0", "TE007", "use `match`");
}

#[test]
fn payload_bindings_are_owned_locals_scoped_to_their_arm() {
    rejected(
        "match make(1) { Shape::Rect(w, _) => w, _ => w }",
        "TE005",
        "w",
    );
    // A binding is immutable.
    rejected(
        "match make(1) { Shape::Rect(w, _) => { w = 2; w } _ => 0 }",
        "TE004",
        "immutable",
    );
    // Bindings shadow outer names only inside their arm.
    accepted("let w := 10; let n := match make(1) { Shape::Rect(w, _) => w, _ => 0 }; w + n");
}

#[test]
fn lowering_reads_the_tag_switches_and_extracts_payloads() {
    let program = accepted(&format!("let s := make(2); {FULL}"));
    let main = program.functions.last().unwrap();
    let mut tags = 0;
    let mut extracts = Vec::new();
    for block in &main.blocks {
        for instruction in &block.instructions {
            match &instruction.kind {
                InstructionKind::EnumTag { .. } => tags += 1,
                InstructionKind::VariantExtract {
                    variant,
                    field,
                    base,
                } => extracts.push((*variant, *field, base.mode)),
                _ => {}
            }
        }
    }
    assert_eq!(tags, 1);
    // Rect binds both fields (the last one consumes); Poly binds both; Circle one.
    assert_eq!(
        extracts,
        [
            (1, 0, UseMode::Consume),
            (2, 0, UseMode::Read),
            (2, 1, UseMode::Consume),
            (3, 0, UseMode::Read),
            (3, 1, UseMode::Consume),
        ]
    );
    let switches: Vec<_> = main
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator.kind {
            TerminatorKind::Switch {
                targets, default, ..
            } => Some((
                targets.iter().map(|(v, _)| *v).collect::<Vec<_>>(),
                default.is_some(),
            )),
            _ => None,
        })
        .collect();
    assert_eq!(switches, [(vec![0, 1, 2, 3], false)]);
}

#[test]
fn a_wildcard_arm_becomes_the_switch_default() {
    let program = accepted("match make(1) { Shape::Rect(w, _) => w, _ => 0 }");
    let main = program.functions.last().unwrap();
    let found = main
        .blocks
        .iter()
        .find_map(|block| match &block.terminator.kind {
            TerminatorKind::Switch {
                targets, default, ..
            } => Some((targets.len(), default.is_some())),
            _ => None,
        });
    assert_eq!(found, Some((1, true)));
}

#[test]
fn the_scrutinee_is_consumed_exactly_once() {
    owned_error(
        "let s := make(1); let n := match s { _ => 1 }; eat(s); n",
        "BE001",
    );
    owned_error(
        "let s := make(1); let n := match s { Shape::Empty => 1, _ => 2 }; \
         match s { _ => n }",
        "BE001",
    );
    owned_error(
        "let s := make(1); match s { Shape::Empty => 1, _ => 2 }; let t := s; 0",
        "BE001",
    );
    // A call result and a construction are temporaries: nothing to reuse.
    accepted("match Shape::Circle(1.0) { Shape::Circle(r) => 1, _ => 2 }");
    accepted("match Shape::Empty { Shape::Empty => 1, _ => 2 }");
    // Reassigning a `var` after the match makes it usable again.
    accepted("var s := make(1); let n := match s { _ => 1 }; s = make(2); eat(s); n");
}

#[test]
fn aggregate_payloads_move_out_and_primitives_copy() {
    accepted(
        "match Shape::Poly(P { x: 3, y: 4 }, [1, 2, 3]) { \
         Shape::Poly(p, a) => { let first: u8 = a[0]; p.x + p.y } _ => 0 }",
    );
    owned_error(
        "match Shape::Poly(P { x: 3, y: 4 }, [1, 2, 3]) { \
         Shape::Poly(p, a) => { let q := p; let r := p; 0 } _ => 0 }",
        "BE001",
    );
    // A payload moved into a binding can be passed on.
    accepted(
        "match Wrap::Boxed(make(2)) { Wrap::Boxed(inner) => { eat(inner); 1 } Wrap::Plain => 0 }",
    );
    owned_error(
        "match Wrap::Boxed(make(2)) { Wrap::Boxed(inner) => { eat(inner); eat(inner); 1 } \
         Wrap::Plain => 0 }",
        "BE001",
    );
}

#[test]
fn nested_enums_match_in_two_steps() {
    accepted(
        "match Wrap::Boxed(make(2)) { Wrap::Boxed(s) => match s { \
         Shape::Rect(w, h) => w * h, _ => 0 }, Wrap::Plain => 0 }",
    );
}

#[test]
fn matches_inside_loops_reinitialise_their_bindings() {
    accepted(
        "var total := 0; var i := 0; \
         loop { if i == 4 { break; } \
         total += match make(i) { Shape::Rect(w, h) => w + h, _ => 0 }; i += 1; } total",
    );
}

#[test]
fn matches_can_sit_in_owned_value_positions() {
    accepted("let s := match make(1) { Shape::Empty => Shape::Empty, _ => Shape::Empty }; 0");
    accepted(
        "let s := match make(1) { Shape::Empty => Shape::Circle(1.0), _ => make(3) }; eat(s); 0",
    );
    // As a temporary a unit variant is not an owned-value position.
    rejected(
        "match make(1) { Shape::Empty => Shape::Empty, _ => Shape::Empty }; 0",
        "TE017",
        "owned value",
    );
}
