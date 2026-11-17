//! Borrowing `match` (package B3): a scrutinee that cannot be moved (a
//! reference, an element or a field place) is matched in place. Payload
//! bindings are copies (primitives) or read-only borrows (aggregates), tracked
//! as loans with a variant step, so disjoint writes are accepted and
//! overlapping ones are BE005.
use memobits_analysis::lower_module;
use memobits_diagnostics::{Diagnostic, SourceId};
use memobits_ir::{InstructionKind, Program, UseMode};
use memobits_syntax::parse;

const DECLS: &str = "type P { x: i32, y: i32 } \
    type Shape [ Empty, Circle(f64), Rect(i32, i32), Poly(P, Array<i32, 3>) ] \
    type Cell { kind: Shape, n: i32 } \
    type Grid { cells: Array<Cell, 3>, extra: P } \
    type Wrap [ Plain, Boxed(Shape) ] \
    type H { s: Shape, o: P } \
    fn make(n: i32) -> Shape { if n > 0 { Shape::Rect(n, 2) } else { Shape::Empty } } \
    fn read(p: borrow P) -> i32 { p.x + p.y } \
    fn take(p: P) -> i32 { p.x } \
    fn is_big(s: borrow Shape) -> Bool { match s { Shape::Rect(w, h) => w * h > 10, _ => false } } ";

fn lower(body: &str) -> Result<Program, Vec<Diagnostic>> {
    let source = format!("{DECLS} fn main() -> i32 {{ {body} }}");
    let parsed = parse(SourceId(71), &source);
    assert!(
        parsed.diagnostics.is_empty(),
        "{source}: {:?}",
        parsed.diagnostics
    );
    lower_module(&parsed.module, "test", &["main".into()])
}

fn accepted(body: &str) -> Program {
    let program = lower(body).unwrap_or_else(|errors| panic!("{body}: {errors:?}"));
    program.validate().unwrap();
    let found = memobits_ownership::check_ownership(&program);
    assert!(found.is_empty(), "{body}: {found:?}");
    program
}

fn rejected(body: &str, code: &str, text: &str) {
    let found = match lower(body) {
        Err(errors) => errors,
        Ok(program) => memobits_ownership::check_ownership(&program),
    };
    assert!(
        found
            .iter()
            .any(|d| d.code.to_string() == code && d.message.contains(text)),
        "{body}: expected {code} containing {text:?}, found {found:?}"
    );
}

fn main_instructions(program: &Program) -> Vec<&InstructionKind> {
    program
        .functions
        .iter()
        .find(|f| f.path.name == "main")
        .unwrap()
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .map(|instruction| &instruction.kind)
        .collect()
}

#[test]
fn array_elements_fields_and_nested_places_match_in_place() {
    accepted("let a := [make(1); 2]; match a[0] { Shape::Rect(w, h) => w * h, _ => 0 }");
    accepted("let h := H { s: make(1), o: P { x: 1, y: 2 } }; match h.s { Shape::Rect(w, _) => w, _ => 0 }");
    accepted(
        "let g := Grid { cells: [Cell { kind: make(1), n: 1 }; 3], extra: P { x: 0, y: 0 } }; \
         var i := 1; match g.cells[i].kind { Shape::Rect(w, h) => w + h + g.cells[i].n, _ => 0 }",
    );
    // A place may be matched repeatedly; nothing is consumed.
    accepted(
        "let h := H { s: make(1), o: P { x: 1, y: 2 } }; \
         let a := match h.s { Shape::Rect(w, _) => w, _ => 0 }; \
         let b := match h.s { Shape::Empty => 1, _ => 2 }; a + b",
    );
}

#[test]
fn the_borrowing_match_addresses_payloads_instead_of_extracting_them() {
    let program = accepted(
        "let h := H { s: make(1), o: P { x: 1, y: 2 } }; \
         match h.s { Shape::Rect(w, h2) => w + h2, Shape::Poly(p, a) => p.x + a[1], _ => 0 }",
    );
    let kinds = main_instructions(&program);
    assert!(!kinds
        .iter()
        .any(|k| matches!(k, InstructionKind::VariantExtract { .. })));
    let addrs: Vec<_> = kinds
        .iter()
        .filter_map(|k| match k {
            InstructionKind::VariantAddr {
                variant,
                field,
                base,
                ..
            } => Some((*variant, *field, base.mode)),
            _ => None,
        })
        .collect();
    assert_eq!(
        addrs,
        [
            (2, 0, UseMode::Borrow),
            (2, 1, UseMode::Borrow),
            (3, 0, UseMode::Borrow),
            (3, 1, UseMode::Borrow),
        ]
    );
    // The tag is read once, through the reference.
    let tags = kinds
        .iter()
        .filter(|k| matches!(k, InstructionKind::EnumTag { base } if base.mode == UseMode::Borrow))
        .count();
    assert_eq!(tags, 1);
}

#[test]
fn borrow_and_share_parameters_and_conversions_match_in_place() {
    accepted("let s := make(3); if is_big(s.borrow()) { 1 } else { 0 }");
    accepted("let a := [make(3); 2]; if is_big(a[1].borrow()) { 1 } else { 0 }");
    accepted(
        "let h := H { s: make(3), o: P { x: 1, y: 2 } }; if is_big(h.s.borrow()) { 1 } else { 0 }",
    );
    accepted("let s := make(1); match s.borrow() { Shape::Rect(w, _) => w, _ => 0 }");
    accepted("var s := make(1); match s.share() { Shape::Rect(w, _) => w, _ => 0 }");
    accepted("let s := make(1); let r := s.borrow(); match r { Shape::Rect(w, _) => w, _ => 0 }");
}

#[test]
fn nested_enum_payloads_match_in_a_second_borrowing_match() {
    accepted(
        "let w := Wrap::Boxed(make(2)); \
         let r := match w.borrow() { Wrap::Boxed(s) => match s { \
             Shape::Rect(a, b) => a * b, _ => 0 }, Wrap::Plain => 0 }; r",
    );
}

#[test]
fn payload_aggregates_are_references_that_can_be_passed_indexed_and_read() {
    accepted(
        "let a := [Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]); 2]; \
         match a[1] { Shape::Poly(p, pts) => read(p) + p.x + pts[1], _ => 0 }",
    );
    accepted(
        "let h := H { s: Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]), o: P { x: 0, y: 0 } }; \
         match h.s { Shape::Poly(p, _) => read(p), _ => 0 }",
    );
}

#[test]
fn disjoint_writes_are_accepted_while_a_payload_borrow_is_live() {
    accepted(
        "var h := H { s: Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]), o: P { x: 0, y: 0 } }; \
         match h.s { Shape::Poly(p, _) => { h.o.y = 1; p.x }, _ => 0 }",
    );
    // A primitive payload is a copy, so the place itself may be rewritten.
    accepted(
        "var h := H { s: make(1), o: P { x: 0, y: 0 } }; \
         match h.s { Shape::Rect(w, _) => { h.s = Shape::Empty; w }, _ => 0 }",
    );
    // A payload borrow that is no longer used does not block writes.
    accepted(
        "var h := H { s: Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]), o: P { x: 0, y: 0 } }; \
         match h.s { Shape::Poly(p, _) => { let n := p.x; h.s = Shape::Empty; n }, _ => 0 }",
    );
}

#[test]
fn overlapping_writes_while_a_payload_borrow_is_live_are_be005() {
    rejected(
        "var h := H { s: Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]), o: P { x: 0, y: 0 } }; \
         match h.s { Shape::Poly(p, _) => { h.s = Shape::Empty; p.x }, _ => 0 }",
        "BE005",
        "cannot write `h.s` while it is borrowed",
    );
    // Moving the enclosing struct is an overlapping access too.
    rejected(
        "var h := H { s: Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]), o: P { x: 0, y: 0 } }; \
         match h.s { Shape::Poly(p, _) => { let g := h; p.x }, _ => 0 }",
        "BE005",
        "`h`",
    );
}

#[test]
fn a_dynamic_index_overlaps_every_element() {
    rejected(
        "var a := [Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]); 2]; var i := 0; var j := 1; \
         match a[i] { Shape::Poly(p, _) => { a[j] = Shape::Empty; p.x }, _ => 0 }",
        "BE005",
        "`a[_]`",
    );
    // Distinct constant indices are disjoint.
    accepted(
        "var a := [Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]); 2]; \
         match a[0] { Shape::Poly(p, _) => { a[1] = Shape::Empty; p.x }, _ => 0 }",
    );
}

#[test]
fn the_conflict_message_names_the_borrowed_payload() {
    let body = "var h := H { s: Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]), o: P { x: 0, y: 0 } }; \
         match h.s { Shape::Poly(p, _) => { h.s = Shape::Empty; p.x }, _ => 0 }";
    let program = lower(body).unwrap();
    let found = memobits_ownership::check_ownership(&program);
    let labels: Vec<&str> = found
        .iter()
        .flat_map(|d| d.labels.iter().map(|l| l.message.as_str()))
        .collect();
    assert!(
        labels
            .iter()
            .any(|l| l.contains("`h.s::Poly.0` was borrowed here")),
        "{labels:?}"
    );
    assert!(
        labels.iter().any(|l| l.contains("is used later here")),
        "{labels:?}"
    );
}

#[test]
fn payload_bindings_cannot_be_moved_out_or_written() {
    // Moving: the binding is a reference, not an owned value.
    rejected(
        "let h := H { s: Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]), o: P { x: 0, y: 0 } }; \
         match h.s { Shape::Poly(p, _) => take(p), _ => 0 }",
        "TE017",
        "reference values cannot escape",
    );
    rejected(
        "let h := H { s: Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]), o: P { x: 0, y: 0 } }; \
         let q: P = match h.s { Shape::Poly(p, _) => p, _ => P { x: 0, y: 0 } }; q.x",
        "TE017",
        "reference",
    );
    // Writing: matching is read-only, also through a share.
    rejected(
        "var h := H { s: Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]), o: P { x: 0, y: 0 } }; \
         match h.s { Shape::Poly(p, _) => { p.x = 3; 1 }, _ => 0 }",
        "TE004",
        "cannot assign through borrow binding 'p'",
    );
    rejected(
        "var h := H { s: Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]), o: P { x: 0, y: 0 } }; \
         match h.s { Shape::Poly(_, a) => { a[0] = 3; 1 }, _ => 0 }",
        "TE004",
        "borrow binding 'a'",
    );
    rejected(
        "var s := Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]); \
         match s.share() { Shape::Poly(p, _) => { p.x = 3; 1 }, _ => 0 }",
        "TE004",
        "borrow binding 'p'",
    );
    // A primitive payload is an immutable copy.
    rejected(
        "var h := H { s: make(1), o: P { x: 0, y: 0 } }; \
         match h.s { Shape::Rect(w, _) => { w = 3; w }, _ => 0 }",
        "TE004",
        "immutable",
    );
}

#[test]
fn owned_scrutinees_still_consume() {
    let found = {
        let program = lower("let s := make(1); let n := match s { _ => 1 }; take(P { x: n, y: 0 }); match s { _ => 2 }").unwrap();
        memobits_ownership::check_ownership(&program)
    };
    assert!(
        found.iter().any(|d| d.code.to_string() == "BE001"),
        "{found:?}"
    );
    // The payload of an owned match is an owned aggregate.
    accepted(
        "match Shape::Poly(P { x: 1, y: 2 }, [3, 4, 5]) { Shape::Poly(p, _) => take(p), _ => 0 }",
    );
}
