//! Nesting of aggregates (package A3): struct-typed fields, array-typed fields
//! and arrays of structs, lowered through chained `FieldAddr` / `ElementAddr`
//! projections, with the diagnostics around what stays gated.
use memobits_analysis::lower_module;
use memobits_diagnostics::{Diagnostic, SourceId};
use memobits_ir::{Access, InstructionKind, Program, Type, TypeId};
use memobits_syntax::parse;

const DECLS: &str = "type P { x: i32, y: i32 } \
    type Line { a: P, b: P } \
    type Poly { n: u8, pts: array<i32, 4>, c: P } \
    fn make_p() -> P { P { x: 7, y: 8 } } \
    fn rd(p: borrow P) -> i32 { p.x } \
    fn bump(p: share P) { p.x += 1; } \
    fn both(a: share P, b: share P) {} \
    fn total(a: borrow array<P, 3>) -> i32 { a[0].x + a[2].y } \
    fn sum(p: borrow Poly) -> i32 { p.pts[0] + p.c.x } ";

fn parsed(source: &str) -> memobits_syntax::Module {
    let parsed = parse(SourceId(51), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    parsed.module
}

fn main_body(body: &str) -> String {
    format!("{DECLS} fn main() {{ {body} }}")
}

fn lower(source: &str) -> Program {
    let program = lower_module(&parsed(source), "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"));
    program.validate().unwrap();
    program
}

fn diagnostics(source: &str) -> Vec<Diagnostic> {
    lower_module(&parsed(source), "test", &["main".into()]).expect_err(source)
}

fn rejected(source: &str, code: &str, text: &str) {
    let found = diagnostics(source);
    assert!(
        found
            .iter()
            .any(|d| d.code.to_string() == code && d.message.contains(text)),
        "{source}: expected {code} containing {text:?}, found {found:?}"
    );
    assert!(found.iter().all(|d| d.span.is_some()), "{found:?}");
}

fn ownership(source: &str) -> Vec<String> {
    memobits_ownership::check_ownership(&lower(source))
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

fn accepted_body(body: &str) {
    let codes = ownership(&main_body(body));
    assert!(codes.is_empty(), "{body}: {codes:?}");
}

fn loan_rejected(body: &str) {
    let codes = ownership(&main_body(body));
    assert!(codes.iter().any(|c| c == "BE005"), "{body}: {codes:?}");
}

#[test]
fn nested_reads_chain_field_and_element_addresses() {
    let program = lower(&main_body(
        "var a := [Poly { n: 1, pts: [1, 2, 3, 4], c: P { x: 5, y: 6 } }; 2]; let v := a[1].pts[2]; let w := a[0].c.y;",
    ));
    let function = &program.functions.last().unwrap();
    let kinds: Vec<&str> = function
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match &instruction.kind {
            InstructionKind::ElementAddr {
                access: Access::Borrow,
                ..
            } => Some("element"),
            InstructionKind::FieldAddr {
                access: Access::Borrow,
                ..
            } => Some("field"),
            _ => None,
        })
        .collect();
    // a[1].pts[2]: element, field, element; a[0].c.y: element, field, field.
    assert_eq!(
        kinds,
        ["element", "field", "element", "element", "field", "field"]
    );
    // The chain is typed level by level: Poly element, Array field, i32 element.
    let borrowed: Vec<&Type> = function
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter(|instruction| {
            matches!(
                instruction.kind,
                InstructionKind::ElementAddr {
                    access: Access::Borrow,
                    ..
                } | InstructionKind::FieldAddr {
                    access: Access::Borrow,
                    ..
                }
            )
        })
        .map(|instruction| &function.values[instruction.output.unwrap().0 as usize])
        .collect();
    let inner = |ty: &Type| match ty {
        Type::Reference { inner, .. } => (**inner).clone(),
        other => panic!("not a reference: {other:?}"),
    };
    assert_eq!(inner(borrowed[0]), Type::Struct(TypeId(2)));
    assert!(matches!(inner(borrowed[1]), Type::Array { .. }));
    assert_eq!(
        inner(borrowed[2]),
        Type::Primitive(memobits_ir::Primitive::I32)
    );
}

#[test]
fn nested_writes_use_share_chains_and_whole_aggregate_stores() {
    let program = lower(&main_body(
        "var l := Line { a: P { x: 1, y: 2 }, b: make_p() }; \
         l.a.x = 3; l.b.y += 4; l.a = P { x: 9, y: 9 }; let o := make_p(); l.b = o;",
    ));
    let function = program.functions.last().unwrap();
    let stores: Vec<_> = function
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter(|i| matches!(i.kind, InstructionKind::Store { .. }))
        .collect();
    assert_eq!(stores.len(), 4);
    // The two whole-struct stores go through references to `P`.
    let whole = stores
        .iter()
        .filter(|i| {
            let InstructionKind::Store { value, .. } = &i.kind else {
                unreachable!()
            };
            matches!(
                value.source,
                memobits_ir::Source::Value(id) if function.values[id.0 as usize] == Type::Struct(TypeId(0))
            ) || matches!(
                value.source,
                memobits_ir::Source::Local(id) if function.locals[id.0 as usize].ty == Type::Struct(TypeId(0))
            )
        })
        .count();
    assert_eq!(whole, 2);
}

#[test]
fn evaluation_order_is_indices_then_rhs_then_checked_store() {
    let source = format!(
        "{DECLS} fn f() -> i32 {{ 0 }} fn g() -> i32 {{ 1 }} fn h() -> i32 {{ 2 }} \
         fn main() {{ var a := [Poly {{ n: 1, pts: [1, 2, 3, 4], c: P {{ x: 5, y: 6 }} }}; 2]; \
         a[f()].pts[g()] = h(); }}"
    );
    let program = lower(&source);
    let function = program.functions.last().unwrap();
    let instructions: Vec<_> = function
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .collect();
    let call_names: Vec<u32> = instructions
        .iter()
        .filter_map(|i| match &i.kind {
            InstructionKind::Call { callee, .. } => match callee.source {
                memobits_ir::Source::Function(id) => Some(id.0),
                _ => None,
            },
            _ => None,
        })
        .collect();
    // DECLS defines make_p, rd, bump, both, total, sum (0..=5), then f, g, h.
    assert_eq!(call_names, [6, 7, 8]);
    let position = |pred: &dyn Fn(&InstructionKind) -> bool| {
        instructions.iter().position(|i| pred(&i.kind)).unwrap()
    };
    let h_call = position(
        &|k| matches!(k, InstructionKind::Call { callee, .. } if callee.source == memobits_ir::Source::Function(memobits_ir::FunctionId(8))),
    );
    let first_share = instructions
        .iter()
        .enumerate()
        .skip(h_call)
        .find_map(|(index, i)| {
            matches!(
                i.kind,
                InstructionKind::ElementAddr {
                    access: Access::Share,
                    ..
                }
            )
            .then_some(index)
        })
        .unwrap();
    let store = instructions
        .iter()
        .enumerate()
        .skip(h_call)
        .find_map(|(index, i)| matches!(i.kind, InstructionKind::Store { .. }).then_some(index))
        .unwrap();
    assert!(h_call < first_share, "bounds checks come after the rhs");
    // The share chain (element, field, element) and the store are adjacent.
    assert_eq!(store, first_share + 3);
}

#[test]
fn array_of_struct_forms_are_accepted() {
    for body in [
        "let a := [P { x: 1, y: 2 }, make_p()]; let v := a[1].x + a[0].y;",
        "var a := [P { x: 0, y: 0 }; 8]; a[3].x = 5; a[4] = P { x: 1, y: 1 }; a[2].y += 3;",
        "let a: array<P, 0> = [P { x: 0, y: 0 }; 0];",
        "var a := [P { x: 0, y: 0 }; 1]; a[0].x = 1;",
        "var m := [[P { x: 0, y: 0 }; 2]; 3]; m[1][0].x = 2; let v := m[2][1].y;",
        "var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; let v := l.a.x + l.b.y;",
        "var p := Poly { n: 1, pts: [1, 2, 3, 4], c: P { x: 5, y: 6 } }; p.pts[2] += 3; p.pts = [4, 3, 2, 1]; p.c = P { x: 0, y: 0 }; let v := p.pts[0] + p.c.y;",
        "var a := [Poly { n: 1, pts: [1, 2, 3, 4], c: P { x: 5, y: 6 } }; 2]; a[1].pts[2] = 9; a[0].c.x += 1; let v := a[0].pts[3];",
        "let q := P { x: 1, y: 2 }; let l := Line { a: q, b: make_p() };",
    ] {
        accepted_body(body);
    }
}

#[test]
fn lending_sub_aggregates_matches_the_whole_aggregate_rules() {
    for body in [
        "var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; let v := rd(l.a.borrow()) + rd(l.b.borrow()); bump(l.a.share());",
        "var a := [P { x: 0, y: 0 }; 3]; let v := total(a.borrow()) + rd(a[1].borrow()); bump(a[2].share());",
        "var p := Poly { n: 1, pts: [1, 2, 3, 4], c: P { x: 5, y: 6 } }; let v := sum(p.borrow()); bump(p.c.share()); let r := p.pts.borrow();",
        "var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; var r := l.a.share(); r.x = 5; r = P { x: 1, y: 1 };",
    ] {
        accepted_body(body);
    }
}

#[test]
fn loans_to_overlapping_locations_still_conflict() {
    // A live reference to a location blocks writes to it, to anything below it
    // and to anything that encloses it (A4 overlap rule).
    for body in [
        "var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; let r := l.a.borrow(); l.a.x = 5; let v := r.x;",
        "var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; both(l.a.share(), l.a.share());",
        "var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; let r := l.a.borrow(); bump(l.a.share()); let v := r.x;",
        "var a := [P { x: 0, y: 0 }; 3]; let r := a[0].borrow(); a[0].x = 2; let v := r.x;",
        "var a := [P { x: 0, y: 0 }; 3]; both(a[0].share(), a[0].share());",
        "var p := Poly { n: 1, pts: [1, 2, 3, 4], c: P { x: 5, y: 6 } }; let r := p.pts.borrow(); p.pts[0] = 1; let v := r[0];",
        "var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; let r := l.a.borrow(); l = Line { a: P { x: 0, y: 0 }, b: P { x: 0, y: 0 } }; let v := r.x;",
    ] {
        loan_rejected(body);
    }
}

#[test]
fn loans_to_disjoint_fields_and_constant_elements_are_independent() {
    for body in [
        "var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; let r := l.a.borrow(); l.b.x = 5; let v := r.x;",
        "var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; both(l.a.share(), l.b.share());",
        "var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; let r := l.a.borrow(); bump(l.b.share()); let v := r.x;",
        "var a := [P { x: 0, y: 0 }; 3]; let r := a[0].borrow(); a[1].x = 2; let v := r.x;",
        "var a := [P { x: 0, y: 0 }; 3]; both(a[0].share(), a[1].share());",
        "var p := Poly { n: 1, pts: [1, 2, 3, 4], c: P { x: 5, y: 6 } }; let r := p.pts.borrow(); p.c.x = 1; let v := r[0];",
    ] {
        accepted_body(body);
    }
}

#[test]
fn moving_a_sub_aggregate_out_is_te022_for_fields_and_elements() {
    let setup = "var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; \
                 var a := [P { x: 0, y: 0 }; 3]; \
                 var p := Poly { n: 1, pts: [1, 2, 3, 4], c: P { x: 5, y: 6 } }; \
                 var m := [[1, 2], [3, 4]]; ";
    for statement in [
        "let q := l.a;",
        "let r := a[1];",
        "let q := p.pts;",
        "let q := p.c;",
        "let q := m[0];",
        "l.b = l.a;",
        "a[0] = a[1];",
        "p.pts = p.pts;",
        "bump_owned(l.a);",
        "bump_owned(a[0]);",
        "let q := [l.a, l.b];",
        "let q := Line { a: l.b, b: l.a };",
        "l.a;",
        "a[0];",
    ] {
        let source =
            format!("{DECLS} fn bump_owned(p: P) {{}} fn main() {{ {setup} {statement} }}");
        rejected(&source, "TE022", "cannot be moved out");
    }
    for source in [
        format!("{DECLS} fn f(l: Line) -> P {{ return l.a; }} fn main() {{}}"),
        format!("{DECLS} fn f(l: Line) -> P {{ l.a }} fn main() {{}}"),
        format!("{DECLS} fn f(a: array<P, 2>) -> P {{ return a[0]; }} fn main() {{}}"),
        format!("{DECLS} fn f(p: Poly) -> array<i32, 4> {{ p.pts }} fn main() {{}}"),
    ] {
        rejected(&source, "TE022", "partial moves are deferred");
    }
}

#[test]
fn reading_primitives_at_any_depth_copies_implicitly() {
    accepted_body(
        "var a := [Poly { n: 1, pts: [1, 2, 3, 4], c: P { x: 5, y: 6 } }; 2]; \
         let v := a[1].pts[2]; let w := a[0].c.y; let n := a[1].n; \
         let t := v + w; a[0].pts[0] = a[1].pts[1]; a[0].c.x = a[1].c.y;",
    );
}

#[test]
fn field_level_references_to_primitives_stay_gated_like_elements() {
    for body in [
        "var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; let r := l.a.x.share();",
        "var p := Poly { n: 1, pts: [1, 2, 3, 4], c: P { x: 5, y: 6 } }; let r := p.pts[0].share();",
        "var m := [[1, 2], [3, 4]]; let r := m[0][1].share();",
    ] {
        rejected(&main_body(body), "TE017", "references to primitive elements");
    }
}

#[test]
fn write_through_immutable_roots_is_te004() {
    for body in [
        "let l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; l.a.x = 1;",
        "let a := [P { x: 0, y: 0 }; 2]; a[0].x = 1;",
        "let p := Poly { n: 1, pts: [1, 2, 3, 4], c: P { x: 5, y: 6 } }; p.pts[1] = 1;",
        "let a := [P { x: 0, y: 0 }; 2]; a[0] = P { x: 1, y: 1 };",
    ] {
        rejected(&main_body(body), "TE004", "cannot assign");
    }
    rejected(
        &format!("{DECLS} fn w(l: borrow Line) {{ l.a.x = 1; }} fn main() {{}}"),
        "TE004",
        "through borrow binding",
    );
    rejected(
        &format!("{DECLS} fn w(a: borrow array<P, 2>) {{ a[0].x = 1; }} fn main() {{}}"),
        "TE004",
        "through borrow binding",
    );
}

#[test]
fn type_errors_in_nested_places() {
    rejected(
        &main_body("var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; l.a.z = 1;"),
        "TE024",
        "no field 'z'",
    );
    rejected(
        &main_body("var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; l.a = 1;"),
        "TE002",
        "expected P",
    );
    rejected(
        &main_body("var l := Line { a: 1, b: make_p() };"),
        "TE002",
        "expected P",
    );
    rejected(
        &main_body("var a := [P { x: 0, y: 0 }; 2]; a[0].x = true;"),
        "TE002",
        "expected i32",
    );
    rejected(
        &main_body("var p := Poly { n: 1, pts: [1, 2, 3], c: P { x: 5, y: 6 } };"),
        "TE002",
        "Array<i32, 4>",
    );
    rejected(
        &main_body("var p := Poly { n: 1, pts: [1, 2, 3, 4], c: P { x: 5, y: 6 } }; p.pts[4] = 1;"),
        "TE008",
        "out of bounds",
    );
    rejected(
        &main_body("var a := [P { x: 0, y: 0 }; 2]; a[2].x = 1;"),
        "TE008",
        "out of bounds",
    );
    rejected(
        &main_body(
            "var p := Poly { n: 1, pts: [1, 2, 3, 4], c: P { x: 5, y: 6 } }; p.pts[0].x = 1;",
        ),
        "TE024",
        "field access requires a struct",
    );
    rejected(
        &main_body("var a := [P { x: 0, y: 0 }; 2]; a.x = 1;"),
        "TE024",
        "field access requires a struct",
    );
}

#[test]
fn recursive_containment_through_arrays_is_te026() {
    for source in [
        "type A { xs: array<A, 2> } fn main() {}",
        "type A { xs: array<array<A, 2>, 3> } fn main() {}",
        "type A { b: array<B, 2> } type B { a: A } fn main() {}",
        "type A { b: B } type B { xs: array<A, 0> } fn main() {}",
        "type R = array<A, 2>; type A { xs: R } fn main() {}",
    ] {
        rejected(source, "TE026", "recursive struct");
    }
}

#[test]
fn aggregate_fields_and_elements_are_valid_by_value_types() {
    // Not recursive: a struct may repeat a type, and arrays may hold structs
    // that themselves hold arrays.
    lower("type P { x: i32 } type Q { a: P, b: P, c: array<P, 2> } type R { qs: array<Q, 2> } fn main() {}");
    lower("type G = array<P, 2>; type P { x: i32 } type H { g: G } fn main() {}");
}
