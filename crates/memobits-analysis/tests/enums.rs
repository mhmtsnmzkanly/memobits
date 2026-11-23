//! Enum types as values (package B1): declarations in the type table, variant
//! construction, aggregate behaviour (moves, parameters, joins, fields, arrays)
//! and the diagnostics around misuse. Inspection with `match` is tested in
//! `match_enums.rs`.
use memobits_analysis::lower_module;
use memobits_diagnostics::{Diagnostic, SourceId};
use memobits_ir::{
    Access, Constant, InstructionKind, Primitive, Program, Source, Type, TypeDefKind, TypeId,
};
use memobits_syntax::parse;

const SHAPE: &str = "type P { x: i32, y: i32 } \
    type Shape [ Empty, Circle(f64), Rect(i32, i32), Poly(P, array<u8, 3>) ] \
    fn make(n: i32) -> Shape { if n > 0 { Shape::Rect(n, 2) } else { Shape::Empty } } \
    fn eat(s: Shape) {} \
    fn peek(s: borrow Shape) {} \
    fn poke(s: share Shape) { s = Shape::Empty; } \
    type H { s: Shape, n: i32 } ";

fn parsed(source: &str) -> memobits_syntax::Module {
    let parsed = parse(SourceId(61), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    parsed.module
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

fn body(text: &str) -> String {
    format!("{SHAPE} fn main() {{ {text} }}")
}

fn accepted(text: &str) {
    let codes = ownership(&body(text));
    assert!(codes.is_empty(), "{text}: {codes:?}");
}

fn owned_error(text: &str, code: &str) {
    let codes = ownership(&body(text));
    assert!(codes.iter().any(|c| c == code), "{text}: {codes:?}");
}

/// The enum constructions in `main`, the last function.
fn enum_news(program: &Program) -> Vec<(TypeId, u32, usize)> {
    program
        .functions
        .last()
        .unwrap()
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .filter_map(|i| match &i.kind {
            InstructionKind::EnumNew {
                ty,
                variant,
                payload,
            } => Some((*ty, *variant, payload.len())),
            _ => None,
        })
        .collect()
}

#[test]
fn declarations_become_nominal_enum_definitions() {
    let program = lower(&body(""));
    let TypeDefKind::Enum { variants } = &program.types[1].kind else {
        panic!("expected an enum definition");
    };
    assert_eq!(program.types[1].path.name, "Shape");
    let names: Vec<_> = variants.iter().map(|v| v.name.as_str()).collect();
    assert_eq!(names, ["Empty", "Circle", "Rect", "Poly"]);
    assert!(variants[0].payload.is_empty());
    assert_eq!(variants[1].payload, [Type::Primitive(Primitive::F64)]);
    assert_eq!(
        variants[2].payload,
        [
            Type::Primitive(Primitive::I32),
            Type::Primitive(Primitive::I32)
        ]
    );
    assert_eq!(
        variants[3].payload,
        [
            Type::Struct(TypeId(0)),
            Type::Array {
                element: Box::new(Type::Primitive(Primitive::U8)),
                len: 3
            }
        ]
    );
}

#[test]
fn structs_and_enums_share_one_id_space_in_declaration_order() {
    let program = lower("type A [ X(B) ] type B { v: i32 } type C [ Y(A), Z ] fn main() {}");
    assert!(matches!(program.types[0].kind, TypeDefKind::Enum { .. }));
    assert!(matches!(program.types[1].kind, TypeDefKind::Struct { .. }));
    let TypeDefKind::Enum { variants } = &program.types[2].kind else {
        panic!("C is an enum")
    };
    assert_eq!(variants[0].payload, [Type::Enum(TypeId(0))]);
}

#[test]
fn payloads_nest_through_enums_arrays_and_structs_in_any_order() {
    lower(
        "type Outer [ Wrap(Inner), Many(array<Inner, 2>) ] \
         type Inner [ One(Holder), Two ] \
         type Holder { e: array<Deep, 2> } \
         type Deep [ D(i64), E(array<array<u8, 2>, 2>) ] \
         fn main() {}",
    );
}

#[test]
fn aliases_name_enum_types_and_variant_paths() {
    lower(
        "type Shape [ Empty, Circle(f64) ] type S = Shape; \
         fn f(s: S) -> S { s } \
         fn main() { let a: S = Shape::Circle(1.0); let b := f(a); }",
    );
}

#[test]
fn an_empty_enum_is_rejected() {
    rejected("type E [] fn main() {}", "TE027", "declares no variants");
    rejected(
        "type E [] fn f(e: E) {} fn main() {}",
        "TE027",
        "at least one",
    );
}

#[test]
fn recursion_by_value_is_the_recursive_type_diagnostic() {
    for source in [
        "type E [ A(E) ] fn main() {}",
        "type E [ A(i32), B(array<E, 2>) ] fn main() {}",
        "type A [ X(B) ] type B [ Y(A) ] fn main() {}",
        "type S { e: E } type E [ A(S) ] fn main() {}",
        "type E [ A(array<array<E, 2>, 3>) ] fn main() {}",
    ] {
        rejected(source, "TE026", "recursive");
    }
    rejected(
        "type E [ A(E) ] fn main() {}",
        "TE026",
        "recursive enum: 'E' contains 'E' by value",
    );
}

#[test]
fn payload_types_must_resolve() {
    rejected("type E [ A(Missing) ] fn main() {}", "TE001", "Missing");
    rejected(
        "type E [ A(array<i32, 99999999999>) ] fn main() {}",
        "TE008",
        "implementation limit",
    );
}

#[test]
fn construction_emits_enum_new_with_the_variant_index() {
    let program = lower(&body(
        "let a := Shape::Empty; let b := Shape::Circle(1.5); let c := Shape::Rect(1, 2);",
    ));
    assert_eq!(
        enum_news(&program),
        [(TypeId(1), 0, 0), (TypeId(1), 1, 1), (TypeId(1), 2, 2)]
    );
}

#[test]
fn payload_arguments_are_evaluated_left_to_right_and_moved_in() {
    let program = lower(&body("let r := Shape::Rect(3, 4);"));
    let main = program.functions.last().unwrap();
    let instructions = &main.blocks[0].instructions;
    let constants: Vec<_> = instructions
        .iter()
        .filter_map(|i| match &i.kind {
            InstructionKind::Constant(Constant::Integer(text)) => Some(text.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(constants, ["3", "4"]);
    let new = instructions
        .iter()
        .find_map(|i| match &i.kind {
            InstructionKind::EnumNew { payload, .. } => Some(payload.clone()),
            _ => None,
        })
        .unwrap();
    assert!(new
        .iter()
        .all(|operand| matches!(operand.source, Source::Value(_))
            && operand.mode == memobits_ir::UseMode::Consume));
}

#[test]
fn aggregate_payloads_are_moved_in_and_primitives_copied() {
    accepted(
        "let p := P { x: 1, y: 2 }; let xs: array<u8, 3> = [1, 2, 3]; let n := 5; \
         let s := Shape::Poly(p, xs); let t := Shape::Rect(n, n); let u := n + 1;",
    );
    owned_error(
        "let p := P { x: 1, y: 2 }; let xs: array<u8, 3> = [1, 2, 3]; \
         let s := Shape::Poly(p, xs); let q := p;",
        "BE001",
    );
    owned_error(
        "let p := P { x: 1, y: 2 }; let xs: array<u8, 3> = [1, 2, 3]; \
         let s := Shape::Poly(p, xs); let ys := xs;",
        "BE001",
    );
}

#[test]
fn construction_diagnostics() {
    rejected(
        "type E [ A ] fn main() { let e := E::B; }",
        "TE028",
        "has no variant 'B'",
    );
    rejected(
        "type E [ A(i32) ] fn main() { let e := E::B(1); }",
        "TE028",
        "has no variant 'B'",
    );
    rejected(&body("let s := Shape::Rect(1);"), "TE010", "expects 2");
    rejected(
        &body("let s := Shape::Rect(1, 2, 3);"),
        "TE010",
        "expects 2",
    );
    rejected(&body("let s := Shape::Circle(true);"), "TE002", "f64");
    rejected(&body("let s := Shape::Rect(1, 2.5);"), "TE002", "i32");
    rejected(&body("let s := Shape::Empty(1);"), "TE028", "no payload");
    rejected(&body("let s := Shape::Empty();"), "TE028", "no payload");
    rejected(
        &body("let s := Shape::Circle;"),
        "TE028",
        "construct it as Shape::Circle(...)",
    );
    rejected(&body("let s := Shape::Poly(1, 2);"), "TE002", "P");
    // A primitive read through a reference is copied into the payload.
    lower(&body("let a := 1.5; let s := Shape::Circle(a.borrow());"));
}

#[test]
fn enum_values_must_sit_in_owned_value_positions() {
    rejected(&body("Shape::Empty;"), "TE017", "owned value");
    rejected(&body("let a := Shape::Empty; a;"), "TE017", "whole arrays");
    rejected(&body("let n := Shape::Empty + 1;"), "TE017", "owned value");
}

#[test]
fn enums_have_no_fields_indexing_or_arithmetic() {
    rejected(
        &body("let a := Shape::Empty; let n := a.x;"),
        "TE024",
        "struct",
    );
    rejected(
        &body("let a := Shape::Empty; let n := a[0];"),
        "TE007",
        "Array",
    );
    rejected(
        &body("let a := Shape::Empty; let b := Shape::Empty; let c := a == b;"),
        "TE007",
        "use `match`",
    );
}

#[test]
fn bindings_assignment_and_moves() {
    accepted("let a := Shape::Empty; let b := a;");
    accepted("var a := Shape::Empty; a = Shape::Circle(2.0); a = make(1);");
    accepted("var a := Shape::Empty; let b := a; a = Shape::Empty; let c := a;");
    owned_error("let a := Shape::Empty; let b := a; let c := a;", "BE001");
    owned_error("let a := Shape::Empty; eat(a); eat(a);", "BE001");
    owned_error("let a := Shape::Empty; eat(a); peek(a.borrow());", "BE001");
    rejected(
        &body("let a := Shape::Empty; a = Shape::Empty;"),
        "TE004",
        "a",
    );
    rejected(&body("var a := Shape::Empty; a = 1;"), "TE002", "Shape");
    rejected(
        &body("let a: Shape = Shape::Empty; let b: P = a;"),
        "TE002",
        "P",
    );
}

#[test]
fn parameters_results_and_joins() {
    accepted(
        "let a := make(3); eat(a); \
         var b := Shape::Empty; peek(b.borrow()); poke(b.share()); \
         let c := if true { Shape::Circle(1.0) } else { make(0) }; eat(c); \
         let d := { let t := Shape::Empty; t }; eat(d);",
    );
    accepted("let a := Shape::Empty; let b := if true { a } else { Shape::Empty };");
    owned_error(
        "let a := Shape::Empty; let b := if true { a } else { Shape::Empty }; eat(a);",
        "BE001",
    );
    rejected(
        &body("let a := Shape::Empty; poke(a.share());"),
        "TE017",
        "mutable local owner",
    );
}

#[test]
fn return_values_and_early_returns_of_enums() {
    lower(
        "type E [ A, B(i32) ] \
         fn pick(n: i32) -> E { if n > 0 { return E::B(n); } E::A } \
         fn main() { let e := pick(1); }",
    );
    rejected("type E [ A ] fn f() -> E { 1 } fn main() {}", "TE002", "E");
}

#[test]
fn enum_fields_arrays_and_repetition() {
    accepted(
        "let h := H { s: Shape::Circle(1.0), n: 1 }; let a := [Shape::Empty, make(2)]; \
         let r := [Shape::Rect(1, 2); 4]; let g: array<Shape, 2> = [make(1), make(0)];",
    );
    // Repetition evaluates the element expression once per element: the
    // construction sits inside the generated loop, not outside it.
    let program = lower(&body("let r := [Shape::Rect(1, 2); 4];"));
    assert_eq!(enum_news(&program).len(), 1);
    let main = program.functions.last().unwrap();
    assert!(main.blocks.len() > 1);
    let loop_blocks_with_new = main.blocks[1..]
        .iter()
        .filter(|b| {
            b.instructions
                .iter()
                .any(|i| matches!(i.kind, InstructionKind::EnumNew { .. }))
        })
        .count();
    assert_eq!(loop_blocks_with_new, 1);
    // Moving an enum into a struct field or an element consumes the local.
    owned_error(
        "let s := Shape::Empty; let h := H { s: s, n: 1 }; eat(s);",
        "BE001",
    );
    owned_error(
        "let s := Shape::Empty; let a := [s, Shape::Empty]; eat(s);",
        "BE001",
    );
    // Element and field reads cannot move an enum out.
    rejected(
        &body("let h := H { s: Shape::Empty, n: 1 }; let t := h.s;"),
        "TE022",
        "cannot be moved out",
    );
    rejected(
        &body("let a := [Shape::Empty; 2]; let t := a[0];"),
        "TE022",
        "cannot be moved out",
    );
}

#[test]
fn whole_enum_borrows_conflict_conservatively() {
    accepted("var a := Shape::Empty; peek(a.borrow()); a = Shape::Circle(1.0);");
    accepted("var a := Shape::Empty; let r := a.borrow(); peek(r);");
    owned_error(
        "var a := Shape::Empty; let r := a.borrow(); a = Shape::Circle(1.0); peek(r);",
        "BE005",
    );
    owned_error(
        "var a := Shape::Empty; let r := a.share(); peek(a.borrow()); poke(r);",
        "BE005",
    );
    owned_error(
        "var a := Shape::Empty; let r := a.borrow(); eat(a); peek(r);",
        "BE005",
    );
    owned_error(
        "var a := Shape::Empty; let r := a.share(); eat(a); poke(r);",
        "BE005",
    );
    // Two live references, one exclusive, to the same enum.
    owned_error(
        "var a := Shape::Empty; let r := a.borrow(); poke(a.share()); peek(r);",
        "BE005",
    );
    // Reads through a field path overlap the whole root only when the paths do.
    owned_error(
        "var h := H { s: Shape::Empty, n: 1 }; let r := h.s.borrow(); h.s = Shape::Empty; peek(r);",
        "BE005",
    );
    accepted("var h := H { s: Shape::Empty, n: 1 }; let r := h.s.borrow(); h.n = 2; peek(r);");
}

#[test]
fn enum_parameter_borrows_are_loan_checked_like_other_aggregates() {
    let codes = ownership(
        "type E [ A, B(i32) ] fn two(a: share E, b: share E) {} \
         fn main() { var e := E::A; two(e.share(), e.share()); }",
    );
    assert!(codes.iter().any(|c| c == "BE005"), "{codes:?}");
}

#[test]
fn enum_types_have_the_expected_ir_access_modes() {
    let program = lower(&body(""));
    let peek = program
        .functions
        .iter()
        .find(|f| f.path.name == "peek")
        .unwrap();
    assert_eq!(peek.signature.parameters[0].access, Access::Borrow);
    assert_eq!(peek.signature.parameters[0].ty, Type::Enum(TypeId(1)));
}
