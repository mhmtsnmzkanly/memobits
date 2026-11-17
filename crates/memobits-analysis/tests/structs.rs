//! User-defined struct types: type table, literals, field reads, visibility and
//! the gates around every form outside this package.
use memobits_analysis::{check_types, lower_module, lower_resolved};
use memobits_diagnostics::{Diagnostic, SourceId};
use memobits_ir::{
    Access, CanonicalType, Constant, InstructionKind, Primitive, Program, Source, Type, TypeId,
};
use memobits_project::Project;
use memobits_resolve::{resolve, Target};
use memobits_syntax::parse;
use std::{
    fs,
    sync::atomic::{AtomicUsize, Ordering},
};

const P: &str = "type P { x: i32, y: i32 } ";

fn lower(source: &str) -> Program {
    let parsed = parse(SourceId(31), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let program = lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"));
    program.validate().unwrap();
    program
}

fn diagnostics(source: &str) -> Vec<Diagnostic> {
    let parsed = parse(SourceId(31), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    lower_module(&parsed.module, "test", &["main".into()]).expect_err(source)
}

fn codes(source: &str) -> Vec<String> {
    diagnostics(source)
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

/// Assert that `source` is rejected with `code` and a message containing `text`.
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

#[test]
fn struct_literal_and_field_reads_lower_to_struct_new_and_field_addr() {
    let program = lower(&format!(
        "{P} fn main() -> i32 {{ let p := P {{ y: 4, x: 3 }}; p.x * p.y }}"
    ));
    assert_eq!(program.types.len(), 1);
    assert_eq!(
        program.types[0].path,
        CanonicalType {
            package: "test".into(),
            module: vec!["main".into()],
            name: "P".into()
        }
    );
    let function = &program.functions[0];
    assert_eq!(function.locals[0].ty, Type::Struct(TypeId(0)));
    let instructions: Vec<_> = function
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .collect();
    // Initialisers are evaluated in source order (4 then 3) ...
    let constants: Vec<_> = instructions
        .iter()
        .filter_map(|i| match &i.kind {
            InstructionKind::Constant(Constant::Integer(text)) => Some((text.as_str(), i.output)),
            _ => None,
        })
        .collect();
    assert_eq!(constants[0].0, "4");
    assert_eq!(constants[1].0, "3");
    // ... but StructNew receives them in declaration order (x = 3, y = 4).
    let Some(InstructionKind::StructNew { ty, fields }) = instructions
        .iter()
        .find_map(|i| matches!(i.kind, InstructionKind::StructNew { .. }).then(|| i.kind.clone()))
    else {
        panic!("expected StructNew")
    };
    assert_eq!(ty, TypeId(0));
    assert_eq!(fields[0].source, Source::Value(constants[1].1.unwrap()));
    assert_eq!(fields[1].source, Source::Value(constants[0].1.unwrap()));
    let field_indices: Vec<_> = instructions
        .iter()
        .filter_map(|i| match &i.kind {
            InstructionKind::FieldAddr {
                field,
                access: Access::Borrow,
                ..
            } => Some(*field),
            _ => None,
        })
        .collect();
    assert_eq!(field_indices, [0, 1]);
    assert_eq!(
        instructions
            .iter()
            .filter(|i| matches!(i.kind, InstructionKind::Load { .. }))
            .count(),
        2
    );
}

#[test]
fn field_initialisers_are_evaluated_in_source_order_even_when_declared_differently() {
    let program = lower(&format!(
        "{P} fn f(n: i32) -> i32 {{ n }} \
         fn main() -> i32 {{ let p := P {{ y: f(2), x: f(1) }}; p.x + 0 }}"
    ));
    let main = &program.functions[1];
    let calls = main
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .filter(|i| matches!(i.kind, InstructionKind::Call { .. }))
        .count();
    assert_eq!(calls, 2);
    // The first call's argument is the constant 2 (the `y` initialiser).
    let first_call = main
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .find_map(|i| match &i.kind {
            InstructionKind::Call { arguments, .. } => Some(arguments[0]),
            _ => None,
        })
        .unwrap();
    let Source::Value(id) = first_call.source else {
        panic!()
    };
    let producer = main
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .find(|i| i.output == Some(id))
        .unwrap();
    assert!(matches!(&producer.kind, InstructionKind::Constant(Constant::Integer(n)) if n == "2"));
}

#[test]
fn literals_are_typed_by_the_declared_field_types() {
    let program = lower(
        "type M { a: u8, b: i64, c: Bool, d: f32, e: i16 } \
         fn main() -> i32 { let m := M { e: -7, a: 200, d: 1.5, c: true, b: 5 }; let e := m.e.copy(); 1 }",
    );
    let Some(memobits_ir::TypeDefKind::Struct { fields }) = program.types.first().map(|t| &t.kind)
    else {
        panic!()
    };
    let types: Vec<_> = fields.iter().map(|f| f.ty.clone()).collect();
    assert_eq!(
        types,
        [
            Type::Primitive(Primitive::U8),
            Type::Primitive(Primitive::I64),
            Type::Primitive(Primitive::Bool),
            Type::Primitive(Primitive::F32),
            Type::Primitive(Primitive::I16),
        ]
    );
}

#[test]
fn field_reads_work_in_arithmetic_comparison_conditions_and_indices() {
    for source in [
        "fn main() -> i32 { let p := P { x: 3, y: 4 }; p.x * p.y + 1 }",
        "fn main() -> Bool { let p := P { x: 3, y: 4 }; p.x < p.y }",
        "fn main() -> i32 { let p := P { x: 3, y: 4 }; if p.x == 3 { 1 } else { 2 } }",
        "fn main() -> i32 { let p := P { x: 1, y: 4 }; let a := [10, 20, 30]; a[p.x] + 0 }",
        "fn main() -> i32 { let p := P { x: 3, y: 4 }; -p.x }",
        "fn main() -> i32 { let p := P { x: 3, y: 4 }; let q := p.x.copy(); q + p.y.copy() }",
        "type F { on: Bool } fn main() -> i32 { let f := F { on: true }; if f.on { 1 } else { 2 } }",
        "type F { on: Bool } fn main() -> Bool { let f := F { on: true }; f.on && !f.on }",
        "type F { on: Bool } fn main() -> Bool { let f := F { on: false }; true && f.on }",
        "fn main() -> i32 { let p: P = P { x: 3, y: 4 }; p.x + 0 }",
        "type E {} fn main() -> i32 { let e := E {}; 1 }",
    ] {
        lower(&if source.starts_with("type ") {
            source.to_string()
        } else {
            format!("{P}{source}")
        });
    }
}

#[test]
fn literal_shape_errors_have_dedicated_diagnostics() {
    rejected(
        &format!("{P} fn main() {{ let p := P {{ x: 1 }}; }}"),
        "TE023",
        "missing field(s) in 'P' literal: y",
    );
    rejected(
        &format!("{P} fn main() {{ let p := P {{ x: 1, y: 2, z: 3 }}; }}"),
        "TE023",
        "has no field 'z'",
    );
    rejected(
        &format!("{P} fn main() {{ let p := P {{ x: 1, y: 2, x: 3 }}; }}"),
        "TE023",
        "'x' is initialised more than once",
    );
    rejected(
        &format!("{P} fn main() {{ let p := P {{ x: 1, y: true }}; }}"),
        "TE002",
        "expected i32, found Bool",
    );
    rejected(
        "type N = i32; fn main() { let p := N { x: 1 }; }",
        "TE023",
        "is not a struct type",
    );
    rejected(
        &format!("{P} fn main() {{ let p: i32 = P {{ x: 1, y: 2 }}; }}"),
        "TE002",
        "expected i32, found P",
    );
    rejected(
        &format!("{P} type Q {{ x: i32, y: i32 }} fn main() {{ let p: P = Q {{ x: 1, y: 2 }}; }}"),
        "TE002",
        "expected P, found Q",
    );
    rejected(
        "fn main() { let p := Missing { x: 1 }; }",
        "TE001",
        "unresolved type 'Missing'",
    );
    rejected(
        &format!("{P} fn main() {{ let p := P {{ x: 1.5, y: 2 }}; }}"),
        "TE002",
        "expected i32",
    );
    rejected(
        "type B { b: u8 } fn main() { let p := B { b: 300 }; }",
        "TE008",
        "does not fit u8",
    );
}

#[test]
fn field_access_errors() {
    rejected(
        &format!("{P} fn main() -> i32 {{ let p := P {{ x: 1, y: 2 }}; p.z + 1 }}"),
        "TE024",
        "has no field 'z'",
    );
    rejected(
        "fn main() -> i32 { let n := 4; n.x + 1 }",
        "TE024",
        "requires a struct value, found i32",
    );
    // Only the explicit error, not an extra extraction diagnostic.
    assert_eq!(
        codes("fn main() -> i32 { let n := 4; let m := n.x; 1 }"),
        ["TE024"]
    );
    rejected(
        "fn main() -> i32 { 1.field }",
        "TE017",
        "named local structs only",
    );
}

#[test]
fn reading_a_primitive_field_into_an_owned_position_copies_it() {
    for (source, what) in [
        ("let q := p.x; q", "binding"),
        ("let q: i32 = p.x; q", "annotated binding"),
        ("p.x", "tail"),
        ("return p.x;", "return"),
        ("let a := [p.x, 1]; 0", "array element"),
        ("f(p.x)", "argument"),
        ("if true { p.x } else { 1 }", "branch tail"),
        ("var v := 0; v = p.x; v", "assignment"),
        ("let q := P { x: p.x, y: 1 }; 0", "struct field initialiser"),
    ] {
        let source = format!("{P} fn f(a: i32) -> i32 {{ a }} fn main() -> i32 {{ let p := P {{ x: 1, y: 2 }}; {source} }}");
        let program = lower(&source);
        let moves = memobits_ownership::check_moves(&program);
        assert!(moves.is_empty(), "{what}: {moves:?}");
    }
    // The struct stays whole and its field stays readable after copies.
    lower(&format!(
        "{P} fn f(a: i32) -> i32 {{ a }} fn main() -> i32 {{ let p := P {{ x: 1, y: 2 }}; f(p.x) + f(p.x) + p.y }}"
    ));
    lower(&format!(
        "{P} fn main() -> i32 {{ let p := P {{ x: 1, y: 2 }}; let q := p.x.copy(); q }}"
    ));
}

#[test]
fn gated_forms_are_diagnostics_not_panics() {
    let p = "let p := P { x: 1, y: 2 };";
    for (source, text) in [
        // var struct bindings and field assignment
        (format!("{P} fn main() {{ var p := P {{ x: 1, y: 2 }}; }}"), "`var` struct bindings"),
        (format!("{P} fn main() {{ {p} p.x = 3; }}"), "assigning to a struct field"),
        (format!("{P} fn main() {{ {p} p.x += 3; }}"), "assigning to a struct field"),
        // whole-struct move / assignment / use as a value
        (format!("{P} fn main() {{ {p} let q := p; }}"), "whole structs cannot be used as values"),
        (format!("{P} fn main() {{ {p} p; }}"), "whole structs cannot be used as values"),
        (format!("{P} fn main() {{ var q := 1; {p} q = p; }}"), "whole structs cannot be used as values"),
        (format!("{P} fn main() {{ let q: P = if true {{ P {{ x: 1, y: 2 }} }} else {{ P {{ x: 3, y: 4 }} }}; }}"), "struct literals can only initialise"),
        (format!("{P} fn main() {{ P {{ x: 1, y: 2 }}; }}"), "struct literals can only initialise"),
        (format!("{P} fn main() {{ let x := P {{ x: 1, y: 2 }}.x; }}"), "struct literals can only initialise"),
        (format!("{P} fn main() {{ let a := [P {{ x: 1, y: 2 }}]; }}"), "struct literals can only initialise"),
        // parameters, results, references
        (format!("{P} fn f(p: P) {{}} fn main() {{}}"), "cannot appear in a function signature"),
        (format!("{P} fn f(p: borrow P) {{}} fn main() {{}}"), "cannot appear in a function signature"),
        (format!("{P} fn f(p: share P) {{}} fn main() {{}}"), "cannot appear in a function signature"),
        (format!("{P} fn f() -> P {{ P {{ x: 1, y: 2 }} }} fn main() {{}}"), "cannot appear in a function signature"),
        (format!("{P} pub fn main(p: P) {{}}"), "cannot appear in a function signature"),
        (format!("{P} fn main() {{ {p} let r := p.borrow(); }}"), "borrow/share conversion of a struct"),
        (format!("{P} fn main() {{ {p} let r := p.share(); }}"), "borrow/share conversion of a struct"),
        (format!("{P} fn main() {{ {p} let q := p.copy(); }}"), "copy is currently available only for primitive values"),
        // struct-typed and array-typed fields, arrays of structs
        (format!("{P} type L {{ a: P }} fn main() {{}}"), "struct-typed fields are not supported"),
        ("type L { a: Array<i32, 2> } fn main() {}".to_string(), "array-typed fields are not supported"),
        (format!("{P} fn main() {{ let a: Array<P, 2> = [P {{ x: 1, y: 2 }}, P {{ x: 1, y: 2 }}]; }}"), "arrays of structs"),
        (format!("{P} type G = Array<P, 2>; fn main() {{}}"), "arrays of structs"),
        // field access on a non-local base
        (format!("{P} fn f() -> i32 {{ 1 }} fn main() -> i32 {{ f().x + 1 }}"), "named local structs only"),
    ] {
        rejected(&source, "TE017", text);
    }
}

#[test]
fn recursive_structs_and_alias_cycles_are_diagnostics() {
    rejected("type A { a: A } fn main() {}", "TE026", "recursive struct");
    rejected(
        "type A { b: B } type B { a: A } fn main() {}",
        "TE026",
        "recursive struct",
    );
    rejected(
        "type N = A; type A { a: N } fn main() {}",
        "TE026",
        "recursive struct",
    );
    rejected(
        "type A = B; type B = A; fn main() {}",
        "TE026",
        "alias cycle",
    );
    rejected("type A = A; fn main() {}", "TE026", "alias cycle");
}

#[test]
fn enum_types_are_not_value_types_and_never_panic() {
    for source in [
        "type E [ A, B ] fn main() { let e: E = 1; }",
        "type E [ A, B ] fn f(e: E) {} fn main() {}",
        "type E [ A, B ] fn f() -> E { E::A } fn main() {}",
        "type E [ A, B ] type S { e: E } fn main() {}",
        "type E [ A, B ] type S = E; fn main() { let s := S { x: 1 }; }",
    ] {
        let found = codes(source);
        assert!(
            found.iter().any(|c| c == "TE001" || c == "TE016"),
            "{source}: {found:?}"
        );
    }
}

#[test]
fn aliases_resolve_wherever_a_type_is_named() {
    let program = lower(
        "type Num = i32; type Pair = P; type Row = Array<Num, 2>; \
         type P { x: Num, y: Num } \
         fn id(n: Num) -> Num { n } \
         fn main() -> Num { let p: Pair = Pair { x: id(3), y: 4 }; let r: Row = [1, 2]; p.x.copy() + r[1] }",
    );
    // Aliases add no type definitions of their own.
    assert_eq!(program.types.len(), 1);
    assert_eq!(
        program.functions[0].signature.result.as_ref(),
        &Type::Primitive(Primitive::I32)
    );
    // Standalone checking accepts the same program.
    let parsed = parse(
        SourceId(32),
        "type Num = i32; fn f(n: Num) -> Num { n } fn main() -> i64 { let x: Num = 1; 5 }",
    );
    assert!(check_types(&parsed.module).is_empty());
    rejected(
        "type Num = Missing; fn main() {}",
        "TE001",
        "unresolved type 'Missing'",
    );
    rejected(
        "type Num = i32; fn main() { let x: Num = true; }",
        "TE002",
        "expected i32, found Bool",
    );
}

#[test]
fn duplicate_type_declarations_and_fields_are_diagnostics() {
    rejected(
        "type P { x: i32 } type P { y: i32 } fn main() {}",
        "TE014",
        "duplicate type",
    );
    rejected(
        "type P { x: i32, x: i32 } fn main() {}",
        "TE023",
        "more than once",
    );
}

#[test]
fn private_field_reads_are_checked_against_the_declaring_module() {
    // A private field read, even when the (rejected) literal still gives a typed value.
    let fixture = Project2::new(&[
        ("geom", "pub type Hidden { pub x: i32, secret: i32 }"),
        (
            "main",
            "use geom::Hidden; fn main() -> i32 { let h := Hidden { x: 1, secret: 2 }; h.x + h.secret }",
        ),
    ]);
    let found = fixture.errors();
    assert!(
        found.iter().any(|d| d.code.to_string() == "TE025"
            && d.message
                .contains("cannot construct struct 'Hidden' outside module 'geom'")),
        "{found:?}"
    );
    assert!(
        found.iter().any(|d| d.code.to_string() == "TE025"
            && d.message
                .contains("field 'secret' of struct 'Hidden' is private to module 'geom'")),
        "{found:?}"
    );
}

#[test]
fn all_public_structs_are_constructible_and_readable_across_modules() {
    let fixture = Project2::new(&[
        (
            "geom",
            "pub type Point { pub x: i32, pub y: i32 } pub type Alias = Point; \
             pub fn local() -> i32 { let p := Point { x: 1, y: 2 }; p.x + p.y }",
        ),
        (
            "main",
            "use geom::Point; use geom::Alias; \
             fn main() -> i32 { \
                 let a := Point { x: 3, y: 4 }; \
                 let b := geom::Point { y: 6, x: 5 }; \
                 let c := Alias { x: 7, y: 8 }; \
                 a.x * b.y + c.y + geom::local() }",
        ),
    ]);
    let program = fixture.lower();
    // One canonical definition however it is spelled.
    assert_eq!(program.types.len(), 1);
    assert_eq!(program.types[0].path.module, ["geom"]);
    let main = program
        .functions
        .iter()
        .find(|f| f.path.name == "main")
        .unwrap();
    let ids: Vec<_> = main
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .filter_map(|i| match &i.kind {
            InstructionKind::StructNew { ty, .. } => Some(*ty),
            _ => None,
        })
        .collect();
    assert_eq!(ids, [TypeId(0); 3]);
}

#[test]
fn private_types_and_missing_names_are_rejected_before_types() {
    let fixture = Project2::new(&[
        ("geom", "type Hidden { x: i32 } pub fn f() {}"),
        ("main", "fn main() { let h := geom::Hidden { x: 1 }; }"),
    ]);
    let resolution = fixture.resolution();
    assert!(resolution
        .diagnostics
        .iter()
        .any(|d| d.code.to_string() == "ME007"));
    let fixture = Project2::new(&[
        ("geom", "pub fn f() {}"),
        ("main", "fn main() { let h := Nope { x: 1 }; }"),
    ]);
    assert!(fixture
        .resolution()
        .diagnostics
        .iter()
        .any(|d| d.code.to_string() == "NE003"));
}

static NEXT: AtomicUsize = AtomicUsize::new(0);

/// A throwaway project whose modules are given as `(name, source)`.
struct Project2(std::path::PathBuf);

impl Project2 {
    fn new(files: &[(&str, &str)]) -> Self {
        let root = std::env::temp_dir().join(format!(
            "mb-structs-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(root.join("src")).unwrap();
        fs::write(
            root.join("project.toml"),
            "[package]\nname='test'\nentry='main::main'\n",
        )
        .unwrap();
        for (name, source) in files {
            fs::write(root.join(format!("src/{name}.mb")), source).unwrap();
        }
        Self(root)
    }
    fn resolution(&self) -> memobits_resolve::Resolution {
        resolve(&Project::load(&self.0, None).unwrap(), Target::Application)
    }
    fn lower(&self) -> Program {
        let project = Project::load(&self.0, None).unwrap();
        let resolution = resolve(&project, Target::Application);
        assert!(
            resolution.diagnostics.is_empty(),
            "{:?}",
            resolution.diagnostics
        );
        let program = lower_resolved(&project, &resolution).unwrap_or_else(|e| panic!("{e:?}"));
        program.validate().unwrap();
        program
    }
    fn errors(&self) -> Vec<Diagnostic> {
        let project = Project::load(&self.0, None).unwrap();
        let resolution = resolve(&project, Target::Application);
        assert!(
            resolution.diagnostics.is_empty(),
            "{:?}",
            resolution.diagnostics
        );
        lower_resolved(&project, &resolution).unwrap_err()
    }
}

impl Drop for Project2 {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
