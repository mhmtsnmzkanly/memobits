//! Struct mutation, whole-value moves, parameters and results (package A2):
//! typing, lowering shape and ownership, checked from source form.
use memobits_analysis::{lower_module, lower_resolved};
use memobits_diagnostics::{Diagnostic, SourceId};
use memobits_ir::{Access, InstructionKind, Program, Type, TypeId};
use memobits_project::Project;
use memobits_resolve::{resolve, Target};
use memobits_syntax::parse;
use std::{
    fs,
    sync::atomic::{AtomicUsize, Ordering},
};

const P: &str = "type P { x: i32, y: i32 } ";
const DECLS: &str = "type P { x: i32, y: i32 } \
    fn read(p: borrow P) -> i32 { p.x + p.y } \
    fn bump(p: share P) { p.x += 1; } \
    fn two(a: share P, b: share P) {} \
    fn mixed(a: share P, b: borrow P) {} \
    fn both(a: borrow P, b: borrow P) -> i32 { a.x + b.y } \
    fn own(p: P) -> i32 { p.x + 0 } \
    fn make() -> P { P { x: 1, y: 2 } } \
    fn pass(p: P) -> P { p } ";

fn lower(source: &str) -> Program {
    let parsed = parse(SourceId(41), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let program = lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"));
    program.validate().unwrap();
    program
}

fn analysis_errors(source: &str) -> Vec<Diagnostic> {
    let parsed = parse(SourceId(41), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    lower_module(&parsed.module, "test", &["main".into()]).expect_err(source)
}

fn ownership_codes(source: &str) -> Vec<String> {
    memobits_ownership::check_ownership(&lower(source))
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

fn accepted(source: &str) {
    let codes = ownership_codes(source);
    assert!(codes.is_empty(), "{source}: {codes:?}");
}

fn owned_rejected(source: &str, code: &str) {
    let codes = ownership_codes(source);
    assert!(codes.iter().any(|c| c == code), "{source}: {codes:?}");
}

fn rejected(source: &str, code: &str, text: &str) {
    let found = analysis_errors(source);
    assert!(
        found
            .iter()
            .any(|d| d.code.to_string() == code && d.message.contains(text)),
        "{source}: expected {code} containing {text:?}, found {found:?}"
    );
    assert!(found.iter().all(|d| d.span.is_some()), "{found:?}");
}

fn main_body(body: &str) -> String {
    format!("{DECLS}fn main() {{ {body} }}")
}

fn instructions(program: &Program, function: usize) -> Vec<&memobits_ir::Instruction> {
    program.functions[function]
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .collect()
}

#[test]
fn var_structs_and_field_writes_lower_to_share_field_addresses_and_stores() {
    let program = lower(&format!(
        "{P} fn main() -> i32 {{ var p := P {{ x: 1, y: 2 }}; p.x = 5; p.y += 3; p.x * p.y }}"
    ));
    assert!(program.functions[0].locals[0].mutable);
    let all = instructions(&program, 0);
    let shares = all
        .iter()
        .filter(|i| {
            matches!(
                i.kind,
                InstructionKind::FieldAddr {
                    access: Access::Share,
                    ..
                }
            )
        })
        .count();
    assert_eq!(shares, 2);
    let stores = all
        .iter()
        .filter(|i| matches!(i.kind, InstructionKind::Store { .. }))
        .count();
    assert_eq!(stores, 2);
    // The compound write reads the field first through a Borrow address.
    assert!(all.iter().any(|i| matches!(
        i.kind,
        InstructionKind::FieldAddr {
            field: 1,
            access: Access::Borrow,
            ..
        }
    )));
}

#[test]
fn field_write_evaluates_base_then_right_hand_side_then_stores() {
    // `p.x = f()` : the call precedes the Share field address and the store.
    let program = lower(
        "type P { x: i32 } fn f() -> i32 { 1 } \
         fn main() { var p := P { x: 0 }; p.x = f(); }",
    );
    let all = instructions(&program, 1);
    let call = all
        .iter()
        .position(|i| matches!(i.kind, InstructionKind::Call { .. }))
        .unwrap();
    let address = all
        .iter()
        .position(|i| {
            matches!(
                i.kind,
                InstructionKind::FieldAddr {
                    access: Access::Share,
                    ..
                }
            )
        })
        .unwrap();
    let store = all
        .iter()
        .position(|i| matches!(i.kind, InstructionKind::Store { .. }))
        .unwrap();
    assert!(call < address && address + 1 == store);
}

#[test]
fn compound_field_write_reads_the_old_value_before_the_right_hand_side() {
    let program = lower(
        "type P { x: i32 } fn f() -> i32 { 1 } \
         fn main() { var p := P { x: 0 }; p.x += f(); }",
    );
    let all = instructions(&program, 1);
    let load = all
        .iter()
        .position(|i| matches!(i.kind, InstructionKind::Load { .. }))
        .unwrap();
    let call = all
        .iter()
        .position(|i| matches!(i.kind, InstructionKind::Call { .. }))
        .unwrap();
    assert!(load < call);
}

#[test]
fn field_writes_through_let_borrow_and_immutable_shares_are_te004() {
    rejected(
        &format!("{P} fn main() {{ let p := P {{ x: 1, y: 2 }}; p.x = 3; }}"),
        "TE004",
        "immutable struct binding 'p'",
    );
    rejected(
        &format!("{P} fn main() {{ let p := P {{ x: 1, y: 2 }}; p.x += 3; }}"),
        "TE004",
        "immutable struct binding 'p'",
    );
    rejected(
        &format!("{P} fn f(p: borrow P) {{ p.x = 1; }} fn main() {{}}"),
        "TE004",
        "through borrow binding 'p'",
    );
    rejected(
        &format!("{P} fn f(p: P) {{ p.x = 1; }} fn main() {{}}"),
        "TE004",
        "immutable struct binding 'p'",
    );
    rejected(
        &format!("{P} fn main() {{ var p := P {{ x: 1, y: 2 }}; let r := p.share(); r.x = 1; }}"),
        "TE004",
        "immutable share binding 'r'",
    );
    rejected(
        &format!("{P} fn main() {{ var p := P {{ x: 1, y: 2 }}; let r := p.borrow(); r.x = 1; }}"),
        "TE004",
        "borrow binding 'r'",
    );
    // A `var` share binding, a share parameter and a `var` owned parameter may write.
    lower(&format!(
        "{P} fn f(var p: P) -> i32 {{ p.x = 1; p.x + 0 }} fn g(p: share P) {{ p.y = 2; }} \
         fn main() {{ var p := P {{ x: 1, y: 2 }}; var r := p.share(); r.x = 9; g(r.share()); }}"
    ));
}

#[test]
fn field_write_type_and_privacy_errors() {
    rejected(
        &format!("{P} fn main() {{ var p := P {{ x: 1, y: 2 }}; p.x = true; }}"),
        "TE002",
        "expected i32, found bool",
    );
    rejected(
        &format!("{P} fn main() {{ var p := P {{ x: 1, y: 2 }}; p.z = 1; }}"),
        "TE024",
        "no field 'z'",
    );
    rejected(
        "type B { on: bool } fn main() { var b := B { on: true }; b.on += 1; }",
        "TE007",
        "numeric",
    );
    rejected(
        "type B { b: u8 } fn main() { var b := B { b: 1 }; b.b = 300; }",
        "TE008",
        "does not fit u8",
    );
}

#[test]
fn private_fields_cannot_be_written_from_another_module() {
    let fixture = Project2::new(&[
        (
            "geom",
            "pub type Mixed { pub open: i32, secret: i32 } \
             pub fn make() -> Mixed { Mixed { open: 1, secret: 2 } }",
        ),
        (
            "main",
            "use geom::Mixed; use geom::make; \
             fn main() -> i32 { var m := make(); m.open = 5; m.secret = 6; m.open + 0 }",
        ),
    ]);
    let found = fixture.errors();
    let privacy: Vec<_> = found
        .iter()
        .filter(|d| d.code.to_string() == "TE025")
        .collect();
    assert_eq!(privacy.len(), 1, "{found:?}");
    assert!(privacy[0].message.contains("field 'secret'"), "{found:?}");
}

#[test]
fn whole_struct_moves_and_assignments() {
    accepted(&main_body(
        "let p := P { x: 1, y: 2 }; let q := p; q.x + 0;",
    ));
    accepted(&main_body(
        "var p := P { x: 1, y: 2 }; var q := P { x: 3, y: 4 }; q = p; p = P { x: 5, y: 6 }; p.x + q.x;",
    ));
    owned_rejected(
        &main_body("let p := P { x: 1, y: 2 }; let q := p; p.x + 0;"),
        "BE001",
    );
    owned_rejected(
        &main_body("var p := P { x: 1, y: 2 }; var q := P { x: 3, y: 4 }; q = p; q.x + p.x;"),
        "BE001",
    );
    // A moved `var` struct is usable again once reassigned.
    accepted(&main_body(
        "var p := P { x: 1, y: 2 }; let q := p; p = make(); p.x + q.x;",
    ));
    // Moving a struct into an owned argument, binding or struct result.
    owned_rejected(&main_body("let p := make(); own(p); own(p);"), "BE001");
    owned_rejected(
        &main_body("let p := make(); let q := pass(p); p.x + 0;"),
        "BE001",
    );
    // Assignment of a mismatched struct type.
    rejected(
        "type P { x: i32 } type Q { x: i32 } fn main() { var p := P { x: 1 }; p = Q { x: 1 }; }",
        "TE002",
        "expected P, found Q",
    );
    // A whole struct is not a statement, operand or condition.
    for source in [
        "let p := P { x: 1, y: 2 }; p;",
        "let p := P { x: 1, y: 2 }; let a := p + 1;",
    ] {
        analysis_errors(&main_body(source));
    }
    rejected(
        &main_body("let p := P { x: 1, y: 2 }; p;"),
        "TE017",
        "whole arrays and structs",
    );
}

#[test]
fn struct_values_in_if_and_block_results() {
    accepted(&main_body(
        "let c := true; let p := if c { P { x: 1, y: 2 } } else { P { x: 3, y: 4 } }; p.x + 0;",
    ));
    accepted(&main_body(
        "let a := P { x: 1, y: 2 }; let c := true; let p := if c { a } else { make() }; p.x + 0;",
    ));
    // A named struct moved on one branch is unavailable after the `if`.
    owned_rejected(
        &main_body(
            "let a := P { x: 1, y: 2 }; let c := true; let p := if c { a } else { make() }; a.x + 0;",
        ),
        "BE001",
    );
    accepted(&main_body("let p := { P { x: 1, y: 2 } }; p.x + 0;"));
    rejected(
        &main_body("let p := if true { P { x: 1, y: 2 } } else { 4 };"),
        "TE013",
        "incompatible",
    );
}

#[test]
fn struct_parameters_follow_the_array_access_rules() {
    accepted(&main_body("let p := make(); own(p);"));
    owned_rejected(&main_body("let p := make(); own(p); p.x + 0;"), "BE001");
    accepted(&main_body(
        "let p := make(); read(p.borrow()); read(p.borrow());",
    ));
    accepted(&main_body(
        "var p := make(); bump(p.share()); bump(p.share());",
    ));
    // A literal or a call result is a valid owned argument.
    accepted(&main_body("own(P { x: 1, y: 2 }); own(make());"));
    // The signature decides access: a bare struct for a reference parameter,
    // and a share conversion of a `let` owner, are rejected.
    rejected(
        &main_body("let p := make(); read(p);"),
        "TE017",
        "use an explicit .borrow() or .share()",
    );
    rejected(
        &main_body("let p := make(); bump(p.share());"),
        "TE017",
        "share conversion requires a mutable local owner",
    );
    rejected(
        &main_body("var p := make(); bump(p.borrow());"),
        "TE017",
        "does not match the share parameter access",
    );
    rejected(
        &main_body("var p := make(); own(p.borrow());"),
        "TE017",
        "reference values cannot escape",
    );
    // The wrong struct type for a parameter.
    rejected(
        "type Q { x: i32 } type P { x: i32 } fn f(p: borrow P) {} \
         fn main() { let q := Q { x: 1 }; f(q.borrow()); }",
        "TE002",
        "expected borrow P, found borrow Q",
    );
    // `var` on a reference parameter stays gated.
    rejected(
        &format!("{P} fn f(var p: share P) {{}} fn main() {{}}"),
        "TE017",
        "cannot be rebound",
    );
    // Field reads work through references and reborrows are accepted.
    accepted(
        "type P { x: i32, y: i32 } fn inner(p: borrow P) -> i32 { p.x + 0 } \
         fn outer(p: borrow P) -> i32 { inner(p.borrow()) + p.y } \
         fn deep(p: share P) -> i32 { bump2(p.share()); outer(p.borrow()) } \
         fn bump2(p: share P) { p.y += 1; } \
         fn main() {}",
    );
    // Local reference bindings.
    accepted(&main_body(
        "var p := make(); let r := p.borrow(); r.x + 0; var s := p.share(); s.y = 4; s.x + 0;",
    ));
}

#[test]
fn struct_results_are_owned_values() {
    accepted(&main_body("let p := make(); let q := pass(p); q.y + 0;"));
    accepted(&main_body("var p := make(); p = pass(make()); p.x + 0;"));
    accepted(
        "type P { x: i32 } fn make(n: i32) -> P { let p := P { x: n }; p } \
         fn early(n: i32) -> P { if n > 0 { return P { x: n }; } P { x: 0 } } \
         fn main() { let a := make(1); let b := early(2); a.x + b.x; }",
    );
    // The result type is checked against the tail.
    rejected(
        "type P { x: i32 } fn f() -> P { 1 } fn main() {}",
        "TE002",
        "expected P, found i32",
    );
    rejected(
        "type P { x: i32 } fn f() -> i32 { P { x: 1 } } fn main() {}",
        "TE002",
        "expected i32, found P",
    );
    // A borrowed parameter cannot be returned as an owned struct.
    rejected(
        "type P { x: i32 } fn f(p: borrow P) -> P { p } fn main() {}",
        "TE017",
        "cannot escape",
    );
    // Returning a moved-out local is a use after move.
    owned_rejected(
        "type P { x: i32 } fn f() -> P { let p := P { x: 1 }; let q := p; p } fn main() {}",
        "BE001",
    );
}

#[test]
fn field_reads_on_call_results_stay_gated() {
    rejected(
        &main_body("let x := make().x;"),
        "TE017",
        "named local structs and projections of them only",
    );
    rejected(
        &main_body("let x := P { x: 1, y: 2 }.x;"),
        "TE017",
        "named local structs and projections of them only",
    );
}

#[test]
fn field_borrows_and_struct_copies_stay_gated() {
    rejected(
        &main_body("var p := make(); let r := p.x.share();"),
        "TE017",
        "struct field",
    );
    rejected(
        &main_body("let p := make(); let r := p.x.borrow();"),
        "TE017",
        "struct field",
    );
    rejected(
        &main_body("let p := make(); let q := p.copy();"),
        "TE017",
        "copy is currently available only for primitive values",
    );
    accepted(&main_body("let a := [make()];"));
}

#[test]
fn field_write_while_borrowed_and_double_shares_conflict() {
    owned_rejected(
        &main_body("var p := make(); let r := p.borrow(); p.x = 3; r.x + 0;"),
        "BE005",
    );
    owned_rejected(
        &main_body("var p := make(); var r := p.share(); p.x = 3; r.x = 1;"),
        "BE005",
    );
    owned_rejected(
        &main_body("var p := make(); two(p.share(), p.share());"),
        "BE005",
    );
    owned_rejected(
        &main_body("var p := make(); mixed(p.share(), p.borrow());"),
        "BE005",
    );
    accepted(&main_body("var p := make(); both(p.borrow(), p.borrow());"));
    // Once the reference is dead the write is fine.
    accepted(&main_body(
        "var p := make(); let r := p.borrow(); r.x + 0; p.x = 3;",
    ));
    // Whole-struct assignment conflicts with a live borrow too.
    owned_rejected(
        &main_body("var p := make(); let r := p.borrow(); p = make(); r.x + 0;"),
        "BE005",
    );
}

#[test]
fn a_right_hand_side_that_mutates_the_struct_is_ordered_not_rejected() {
    // The share borrow of `p` ends with the call, before the field address is
    // formed, so the store is well defined: the call runs first, then the write.
    accepted(
        "type P { x: i32 } fn bump(p: share P) -> i32 { p.x += 1; p.x + 0 } \
         fn main() { var p := P { x: 0 }; p.x = bump(p.share()); }",
    );
    // A compound write reads the old value first, so it uses the value from
    // before the call: this is also accepted.
    accepted(
        "type P { x: i32 } fn bump(p: share P) -> i32 { p.x += 1; p.x + 0 } \
         fn main() { var p := P { x: 0 }; p.x += bump(p.share()); }",
    );
    // A live reference held across the write still conflicts.
    owned_rejected(
        "type P { x: i32 } fn id(p: borrow P) -> i32 { p.x + 0 } \
         fn main() { var p := P { x: 0 }; let r := p.borrow(); p.x = id(r.borrow()); r.x + 0; }",
        "BE005",
    );
}

#[test]
fn moving_a_struct_while_borrowed_is_rejected() {
    owned_rejected(
        &main_body("var p := make(); let r := p.borrow(); own(p); r.x + 0;"),
        "BE005",
    );
}

#[test]
fn struct_parameter_and_result_ir_shapes() {
    let program = lower(&format!(
        "{P} fn f(a: P, b: borrow P, c: share P) -> P {{ a }} fn main() {{}}"
    ));
    let signature = &program.functions[0].signature;
    assert_eq!(signature.parameters[0].ty, Type::Struct(TypeId(0)));
    assert_eq!(signature.parameters[1].access, Access::Borrow);
    assert_eq!(signature.parameters[2].access, Access::Share);
    assert_eq!(signature.result.as_ref(), &Type::Struct(TypeId(0)));
    // A struct-typed branch join carries a struct block parameter.
    let program = lower(&main_body(
        "let c := true; let p := if c { make() } else { make() }; p.x + 0;",
    ));
    let main = program.functions.last().unwrap();
    assert!(main.blocks.iter().any(|b| b
        .parameters
        .iter()
        .any(|v| main.values[v.0 as usize] == Type::Struct(TypeId(0)))));
}

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Project2(std::path::PathBuf);

impl Project2 {
    fn new(files: &[(&str, &str)]) -> Self {
        let root = std::env::temp_dir().join(format!(
            "mb-struct-mut-{}-{}",
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
