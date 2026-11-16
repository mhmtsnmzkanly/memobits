//! Arrays across internal calls: owned, `borrow` and `share` array parameters,
//! element access through references and the forms that stay gated.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_ir::{Access, InstructionKind, Primitive, Program, Type, UseMode};
use memobits_syntax::parse;

fn try_lower(source: &str) -> Result<Program, Vec<String>> {
    let parsed = parse(SourceId(31), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    lower_module(&parsed.module, "test", &["main".into()]).map_err(|errors| {
        errors
            .iter()
            .map(|diagnostic| diagnostic.code.to_string())
            .collect()
    })
}

fn lower(source: &str) -> Program {
    let program = try_lower(source).unwrap_or_else(|codes| panic!("{source}: {codes:?}"));
    program.validate().unwrap();
    program
}

fn codes(source: &str) -> Vec<String> {
    try_lower(source).expect_err(source)
}

fn array(len: u32) -> Type {
    Type::Array {
        element: Box::new(Type::Primitive(Primitive::I32)),
        len,
    }
}

#[test]
fn array_parameters_have_access_specific_local_types() {
    let program =
        lower("fn f(a: Array<i32, 3>, b: borrow Array<i32, 3>, c: share Array<i32, 3>) {}");
    let function = &program.functions[0];
    assert_eq!(function.locals[0].ty, array(3));
    assert_eq!(
        function.locals[1].ty,
        Type::Reference {
            access: Access::Borrow,
            inner: Box::new(array(3))
        }
    );
    assert_eq!(
        function.locals[2].ty,
        Type::Reference {
            access: Access::Share,
            inner: Box::new(array(3))
        }
    );
    assert_eq!(function.signature.parameters[1].ty, array(3));
}

#[test]
fn array_call_arguments_use_the_parameter_access_mode() {
    let program = lower(
        "fn f(a: Array<i32, 2>, b: borrow Array<i32, 2>, c: share Array<i32, 2>) {} \
         fn main() { var x := [1, 2]; var y := [3, 4]; var z := [5, 6]; f(x, y.borrow(), z.share()); }",
    );
    let call = program.functions[1]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .find_map(|instruction| match &instruction.kind {
            InstructionKind::Call { arguments, .. } => Some(arguments),
            _ => None,
        })
        .unwrap();
    let modes = call
        .iter()
        .map(|argument| argument.mode)
        .collect::<Vec<_>>();
    assert_eq!(modes, [UseMode::Consume, UseMode::Borrow, UseMode::Share]);
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn element_reads_and_writes_through_references_lower() {
    let program = lower(
        "fn f(a: borrow Array<i32, 3>, b: share Array<i32, 3>, i: i32) -> i32 { \
         b[0] = a[1] + 1; b[1] += b[2]; b[i + 0] = 5; a[2] + b[0] }",
    );
    let kinds = program.functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .map(|instruction| &instruction.kind)
        .collect::<Vec<_>>();
    // Reads (and the read half of a compound write) are Borrow addresses;
    // each write is a Share address followed by a Store.
    let shares = kinds
        .iter()
        .filter(|kind| {
            matches!(
                kind,
                InstructionKind::ElementAddr {
                    access: Access::Share,
                    ..
                }
            )
        })
        .count();
    assert_eq!(shares, 3);
    assert!(memobits_ownership::check_ownership(&program).is_empty());
}

#[test]
fn local_array_references_and_reborrows_lower() {
    lower("fn main() -> i32 { var a := [1, 2, 3]; let r := a.borrow(); r[0] + r[2] }");
    lower("fn main() { var a := [1, 2, 3]; var r := a.share(); r[0] = 4; r[1] += 1; }");
    lower("fn main() { var a := [1, 2]; let r := a.borrow(); let q := r; q[0] + 0; }");
    lower(
        "fn read(a: borrow Array<i32, 2>) -> i32 { a[0] + 0 } \
         fn pass(a: borrow Array<i32, 2>) -> i32 { read(a) + read(a) } \
         fn mutate(a: share Array<i32, 2>) { a[0] = 1; } \
         fn forward(a: share Array<i32, 2>) { mutate(a); a[1] = 2; } \
         fn lend(a: share Array<i32, 2>) -> i32 { read(a.borrow()) }",
    );
    // A whole-array store through a share reference.
    lower("fn put(a: share Array<i32, 2>) { a = [1, 2]; }");
}

#[test]
fn owned_array_arguments_accept_literals_repetitions_and_locals() {
    lower(
        "fn f(a: Array<i32, 2>) -> i32 { a[0] + a[1] } \
         fn main() -> i32 { let x := [1, 2]; f(x) + f([3, 4]) + f([5; 2]) }",
    );
    lower("fn f(var a: Array<i32, 2>) -> i32 { a[0] = 9; a[0] + 0 }");
}

#[test]
fn array_type_mismatches_between_argument_and_parameter_are_type_errors() {
    assert!(codes("fn f(a: Array<i32, 3>) {} fn main() { f([1, 2]); }").contains(&"TE002".into()));
    assert!(
        codes("fn f(a: Array<i32, 2>) {} fn main() { f([true, false]); }")
            .contains(&"TE002".into())
    );
    assert!(codes(
        "fn f(a: borrow Array<i32, 3>) {} fn main() { let x := [1, 2]; f(x.borrow()); }"
    )
    .contains(&"TE002".into()));
    assert!(
        codes("fn f(a: share Array<i64, 2>) {} fn main() { var x := [1, 2]; f(x.share()); }")
            .contains(&"TE002".into())
    );
    assert!(codes("fn f(a: Array<i32, 2>) {} fn main() { f(1); }").contains(&"TE002".into()));
}

#[test]
fn references_follow_the_signature_access_without_call_site_overrides() {
    // Arrays are not implicitly borrowed or shared; the explicit conversion is
    // required exactly as for primitives.
    assert!(
        codes("fn f(a: borrow Array<i32, 2>) {} fn main() { let x := [1, 2]; f(x); }")
            .contains(&"TE017".into())
    );
    assert!(
        codes("fn f(a: share Array<i32, 2>) {} fn main() { let x := [1, 2]; f(x.borrow()); }")
            .contains(&"TE017".into())
    );
    assert!(
        codes("fn f(a: share Array<i32, 2>) {} fn main() { let x := [1, 2]; f(x.share()); }")
            .contains(&"TE017".into())
    );
    assert!(
        codes("fn f(a: share Array<i32, 2>) {} fn g(a: borrow Array<i32, 2>) { f(a); }")
            .contains(&"TE017".into())
    );
    // A reference cannot become an owned argument.
    assert!(
        codes("fn f(a: Array<i32, 2>) {} fn g(a: borrow Array<i32, 2>) { f(a); }")
            .contains(&"TE017".into())
    );
}

#[test]
fn writes_require_a_mutable_path() {
    for source in [
        "fn f(a: borrow Array<i32, 2>) { a[0] = 1; }",
        "fn f(a: borrow Array<i32, 2>) { a[0] += 1; }",
        "fn f(a: Array<i32, 2>) { a[0] = 1; }",
        "fn main() { var x := [1, 2]; let r := x.share(); r[0] = 1; }",
        "fn main() { var x := [1, 2]; let r := x.borrow(); r[0] = 1; }",
    ] {
        assert!(codes(source).contains(&"TE004".into()), "{source}");
    }
    assert!(codes("fn main() { let x := [1, 2]; let r := x.share(); }").contains(&"TE017".into()));
    // `var` is rejected on reference parameters, as for primitives.
    assert!(codes("fn f(var a: borrow Array<i32, 2>) {}").contains(&"TE017".into()));
}

#[test]
fn constant_indices_are_checked_through_references() {
    for source in [
        "fn f(a: borrow Array<i32, 3>) -> i32 { a[3] + 0 }",
        "fn f(a: share Array<i32, 3>) { a[3] = 1; }",
        "fn f(a: share Array<i32, 3>) { a[-1] += 1; }",
    ] {
        assert!(codes(source).contains(&"TE008".into()), "{source}");
    }
    lower("fn f(a: borrow Array<i32, 3>) -> i32 { a[2] + 0 }");
}

#[test]
fn element_extraction_through_references_stays_rejected() {
    for source in [
        "fn f(a: borrow Array<i32, 2>) { let x := a[0]; }",
        "fn f(a: borrow Array<i32, 2>) -> i32 { a[0] }",
        "fn f(a: share Array<i32, 2>) { a[1] = a[0]; }",
        "fn g(x: i32) {} fn f(a: borrow Array<i32, 2>) { g(a[0]); }",
    ] {
        assert!(codes(source).contains(&"TE022".into()), "{source}");
    }
}

#[test]
fn unsupported_array_call_forms_report_gate_diagnostics() {
    for source in [
        // references to primitive elements
        "fn f(a: share Array<i32, 2>) { let r := a[0].share(); }",
        "fn g(x: share i32) {} fn f(a: share Array<i32, 2>) { g(a[0].share()); }",
        // temporaries cannot be borrowed
        "fn g(a: borrow Array<i32, 2>) {} fn f() { g([1, 2].borrow()); }",
        // array references are not values
        "fn f(a: borrow Array<i32, 2>) -> i32 { a }",
        "fn f(a: borrow Array<i32, 2>) { let b := if true { a } else { a }; }",
        "fn f(a: borrow Array<i32, 2>) { [a]; }",
        // rebinding a reference handle
        "fn f(a: share Array<i32, 2>, b: share Array<i32, 2>) { var r := a.share(); r = b; }",
    ] {
        assert!(codes(source).contains(&"TE017".into()), "{source}");
    }
}
