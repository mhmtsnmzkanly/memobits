use memobits_analysis::{check_resolved_types, lower_resolved};
use memobits_ir::{FunctionId, InstructionKind, Source};
use memobits_project::Project;
use memobits_resolve::{resolve, Target};
use std::{
    fs,
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Fixture(std::path::PathBuf);

impl Fixture {
    fn new(manifest_tail: &str, main: &str, math: &str, other: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "mb-resolved-types-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(root.join("src")).unwrap();
        fs::write(
            root.join("project.toml"),
            format!("[package]\nname='test'\nentry='main::main'\n{manifest_tail}"),
        )
        .unwrap();
        fs::write(root.join("src/main.mb"), main).unwrap();
        fs::write(root.join("src/math.mb"), math).unwrap();
        fs::write(root.join("src/other.mb"), other).unwrap();
        Self(root)
    }

    fn check(&self) -> Vec<memobits_diagnostics::Diagnostic> {
        let project = Project::load(&self.0, None).unwrap();
        let resolution = resolve(&project, Target::Application);
        assert!(
            resolution.diagnostics.is_empty(),
            "{:?}",
            resolution.diagnostics
        );
        check_resolved_types(&project, &resolution)
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn imports_prelude_qualified_paths_and_module_identity() {
    let f = Fixture::new(
        "[prelude]\nother_add='other::add'\n",
        "use self::math::add as math_add; fn main() -> i32 { math_add(2, 3) + other_add(true) + self::math::add(4, 5) }",
        "pub fn add(a: i32, b: i32) -> i32 { a + b }",
        "pub fn add(a: Bool) -> i32 { if a { 1 } else { 0 } }",
    );
    assert!(f.check().is_empty(), "{:?}", f.check());
}

#[test]
fn local_shadowing_keeps_lexical_binding() {
    let f = Fixture::new(
        "",
        "use math::add as call; fn main() -> i32 { let call := 1; call }",
        "pub fn add(a: i32) -> i32 { a }",
        "pub fn add(a: Bool) -> Bool { a }",
    );
    assert!(f.check().is_empty());
}

#[test]
fn imported_argument_error_uses_call_site_source_span() {
    let source = "use math::add; fn main() -> i32 { add(false) }";
    let f = Fixture::new(
        "",
        source,
        "pub fn add(a: i32) -> i32 { a }",
        "pub fn add(a: Bool) -> Bool { a }",
    );
    let project = Project::load(&f.0, None).unwrap();
    let resolution = resolve(&project, Target::Application);
    assert!(
        resolution.diagnostics.is_empty(),
        "{:?}",
        resolution.diagnostics
    );
    let diagnostics = check_resolved_types(&project, &resolution);
    let mismatch = diagnostics
        .iter()
        .find(|d| d.code.to_string() == "TE002")
        .unwrap();
    let span = mismatch.span.unwrap();
    assert_eq!(span.source, resolution.modules["main"].id);
    assert_eq!(span.start as usize, source.find("false").unwrap());
}

#[test]
fn invalid_resolution_skips_type_pass() {
    let f = Fixture::new("", "use math::missing; fn main() {}", "", "");
    let project = Project::load(&f.0, None).unwrap();
    let resolution = resolve(&project, Target::Application);
    assert!(!resolution.diagnostics.is_empty());
    assert!(check_resolved_types(&project, &resolution).is_empty());
}

#[test]
fn lower_resolved_preserves_canonical_function_identity_for_aliases() {
    let f = Fixture::new(
        "[prelude]\nother_add='other::add'\n",
        "use self::math::add as math_add; fn main() -> i32 { math_add(2, 3) + other_add(true) + self::math::add(4, 5) }",
        "pub fn add(a: i32, b: i32) -> i32 { a + b }",
        "pub fn add(a: Bool) -> i32 { if a { 1 } else { 0 } }",
    );
    let project = Project::load(&f.0, None).unwrap();
    let resolution = resolve(&project, Target::Application);
    let program = lower_resolved(&project, &resolution).unwrap();
    assert_eq!(program.functions.len(), 3);
    assert_eq!(
        program
            .functions
            .iter()
            .map(|function| function.path.module.join("::"))
            .collect::<Vec<_>>(),
        vec!["main", "math", "other"]
    );
    let calls = program.functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| {
            if let InstructionKind::Call { callee, .. } = &instruction.kind {
                Some(callee.source)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(
        calls,
        vec![
            Source::Function(FunctionId(1)),
            Source::Function(FunctionId(2)),
            Source::Function(FunctionId(1))
        ]
    );
    assert!(program.validate().is_ok());
}

#[test]
fn generic_specializations_keep_inline_enum_payload_types_distinct() {
    let f = Fixture::new(
        "",
        r#"
        fn wrap<T>(value: T) -> u32 {
            let wrapped: enum [Item(T), Empty] = Item(value);
            match wrapped { Item(_) => 42, Empty => 0 }
        }
        fn main() -> u32 { wrap(1) + wrap(true) }
        "#,
        "",
        "",
    );
    let project = Project::load(&f.0, None).unwrap();
    let resolution = resolve(&project, Target::Application);
    assert!(
        resolution.diagnostics.is_empty(),
        "{:?}",
        resolution.diagnostics
    );

    let program = lower_resolved(&project, &resolution)
        .unwrap_or_else(|diagnostics| panic!("{diagnostics:?}"));
    program.validate().unwrap();
    let specialized: Vec<_> = program
        .types
        .iter()
        .filter_map(|definition| {
            if definition.path.module.as_slice() != ["\0anonymous-enum"] {
                return None;
            }
            let memobits_ir::TypeDefKind::Enum { variants } = &definition.kind else {
                return None;
            };
            (variants
                .first()
                .is_some_and(|variant| variant.name == "Item"))
            .then(|| variants[0].payload[0].clone())
        })
        .collect();
    assert_eq!(specialized.len(), 2, "{specialized:?}");
    assert!(specialized.contains(&memobits_ir::Type::Primitive(memobits_ir::Primitive::I32)));
    assert!(specialized.contains(&memobits_ir::Type::Primitive(memobits_ir::Primitive::Bool)));
}

#[test]
fn lower_resolved_ownership_tracks_moves_across_modules() {
    let f = Fixture::new(
        "",
        "use math::take; fn main() { let x := [1]; take(x); x[0] + 1; }",
        "pub fn take(value: Array<i32, 1>) {}",
        "",
    );
    let project = Project::load(&f.0, None).unwrap();
    let resolution = resolve(&project, Target::Application);
    let program = lower_resolved(&project, &resolution).unwrap();
    let diagnostics = memobits_ownership::check_moves(&program);
    assert!(diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code.to_string() == "BE001"));
}

#[test]
fn library_lowering_has_only_export_roots_and_invalid_graph_returns_errors() {
    let f = Fixture::new(
        "[export]\napi='math::api'\n",
        "fn main() {}",
        "pub fn api() {}",
        "",
    );
    let project = Project::load(&f.0, None).unwrap();
    let resolution = resolve(&project, Target::Library);
    let program = lower_resolved(&project, &resolution).unwrap();
    assert_eq!(program.functions.len(), 1);
    assert_eq!(program.functions[0].path.module, vec!["math"]);
    assert_eq!(program.functions[0].path.name, "api");

    let invalid = Fixture::new("", "use math::missing; fn main() {}", "", "");
    let project = Project::load(&invalid.0, None).unwrap();
    let resolution = resolve(&project, Target::Application);
    let errors = lower_resolved(&project, &resolution).unwrap_err();
    assert!(!errors.is_empty());
    assert_eq!(
        errors[0].code.to_string(),
        resolution.diagnostics[0].code.to_string()
    );

    let invalid_types = Fixture::new("", "fn main() { break; }", "", "");
    let project = Project::load(&invalid_types.0, None).unwrap();
    let resolution = resolve(&project, Target::Application);
    let errors = lower_resolved(&project, &resolution).unwrap_err();
    assert!(errors
        .iter()
        .any(|diagnostic| diagnostic.code.to_string() == "TE020"));

    let static_error = Fixture::new(
        "",
        "use math::value; fn main() -> i32 { value() + 1 }",
        "pub fn value() -> i32 { 2147483647 + 1 }",
        "",
    );
    let project = Project::load(&static_error.0, None).unwrap();
    let resolution = resolve(&project, Target::Application);
    let errors = lower_resolved(&project, &resolution).unwrap_err();
    assert!(errors
        .iter()
        .any(|diagnostic| diagnostic.code.to_string() == "LE001"));
}

#[test]
fn arrays_check_types_but_unsupported_forms_cannot_lower_in_resolved_modules() {
    for main in ["fn main() { [1, 2]; }", "fn main() { let a := [1, 2]; a; }"] {
        let fixture = Fixture::new("", main, "", "");
        assert!(fixture.check().is_empty(), "{:?}", fixture.check());
        let project = Project::load(&fixture.0, None).unwrap();
        let resolution = resolve(&project, Target::Application);
        let diagnostics = lower_resolved(&project, &resolution).unwrap_err();
        assert!(diagnostics.iter().any(|d| d.code.to_string() == "TE017"));
    }
}

#[test]
fn nested_arrays_and_array_results_lower_in_resolved_modules() {
    for main in [
        "fn main() { let a: Array<Array<i8, 1>, 2> = [[1], [2]]; }",
        "fn main() {} fn values(a: Array<i32, 2>) -> Array<i32, 2> { [1, 2] }",
    ] {
        let fixture = Fixture::new("", main, "", "");
        assert!(fixture.check().is_empty(), "{:?}", fixture.check());
        let project = Project::load(&fixture.0, None).unwrap();
        let resolution = resolve(&project, Target::Application);
        let program = lower_resolved(&project, &resolution).unwrap();
        assert!(program.validate().is_ok());
    }
}

#[test]
fn let_arrays_with_indexing_lower_in_resolved_modules() {
    let fixture = Fixture::new(
        "",
        "fn main() -> i32 { let a: Array<i32, 2> = [1, 2]; a[1] + a[0] }",
        "",
        "",
    );
    let project = Project::load(&fixture.0, None).unwrap();
    let resolution = resolve(&project, Target::Application);
    let program = lower_resolved(&project, &resolution).unwrap();
    assert!(program.functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .any(|instruction| matches!(instruction.kind, InstructionKind::ElementAddr { .. })));
}
