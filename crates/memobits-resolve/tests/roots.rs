use memobits_project::Project;
use memobits_resolve::{resolve, Target};
use std::{
    fs,
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Fixture(std::path::PathBuf);
impl Fixture {
    fn new(math: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "mb-resolve-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            "[package]\nname='test'\nentry='main::main'\n[export]\nadd='math::add'\n",
        )
        .unwrap();
        fs::write(
            path.join("src/main.mb"),
            "use self::math::add; fn main() -> i32 { add(1, 2) }",
        )
        .unwrap();
        fs::write(path.join("src/math.mb"), math).unwrap();
        fs::write(path.join("src/unreachable.mb"), "not valid source").unwrap();
        Self(path)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn library_and_application_load_different_roots() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    let project = Project::load(&f.0, None).unwrap();
    let app = resolve(&project, Target::Application);
    assert!(app.diagnostics.is_empty(), "{:?}", app.diagnostics);
    assert_eq!(
        app.modules.keys().map(String::as_str).collect::<Vec<_>>(),
        ["main", "math"]
    );
    let lib = resolve(&project, Target::Library);
    assert!(lib.diagnostics.is_empty());
    assert_eq!(
        lib.modules.keys().map(String::as_str).collect::<Vec<_>>(),
        ["math"]
    );
}

#[test]
fn compiler_owned_core_module_path_cannot_be_redeclared() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    fs::create_dir_all(f.0.join("src/core")).unwrap();
    fs::write(f.0.join("src/core/ops.mb"), "pub interface Add {}").unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic.message.contains("core::ops") && diagnostic.message.contains("reserved")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn bare_module_import_is_a_direct_extension_edge_not_a_symbol_alias() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    fs::write(
        f.0.join("src/main.mb"),
        "use math; fn main() -> i32 { math::add(1, 2) }",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let resolution = resolve(&project, Target::Application);
    assert!(
        resolution.diagnostics.is_empty(),
        "{:?}",
        resolution.diagnostics
    );
    assert_eq!(
        resolution
            .module_imports
            .get("main")
            .unwrap()
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        ["math"]
    );
}

#[test]
fn symbol_import_loads_a_module_without_activating_it_as_an_extension_edge() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    let project = Project::load(&f.0, None).unwrap();
    let resolution = resolve(&project, Target::Application);
    assert!(
        resolution.diagnostics.is_empty(),
        "{:?}",
        resolution.diagnostics
    );
    assert!(!resolution.module_imports.contains_key("main"));
}

#[test]
fn interface_signatures_extension_types_and_bodies_participate_in_resolution() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    fs::write(
        f.0.join("src/main.mb"),
        "type Point { x: i32 }\ninterface Draw { fn draw(borrow self) -> i32; }\nextend Point of Draw { fn draw(borrow self) -> i32 { self.x } }\nfn main() -> i32 { let point := Point { x: 42 }; point.draw() of Draw }",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
}

#[test]
fn unknown_types_in_extensions_are_resolver_errors() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    fs::write(
        f.0.join("src/main.mb"),
        "interface Draw { fn draw(borrow self) -> Missing; }",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code.to_string() == "NE003"),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn local_extensions_must_match_interface_method_signatures() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    fs::write(
        f.0.join("src/main.mb"),
        "type Point { x: i32 }\ninterface Draw { fn draw(borrow self, scale: i32) -> i32; }\nextend Point of Draw { fn draw(borrow self) -> u32 { 0u32 } }",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("does not match interface 'main::Draw'")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn extension_conformance_resolves_qualified_and_imported_interfaces_and_parameter_access() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    fs::write(
        f.0.join("src/main.mb"),
        "use graphics; pub type Point { pub x: i32 }\npub interface Draw { fn draw(borrow self, input: borrow Point) -> i32; }\nfn main() -> i32 { 0 }",
    )
    .unwrap();
    fs::write(
        f.0.join("src/graphics.mb"),
        "use self::main::Point; use self::main::Draw; extend Point of Draw { fn draw(borrow self, input: share Point) -> i32 { self.x } }",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("does not match interface 'main::Draw'")),
        "{:?}",
        result.diagnostics
    );

    fs::write(
        f.0.join("src/graphics.mb"),
        "use self::main::Point; extend Point of main::Draw { fn draw(borrow self, input: share main::Point) -> i32 { self.x } }",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("does not match interface 'main::Draw'")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn extension_conformance_checks_receiver_mode_and_parameter_mutability() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    for (interface, implementation) in [
        (
            "pub interface Draw { fn draw(self) -> i32; }",
            "extend Point of Draw { fn draw(borrow self) -> i32 { self.x } }",
        ),
        (
            "pub interface Draw { fn draw(borrow self, var amount: i32) -> i32; }",
            "extend Point of Draw { fn draw(borrow self, amount: i32) -> i32 { self.x } }",
        ),
    ] {
        fs::write(
            f.0.join("src/main.mb"),
            format!("use graphics; pub type Point {{ pub x: i32 }}\n{interface}\nfn main() -> i32 {{ 0 }}"),
        )
        .unwrap();
        fs::write(
            f.0.join("src/graphics.mb"),
            format!("use self::main::Point; use self::main::Draw; {implementation}"),
        )
        .unwrap();
        let project = Project::load(&f.0, None).unwrap();
        let result = resolve(&project, Target::Application);
        assert!(
            result.diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("does not match interface 'main::Draw'")),
            "{:?}",
            result.diagnostics
        );
    }
}

#[test]
fn associated_type_bindings_are_required_and_substitute_method_signatures() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    fs::write(
        f.0.join("src/main.mb"),
        "type Left { value: i32 } type Right { value: i32 } type Result { value: i32 } interface Add { type Rhs; type Output; fn add(self, rhs: Rhs) -> Output; } extend Left of Add { type Rhs = Right; type Output = Result; fn add(self, rhs: Right) -> Result { Result { value: self.value + rhs.value } } } fn main() {}",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

    fs::write(
        f.0.join("src/main.mb"),
        "type Left { value: i32 } type Right { value: i32 } type Result { value: i32 } interface Add { type Rhs; type Output; fn add(self, rhs: Rhs) -> Output; } extend Left of Add { type Rhs = Right; fn add(self, rhs: Left) -> Result { Result { value: self.value } } } fn main() {}",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("missing associated type binding 'Output'")),
        "{:?}",
        result.diagnostics
    );
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("does not match interface 'main::Add'")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn extension_constraint_rejects_a_nominal_type_instead_of_an_interface() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    fs::write(
        f.0.join("src/main.mb"),
        "type Point { x: i32 }\ntype NotInterface { x: i32 }\nextend Point of NotInterface { fn draw(borrow self) -> i32 { self.x } }\nfn main() {}",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("is a type, not an interface")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn extension_conformance_resolves_transparent_aliases_locally_and_across_modules() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    fs::write(
        f.0.join("src/main.mb"),
        "use graphics; pub type Point { pub x: i32 } pub type Number = i32; pub interface Draw { fn draw(borrow self, amount: Number, pair: Result<Number, Number>) -> Result<Number, Number>; } extend Point of Draw { fn draw(borrow self, amount: i32, pair: Result<i32, i32>) -> Result<i32, i32> { pair } } fn main() -> i32 { 0 }",
    ).unwrap();
    fs::write(
        f.0.join("src/graphics.mb"),
        "use self::main::{Point, Draw, Number}; pub type OtherNumber = Number; extend Point of Draw { fn draw(borrow self, amount: OtherNumber, pair: Result<OtherNumber, OtherNumber>) -> Result<Number, OtherNumber> { pair } }",
    ).unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("does not match interface")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn extension_conformance_uses_lowercase_string_across_modules() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    fs::write(
        f.0.join("src/main.mb"),
        "use graphics; pub type Point { pub x: i32 } pub interface Text { fn echo(borrow self, input: string) -> string; } fn main() -> i32 { 0 }",
    )
    .unwrap();
    fs::write(
        f.0.join("src/graphics.mb"),
        "use self::main::{Point, Text}; extend Point of Text { fn echo(borrow self, input: string) -> string { input } }",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
}

#[test]
fn extension_constraint_rejects_primitives_and_templates_as_interfaces() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    for constraint in ["i32", "List<i32>", "string"] {
        fs::write(
            f.0.join("src/main.mb"),
            format!("type Point {{ x: i32 }} extend Point of {constraint} {{ fn draw(borrow self) -> i32 {{ self.x }} }} fn main() {{}}"),
        ).unwrap();
        let project = Project::load(&f.0, None).unwrap();
        let result = resolve(&project, Target::Application);
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("not a declared interface")),
            "constraint {constraint}: {:?}",
            result.diagnostics
        );
    }
}

#[test]
fn generic_parameters_are_scoped_types_during_name_resolution() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    fs::write(
        f.0.join("src/main.mb"),
        "pub interface Draw { fn draw(borrow self) -> i32; } pub type Box<T> { value: T } pub fn identity<T>(value: T) -> T where T: Draw { value } fn main() -> i32 { 0 }",
    ).unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("unknown type 'T'")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn public_interface_cannot_expose_a_private_type() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    fs::write(
        f.0.join("src/main.mb"),
        "type Secret { value: i32 }\npub interface Reveal { fn reveal(borrow self) -> Secret; }",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("public signature exposes private type 'Secret'")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn extension_candidates_follow_direct_module_edges_and_public_visibility() {
    let f = Fixture::new(
        "pub fn add(a: i32, b: i32) -> i32 { a + b }\npub type Point { x: i32 }\npub interface Draw { fn draw(borrow self) -> i32; }\npub extend Point of Draw { fn draw(borrow self) -> i32 { 1 } }\nextend Point of Draw { fn draw(borrow self) -> i32 { 2 } }",
    );
    fs::write(
        f.0.join("src/main.mb"),
        "use math; fn main() -> i32 { math::add(1, 2) }",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    let candidates = result.extension_candidates("main");
    assert_eq!(candidates.len(), 1);
    assert_eq!(candidates[0].package, "test");
    assert_eq!(candidates[0].module, "math");
    assert!(candidates[0].public);
    let local_candidates = result.extension_candidates("math");
    assert_eq!(local_candidates.len(), 2);
    assert_ne!(local_candidates[0].span, local_candidates[1].span);

    fs::write(
        f.0.join("src/main.mb"),
        "use self::math::add; fn main() -> i32 { add(1, 2) }",
    )
    .unwrap();
    let result = resolve(&project, Target::Application);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(result.extension_candidates("main").is_empty());
    fs::write(
        f.0.join("src/main.mb"),
        "use math::{add}; fn main() -> i32 { add(1, 2) }",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(result.extension_candidates("main").is_empty());

    fs::write(
        f.0.join("src/bridge.mb"),
        "use math; pub fn via_math() -> i32 { math::add(1, 2) }",
    )
    .unwrap();
    fs::write(
        f.0.join("src/main.mb"),
        "use bridge; fn main() -> i32 { bridge::via_math() }",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(result.modules.contains_key("math"));
    assert!(result.extension_candidates("main").is_empty());

    fs::write(
        f.0.join("project.toml"),
        "[package]\nname='test'\nentry='main::main'\n[export]\nadd='math::add'\n[prelude]\nsum_add='math::add'\n",
    )
    .unwrap();
    fs::write(
        f.0.join("src/main.mb"),
        "fn main() -> i32 { sum_add(1, 2) }",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(result.modules.contains_key("math"));
    assert!(result.extension_candidates("main").is_empty());
}

#[test]
fn extension_candidate_identity_includes_independent_package_name() {
    fn candidate_for(package: &str) -> (String, String, usize, usize) {
        let f = Fixture::new(
            "pub type Point { x: i32 } pub interface Draw { fn draw(borrow self) -> i32; } pub extend Point of Draw { fn draw(borrow self) -> i32 { self.x } }",
        );
        fs::write(
            f.0.join("project.toml"),
            format!("[package]\nname='{package}'\nentry='main::main'\n"),
        )
        .unwrap();
        fs::write(
            f.0.join("src/main.mb"),
            "use model; pub type Point { x: i32 } pub interface Draw { fn draw(borrow self) -> i32; } fn main() -> i32 { 0 }",
        )
        .unwrap();
        fs::write(f.0.join("src/model.mb"), "use self::main::Point; use self::main::Draw; pub extend Point of Draw { fn draw(borrow self) -> i32 { self.x } }").unwrap();
        let project = Project::load(&f.0, None).unwrap();
        let result = resolve(&project, Target::Application);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let candidate = result.extension_candidates("main").remove(0);
        (
            candidate.package,
            candidate.module,
            candidate.span.start,
            candidate.span.end,
        )
    }

    let first = candidate_for("first-package");
    let second = candidate_for("second-package");
    assert_eq!(first.1, second.1, "fixture module paths should collide");
    assert_eq!(
        (first.2, first.3),
        (second.2, second.3),
        "fixture source spans should collide"
    );
    assert_ne!(
        first.0, second.0,
        "package identity must distinguish candidates"
    );
}

#[test]
fn missing_private_and_duplicate_definitions_are_rejected() {
    for (source, expected) in [
        ("fn add() {}", "ME007"),
        ("pub fn other() {}", "ME006"),
        ("pub fn add() {} pub fn add() {}", "ME005"),
    ] {
        let f = Fixture::new(source);
        let project = Project::load(&f.0, None).unwrap();
        for target in [Target::Application, Target::Library] {
            let result = resolve(&project, target);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|d| d.code.to_string() == expected),
                "{:?}",
                result.diagnostics
            );
        }
    }
}

#[test]
fn lexical_scopes_shadowing_and_parameters_are_checked() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    for (source, expected) in [
        ("fn main() { let x := x; }", Some("NE001")),
        ("fn main(x: i32, x: i32) {}", Some("NE002")),
        ("fn main() { { let x := 1; } x; }", Some("NE001")),
        ("fn main() { let x := 1; let x := x + 1; x; }", None),
    ] {
        fs::write(f.0.join("src/main.mb"), source).unwrap();
        let project = Project::load(&f.0, None).unwrap();
        let result = resolve(&project, Target::Application);
        if let Some(code) = expected {
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|d| d.code.to_string() == code),
                "{:?}",
                result.diagnostics
            );
        } else {
            assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        }
    }
}

#[test]
fn qualified_call_discovers_module_without_use_statement() {
    let f = Fixture::new("pub fn add(a: i32, b: i32) -> i32 { a + b }");
    fs::write(
        f.0.join("src/main.mb"),
        "fn main() -> i32 { self::math::add(1, 2) }",
    )
    .unwrap();
    let project = Project::load(&f.0, None).unwrap();
    let result = resolve(&project, Target::Application);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(result.modules.contains_key("math"));
}

#[test]
fn local_type_annotations_and_enum_variants_are_resolved() {
    let f = Fixture::new("pub fn add() {}");
    for (source, expected) in [
        ("fn main(x: Missing) {}", Some("NE003")),
        ("type X { field: Missing } fn main() {}", Some("NE003")),
        ("fn main() { let p := Missing { x: 1 }; }", Some("NE003")),
        (
            "type P { x: i32 } fn main() { let p := P { x: unknown }; }",
            Some("NE001"),
        ),
        (
            "type P { x: i32 } fn main() { let p := P { x: 1 }; let q := p.x; }",
            None,
        ),
        (
            "type State [ Idle ] fn main() { State::Missing; }",
            Some("NE004"),
        ),
        (
            "type State [ Idle ] fn main() -> State { State::Idle }",
            None,
        ),
        ("type Alias = i32; fn main(x: Alias) -> i32 { x }", None),
    ] {
        fs::write(f.0.join("src/main.mb"), source).unwrap();
        let result = resolve(&Project::load(&f.0, None).unwrap(), Target::Application);
        if let Some(code) = expected {
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|d| d.code.to_string() == code),
                "{:?}",
                result.diagnostics
            );
        } else {
            assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        }
    }
}

#[test]
fn imported_and_prelude_annotations_require_types() {
    let f = Fixture::new("pub type Number = i32; pub fn add() {}");
    for (imports, annotation, expected) in [
        ("use math::Number as N;", "N", None),
        ("use math::add as N;", "N", Some("ME008")),
        ("", "math::add", Some("ME008")),
        ("", "N", None),
    ] {
        let prelude = if imports.is_empty() && annotation == "N" {
            "[prelude]\nN='math::Number'\n"
        } else {
            ""
        };
        fs::write(
            f.0.join("project.toml"),
            format!("[package]\nname='test'\nentry='main::main'\n{prelude}"),
        )
        .unwrap();
        fs::write(
            f.0.join("src/main.mb"),
            format!("{imports} fn main(x: {annotation}) {{}}"),
        )
        .unwrap();
        let result = resolve(&Project::load(&f.0, None).unwrap(), Target::Application);
        match expected {
            Some(code) => assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|d| d.code.to_string() == code),
                "{:?}",
                result.diagnostics
            ),
            None => assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics),
        }
    }
}

#[test]
fn application_entry_cannot_be_a_type() {
    let f = Fixture::new("pub fn add() {}");
    fs::write(f.0.join("src/main.mb"), "type main = i32;").unwrap();
    let result = resolve(&Project::load(&f.0, None).unwrap(), Target::Application);
    assert!(result
        .diagnostics
        .iter()
        .any(|d| d.code.to_string() == "ME009"));
}

#[test]
fn imported_enum_variants_resolve_through_aliases_and_qualified_paths() {
    let f = Fixture::new("pub type State [ Idle, Ready(i32) ]");
    for source in [
        "use math::State as S; fn main() { S::Idle; S::Ready(1); }",
        "fn main() { self::math::State::Idle; }",
        "use math::State::Idle; fn main() { Idle; }",
    ] {
        fs::write(f.0.join("src/main.mb"), source).unwrap();
        let result = resolve(&Project::load(&f.0, None).unwrap(), Target::Application);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    }
    fs::write(
        f.0.join("src/main.mb"),
        "use math::State as S; fn main() { S::Missing; }",
    )
    .unwrap();
    let result = resolve(&Project::load(&f.0, None).unwrap(), Target::Application);
    assert!(result
        .diagnostics
        .iter()
        .any(|d| d.code.to_string() == "ME006"));
}

#[test]
fn public_signatures_cannot_expose_private_local_types() {
    let f = Fixture::new("pub fn add() {}");
    for (definition, leaks) in [
        ("pub fn api(x: Hidden) {}", true),
        ("use self::main::Hidden as H; pub fn api(x: H) {}", true),
        ("pub fn api(x: self::main::Hidden) {}", true),
        ("pub fn api(x: main::Hidden) {}", true),
        ("pub type Alias = Hidden;", true),
        ("pub type Event [ Data(Hidden) ]", true),
        ("pub type Wrapper { pub value: Hidden }", true),
        ("pub type Wrapper { value: Hidden }", false),
        ("fn internal(x: Hidden) {}", false),
    ] {
        fs::write(
            f.0.join("src/main.mb"),
            format!("type Hidden = i32; {definition} fn main() {{}}"),
        )
        .unwrap();
        let result = resolve(&Project::load(&f.0, None).unwrap(), Target::Application);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .any(|d| d.code.to_string() == "ME010"),
            leaks,
            "{:?}",
            result.diagnostics
        );
    }
}

#[test]
fn prelude_alias_cannot_hide_private_type_in_public_signature() {
    let f = Fixture::new("pub fn add() {}");
    fs::write(
        f.0.join("project.toml"),
        "[package]\nname='test'\nentry='main::main'\n[prelude]\nH='self::main::Hidden'\n",
    )
    .unwrap();
    fs::write(
        f.0.join("src/main.mb"),
        "type Hidden = i32; pub fn api(x: H) {} fn main() {}",
    )
    .unwrap();
    let result = resolve(&Project::load(&f.0, None).unwrap(), Target::Application);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|d| d.code.to_string() == "ME010"),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn imported_outcome_alias_variants_check_names_and_visibility() {
    let f = Fixture::new(
        "use inner::Read as Inner;
         pub type Maybe = Option<i32>;
         pub type Read = Inner;
         type Hidden = Attempt<i32, Error>;",
    );
    fs::write(
        f.0.join("src/inner.mb"),
        "pub type Read = Result<i32, Error>;",
    )
    .unwrap();
    for (source, expected) in [
        (
            "use math::Maybe; use math::Read as R; fn main() { Maybe::Some(7); R::Ok(7); }",
            None,
        ),
        ("fn main() { math::Read::Done(7); }", Some("ME006")),
        ("fn main() { math::Hidden::Skipped; }", Some("ME007")),
    ] {
        fs::write(f.0.join("src/main.mb"), source).unwrap();
        let result = resolve(&Project::load(&f.0, None).unwrap(), Target::Application);
        let codes: Vec<_> = result
            .diagnostics
            .iter()
            .map(|d| d.code.to_string())
            .collect();
        assert_eq!(codes, expected.into_iter().collect::<Vec<_>>(), "{source}");
    }
}

#[test]
fn public_outcome_signatures_cannot_expose_private_nested_types() {
    let f = Fixture::new(
        "type Hidden { pub value: i32 }
         pub fn make() -> Option<Attempt<Array<Hidden, 2>, Error>> { None }",
    );
    fs::write(f.0.join("src/main.mb"), "use math::make; fn main() {}").unwrap();
    let result = resolve(&Project::load(&f.0, None).unwrap(), Target::Application);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|d| d.code.to_string() == "ME010" && d.message.contains("Hidden")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn reference_arguments_participate_in_name_and_visibility_checks() {
    let f = Fixture::new("type Hidden { pub value: i32 }");
    for (source, expected) in [
        (
            "fn main() { let a: Option<borrow Missing> = None; }",
            "NE003",
        ),
        (
            "fn main() { let a: Option<borrow math::Hidden> = None; }",
            "ME007",
        ),
        (
            "type Hidden { value: i32 } pub type Maybe = Option<borrow Hidden>; fn main() {}",
            "ME010",
        ),
    ] {
        fs::write(f.0.join("src/main.mb"), source).unwrap();
        let result = resolve(&Project::load(&f.0, None).unwrap(), Target::Application);
        assert!(
            result
                .diagnostics
                .iter()
                .any(|d| d.code.to_string() == expected),
            "{source}: {:?}",
            result.diagnostics
        );
    }
}
