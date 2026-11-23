use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-d1-shapes-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, name: &str, text: &str) {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }

    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_mb"))
            .current_dir(&self.0)
            .args(args)
            .output()
            .unwrap()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn anonymous_records_and_contextual_inline_enum_variants_run_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='d1-shapes'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        type Phase = enum [Ready, Waiting];
        type OtherPhase = enum [Ready, Waiting];
        type PayloadState [Present(i32), Absent]

        fn phase() -> Phase { Ready }
        fn other_phase() -> OtherPhase { Ready }
        fn record_sum(value: { right: u32, left: u32 }) -> u32 {
            value.left + value.right
        }

        fn main() -> i32 {
            var order: u32 = 0;
            let first := {
                right: { order += 1; order },
                left: { order += 1; order },
            };
            let reordered := {
                left: { order += 1; order },
                right: { order += 1; order },
            };
            let selected := if true { first } else { reordered };
            let phase_value: Phase = phase();
            let other_value: OtherPhase = other_phase();
            let payload: PayloadState = PayloadState::Present(7);
            let payload_value := match payload {
                PayloadState::Present(value) => value as u32,
                PayloadState::Absent => 0 as u32,
            };
            let tags := match phase_value {
                Ready => match other_value { Ready => 2 as u32, Waiting => 0 as u32 },
                Waiting => 0 as u32,
            };
            let total := record_sum({ left: 40, right: 2 });
            (selected.right * 10 + selected.left + order + total + tags + payload_value) as i32
        }
        "#,
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(67)\n");

    let build = f.run(&["build", "--output", "d1-shapes.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&["run", "d1-shapes.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn anonymous_record_types_require_the_exact_shape() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='d1-shape-rejection'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn main(flag: bool) -> i32 { let left := { x: 1, y: true }; let right := { x: 2, z: true }; let value := if flag { left } else { right }; value.x }",
    );
    let output = f.run(&["analyze-project"]);
    assert!(!output.status.success(), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("TE013"), "{stderr}");
    assert!(
        stderr.contains("if branches have incompatible types"),
        "{stderr}"
    );
}

#[test]
fn inline_anonymous_enum_declarations_keep_distinct_identity_in_projects() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='d1-enum-identity'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "type First = enum [Ready, Stopped]; type Second = enum [Ready, Stopped]; fn make() -> Second { Ready } fn take_first(value: First) {} fn main() { take_first(make()); }",
    );
    let output = f.run(&["analyze-project"]);
    assert!(!output.status.success(), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("TE002"), "{stderr}");
    assert!(!stderr.contains("panicked"), "{stderr}");
}

#[test]
fn local_inline_enum_annotation_resolves_without_module_variant_declarations() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='d1-local-enum'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn main() -> i32 {
            let phase: enum [Ready, Waiting] = Ready;
            match phase {
                Ready => 42,
                Waiting => 0,
            }
        }
        "#,
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(42)\n");

    let build = f.run(&["build", "--output", "d1-local-enum.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&["run", "d1-local-enum.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn field_bearing_nominal_with_trailing_extension_runs_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='d1-field-extension'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        type Counter { value: i32 } extend {
            fn doubled(borrow self) -> i32 { self.value * 2 }
        }
        fn main() -> i32 {
            let counter := Counter { value: 21 };
            counter.doubled()
        }
        "#,
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(42)\n");

    let build = f.run(&["build", "--output", "d1-field-extension.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&["run", "d1-field-extension.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn payload_anonymous_enums_construct_and_extract_multi_field_payloads_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='d1-anonymous-payloads'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        type Choice = enum [Number(i32), Pair(i32, bool), Empty];
        fn main() -> i32 {
            let number: Choice = Choice::Number(20);
            let pair: enum [Number(i32), Pair(i32, bool), Empty] = Pair(20, true);
            let number_value := match number { Choice::Number(value) => value, _ => 0 };
            match pair {
                Pair(left, enabled) => left + number_value + (if enabled { 2 } else { 0 }),
                _ => 0,
            }
        }
        "#,
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(42)\n");

    let build = f.run(&["build", "--output", "d1-anonymous-payloads.wasm"]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&["run", "d1-anonymous-payloads.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn anonymous_payload_enum_identity_and_payload_types_are_checked() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='d1-anonymous-payload-rejections'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "type First = enum [Item(i32), Empty]; type Second = enum [Item(i32), Empty]; fn make() -> Second { Item(42) } fn take_first(value: First) {} fn main() { take_first(make()); }",
    );
    let output = f.run(&["analyze-project"]);
    assert!(!output.status.success(), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("TE002"), "{stderr}");
    assert!(!stderr.contains("panicked"), "{stderr}");

    f.write(
        "src/main.mb",
        "fn main() { let value: enum [Item(i32), Empty] = Item(true); }",
    );
    let output = f.run(&["analyze-project"]);
    assert!(!output.status.success(), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("TE002"), "{stderr}");
    assert!(stderr.contains("expected i32, found Bool"), "{stderr}");

    for (source, code, message) in [
        (
            "fn main() { let item: enum [Item(i32)] = Item; }",
            "TE028",
            "carries 1 payload value(s)",
        ),
        (
            "fn main() { let item: enum [Item(i32)] = Item(); }",
            "TE010",
            "expects 1 argument(s), found 0",
        ),
    ] {
        f.write("src/main.mb", source);
        let output = f.run(&["analyze-project"]);
        assert!(!output.status.success(), "{source}: {output:?}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains(code), "{source}: {stderr}");
        assert!(stderr.contains(message), "{source}: {stderr}");
    }

    f.write(
        "src/main.mb",
        "fn main(value: i32?) { let item: enum [Borrowed((borrow i32)?)] = Borrowed(value); }",
    );
    let output = f.run(&["analyze-project"]);
    assert!(!output.status.success(), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("TE017"), "{stderr}");
    assert!(
        stderr.contains("reference type arguments require embedded-loan tracking"),
        "{stderr}"
    );

    f.write(
        "src/main.mb",
        "type Choice = enum [Owned(string), Empty]; fn size(value: Choice) -> u32 { match value { Owned(text) => text.len() as u32, Empty => 0 } } fn main() -> u32 { let text := \"alpha\".concat(\"\"); let value: Choice = Owned(text); size(value) }",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: u32(5)\n");

    let output = f.run(&["build", "--output", "owned-payload.wasm"]);
    assert!(output.status.success(), "{output:?}");
    let wasm = f.run(&["run", "owned-payload.wasm"]);
    assert!(
        wasm.status.success(),
        "Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, b"Result: i32(5)\n");
}

#[test]
fn generic_nominal_trailing_methods_specialize_for_each_receiver_type() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='d1-generic-inherent'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        type Box<T> { value: T } extend {
            fn read_value(borrow self) -> T { self.value }
        }
        type Packet<const N: u32> { values: array<u32, N> } extend {
            fn first(borrow self) -> u32 { self.values[0] }
        }
        fn main() -> i32 {
            let number := Box<i32> { value: 40 };
            let flag := Box<bool> { value: true };
            let packet := Packet<1> { values: [2] };
            let other := Packet<2> { values: [0, 3] };
            if number.read_value() + packet.first() as i32 == 42
                && flag.read_value() && other.first() == 0 { 42 } else { 0 }
        }
        "#,
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(42)\n");

    let build = f.run(&["build", "--output", "d1-generic-inherent.wasm"]);
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&["run", "d1-generic-inherent.wasm"]);
    assert!(
        wasm.status.success(),
        "{}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn generic_nominal_method_specialization_reaches_mutual_method_calls() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='d1-generic-mutual-methods'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        type Box<T> { value: i32 } extend {
            fn left(borrow self) -> i32 {
                if self.value == 0 { 42 } else { self.right() }
            }
            fn right(borrow self) -> i32 {
                if self.value == 0 { 42 } else { self.left() }
            }
        }
        fn main() -> i32 {
            let value := Box<bool> { value: 0 };
            value.left()
        }
        "#,
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(42)\n");

    let build = f.run(&["build", "--output", "d1-generic-mutual-methods.wasm"]);
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&["run", "d1-generic-mutual-methods.wasm"]);
    assert!(
        wasm.status.success(),
        "{}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn generic_nominal_method_can_instantiate_a_generic_free_function() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='d1-generic-method-function'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn identity<T>(value: T) -> T { value }
        type Box<T> { value: T } extend {
            fn take_value(self) -> T { identity(self.value) }
        }
        fn main() -> i32 {
            let value := Box<i32> { value: 41 };
            value.take_value() + 1
        }
        "#,
    );

    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(42)\n");

    let build = f.run(&["build", "--output", "d1-generic-method-function.wasm"]);
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&["run", "d1-generic-method-function.wasm"]);
    assert!(
        wasm.status.success(),
        "{}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn generic_nominal_method_visibility_crosses_only_public_direct_imports() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='d1-generic-method-visibility'\nentry='main::main'\n",
    );
    f.write(
        "src/geometry.mb",
        "pub type Box<T> { pub value: T } extend { pub fn read(borrow self) -> T { self.value } }",
    );
    f.write(
        "src/main.mb",
        "use geometry; use geometry::Box; fn main() -> i32 { let value := Box<i32> { value: 42 }; value.read() }",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(42)\n");

    let build = f.run(&["build", "--output", "d1-generic-method-visibility.wasm"]);
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&["run", "d1-generic-method-visibility.wasm"]);
    assert!(
        wasm.status.success(),
        "{}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, source.stdout);

    f.write(
        "src/geometry.mb",
        "pub type Box<T> { pub value: T } extend { fn hidden(borrow self) -> T { self.value } }",
    );
    f.write(
        "src/main.mb",
        "use geometry; use geometry::Box; fn main() -> i32 { let value := Box<i32> { value: 42 }; value.hidden() }",
    );
    let hidden = f.run(&["run"]);
    assert!(!hidden.status.success(), "{hidden:?}");
    let stderr = String::from_utf8_lossy(&hidden.stderr);
    assert!(stderr.contains("TE007"), "{stderr}");
    assert!(
        stderr.contains("matching inherent extension is private or inactive"),
        "{stderr}"
    );
}

#[test]
fn generic_nominal_method_specialization_limit_is_reported() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='d1-generic-method-limit'\nentry='main::main'\n",
    );
    let mut source = String::new();
    for index in 0..257 {
        source.push_str(&format!("type Marker{index} {{}}\n"));
    }
    source.push_str(
        "type Box<T> { value: i32 } extend { fn ping(borrow self) -> i32 { if self.value == 0 { 0 } else { self.ping() } } }\nfn main() {\n",
    );
    for index in 0..257 {
        source.push_str(&format!(
            "let value{index} := Box<Marker{index}> {{ value: Marker{index} {{}} }}; value{index}.ping();\n"
        ));
    }
    source.push_str("}\n");
    f.write("src/main.mb", &source);

    let output = f.run(&["analyze-project"]);
    assert!(!output.status.success(), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(
            "generic inherent method specialization limit exceeded (maximum 256 distinct methods)"
        ),
        "{stderr}"
    );
}

#[test]
fn generic_nominal_method_visibility_rejects_symbol_transitive_and_private_extensions() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='d1-generic-method-visibility-edges'\nentry='main::main'\n",
    );
    f.write(
        "src/geometry.mb",
        "pub type Box<T> { pub value: T } extend { pub fn read(borrow self) -> T { self.value } }",
    );
    f.write(
        "src/main.mb",
        "use geometry::Box; fn main() -> i32 { let value := Box<i32> { value: 42 }; value.read() }",
    );
    let symbol_only = f.run(&["run"]);
    assert!(!symbol_only.status.success(), "{symbol_only:?}");
    let stderr = String::from_utf8_lossy(&symbol_only.stderr);
    assert!(stderr.contains("TE024"), "{stderr}");
    assert!(
        stderr.contains("struct 'Box<i32>' has no field 'read'"),
        "{stderr}"
    );

    f.write("src/bridge.mb", "use geometry; pub fn marker() {}");
    f.write(
        "src/main.mb",
        "use bridge; use geometry::Box; fn main() -> i32 { let value := Box<i32> { value: 42 }; value.read() }",
    );
    let transitive = f.run(&["run"]);
    assert!(!transitive.status.success(), "{transitive:?}");
    let stderr = String::from_utf8_lossy(&transitive.stderr);
    assert!(stderr.contains("TE024"), "{stderr}");
    assert!(
        stderr.contains("struct 'Box<i32>' has no field 'read'"),
        "{stderr}"
    );

    f.write(
        "src/geometry.mb",
        "pub type Box<T> { pub value: T } extend Box<i32> { pub fn hidden(borrow self) -> i32 { self.value } }",
    );
    f.write(
        "src/main.mb",
        "use geometry; use geometry::Box; fn main() -> i32 { let value := Box<i32> { value: 42 }; value.hidden() }",
    );
    let private_extension = f.run(&["run"]);
    assert!(!private_extension.status.success(), "{private_extension:?}");
    let stderr = String::from_utf8_lossy(&private_extension.stderr);
    assert!(stderr.contains("TE007"), "{stderr}");
    assert!(
        stderr.contains("matching inherent extension is private or inactive"),
        "{stderr}"
    );
}
