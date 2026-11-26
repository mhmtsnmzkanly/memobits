//! WP22 residual fixes: const parameters forwarded into nested nominal type
//! arguments, and method calls on field-projection receivers.

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
            "memobits-wp22-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let fixture = Self(path);
        fixture.write(
            "project.toml",
            "[package]\nname='wp22'\nentry='main::main'\n",
        );
        fixture
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

    /// Runs the project from source and as a standalone Wasm artifact and
    /// returns the (identical) stdout.
    fn both(&self, expected: &str) {
        let source = self.run(&["run"]);
        assert!(source.status.success(), "source: {source:?}");
        assert_eq!(String::from_utf8_lossy(&source.stdout), expected);
        let build = self.run(&["build", "--output", "out.wasm"]);
        assert!(build.status.success(), "build: {build:?}");
        let wasm = self.run(&["run", "out.wasm"]);
        assert!(wasm.status.success(), "wasm: {wasm:?}");
        assert!(wasm.stderr.is_empty(), "wasm stderr: {wasm:?}");
        assert_eq!(wasm.stdout, source.stdout);
    }

    /// Asserts that `run` (analysis, ownership, lowering) fails with the diagnostic `code` and returns stderr.
    fn rejects(&self, code: &str) -> String {
        let output = self.run(&["run"]);
        assert!(!output.status.success(), "{output:?}");
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert!(stderr.contains(code), "expected {code}: {stderr}");
        stderr
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const BOX: &str = "\
pub type Box2 { pub v: i32 } extend {
    pub fn read(borrow self) -> i32 { self.v }
    pub fn bump(share self) { self.v += 1; }
    pub fn eat(self) -> i32 { self.v }
}
";

// ---- const parameter forwarding ----

const FORWARD: &str = "\
pub type Tag<const N: u32> { pub v: i32 } extend {
    pub fn value(borrow self) -> i32 { self.v }
}
pub type Slot<T, const N: u32> { pub item: T }
pub type Holder<const N: u32> { pub a: i32 } extend {
    pub fn tag(borrow self) -> Tag<N> { Tag<N> { v: self.a } }
    pub fn local(borrow self) -> i32 { let t: Tag<N> = Tag<N> { v: self.a + 1 }; t.value() }
}
pub type Lane<T, const N: u32> { pub a: T, pub items: array<T, N> } extend {
    pub fn slot(borrow self) -> Slot<T, N> { Slot<T, N> { item: self.a } }
}
fn take3(t: Tag<3>) -> i32 { t.value() }
fn take2(t: Tag<2>) -> i32 { t.value() }
";

#[test]
fn const_parameter_forwards_into_nested_types_for_two_instances() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        &format!(
            "{FORWARD}
            fn main() -> i32 {{
                let h3 := Holder<3> {{ a: 30 }};
                let h2 := Holder<2> {{ a: 9 }};
                let lane := Lane<i32, 2> {{ a: 2, items: [1, 2] }};
                let slot := lane.slot();
                let t3 := h3.tag();
                let t2 := h2.tag();
                take3(t3) + take2(t2) + h3.local() + slot.item - 30
            }}"
        ),
    );
    // 30 + 9 + 31 + 2 - 30 = 42
    f.both("Result: i32(42)\n");
}

#[test]
fn forwarded_const_mismatch_is_te002() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        &format!(
            "{FORWARD}
            fn main() -> i32 {{
                let h3 := Holder<3> {{ a: 1 }};
                let t := h3.tag();
                take2(t)
            }}"
        ),
    );
    let stderr = f.rejects("TE002");
    assert!(stderr.contains("Tag<3>"), "{stderr}");
}

#[test]
fn unknown_const_name_stays_ne003() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        "pub type Tag<const N: u32> { pub v: i32 }\n\
         pub type Holder<const N: u32> { pub a: i32 } extend {\n\
             pub fn tag(borrow self) -> Tag<M> { Tag<M> { v: self.a } }\n\
         }\n\
         fn main() -> i32 { 0 }",
    );
    let stderr = f.rejects("NE003");
    assert!(stderr.contains("unknown type 'M'"), "{stderr}");
    // A const parameter is not a type outside a type-argument position.
    f.write(
        "src/main.mb",
        "pub type Holder<const N: u32> { pub a: i32 } extend {\n\
             pub fn bad(borrow self) -> N { 0 }\n\
         }\n\
         fn main() -> i32 { 0 }",
    );
    f.rejects("NE003");
}

#[test]
fn const_parameter_is_not_in_scope_outside_its_item() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        "pub type Tag<const N: u32> { pub v: i32 }\n\
         pub type Plain { pub a: i32 } extend {\n\
             pub fn tag(borrow self) -> Tag<N> { Tag<N> { v: self.a } }\n\
         }\n\
         fn main() -> i32 { 0 }",
    );
    f.rejects("NE003");
}

#[test]
fn generic_function_body_forwards_const_into_nested_type() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        "pub type Tag<const N: u32> { pub v: i32 } extend {\n\
             pub fn value(borrow self) -> i32 { self.v }\n\
         }\n\
         pub fn keep<T, const N: u32>(items: array<T, N>) -> array<T, N> {\n\
             let t: Tag<N> = Tag<N> { v: 7 };\n\
             if t.value() == 7 { items } else { items }\n\
         }\n\
         fn main() -> i32 {\n\
             let a := keep([1, 2]);\n\
             let b := keep([1, 2, 3]);\n\
             if a[1] + b[2] == 5 { 42 } else { 0 }\n\
         }",
    );
    f.both("Result: i32(42)\n");
}

// ---- field-projection receivers ----

#[test]
fn borrow_self_reads_field_nested_field_and_element_places() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        &format!(
            "{BOX}
            pub type Mid {{ pub b: Box2, pub c: Box2 }}
            pub type Tag {{ pub first: Box2, pub x: i32, pub m: Mid }} extend {{
                pub fn inner(borrow self) -> i32 {{ self.first.read() + self.m.c.read() }}
            }}
            pub type Wrap<T> {{ pub value: T }} extend {{
                pub fn unwrap_value(borrow self) -> T {{ self.value }}
            }}
            pub type Holder {{ pub w: Wrap<i32>, pub k: i32 }}
            fn main() -> i32 {{
                let t := Tag {{ first: Box2 {{ v: 10 }}, x: 1, m: Mid {{ b: Box2 {{ v: 3 }}, c: Box2 {{ v: 4 }} }} }};
                let xs := [Box2 {{ v: 5 }}, Box2 {{ v: 6 }}];
                let h := Holder {{ w: Wrap<i32> {{ value: 14 }}, k: 0 }};
                // 10 + 3 + 14 (inner) + 6 (element) + 14 (generic field) - 5 = 42
                t.first.read() + t.m.b.read() + t.inner() + xs[1].read() + h.w.unwrap_value() - 5
            }}"
        ),
    );
    f.both("Result: i32(42)\n");
}

#[test]
fn share_self_on_field_needs_mutable_owner_and_runs_on_places() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        &format!(
            "{BOX}
            pub type Mid {{ pub b: Box2, pub c: Box2 }}
            pub type Tag {{ pub first: Box2, pub m: Mid }}
            fn main() -> i32 {{
                var t := Tag {{ first: Box2 {{ v: 30 }}, m: Mid {{ b: Box2 {{ v: 5 }}, c: Box2 {{ v: 1 }} }} }};
                var xs := [Box2 {{ v: 2 }}, Box2 {{ v: 3 }}];
                t.first.bump();
                t.m.b.bump();
                xs[1].bump();
                t.first.read() + t.m.b.read() + xs[1].read()
            }}"
        ),
    );
    // 31 + 6 + 4 = 41
    f.both("Result: i32(41)\n");

    f.write(
        "src/main.mb",
        &format!(
            "{BOX}
            pub type Tag {{ pub first: Box2 }}
            fn main() -> i32 {{
                let t := Tag {{ first: Box2 {{ v: 1 }} }};
                t.first.bump();
                0
            }}"
        ),
    );
    let stderr = f.rejects("BE005");
    assert!(stderr.contains("immutable owner"), "{stderr}");
}

#[test]
fn field_loans_allow_disjoint_siblings_and_reject_overlap() {
    let f = Fixture::new();
    let program = |statement: &str| {
        format!(
            "{BOX}
            pub type Tag {{ pub first: Box2, pub second: Box2 }}
            fn main() -> i32 {{
                var t := Tag {{ first: Box2 {{ v: 40 }}, second: Box2 {{ v: 1 }} }};
                {statement}
            }}"
        )
    };
    // Disjoint sibling: a live borrow of `first` does not block `second`.
    f.write(
        "src/main.mb",
        &program("let l := t.first.borrow(); t.second.bump(); l.read() + t.second.read()"),
    );
    f.both("Result: i32(42)\n");
    // A live share of `first` does not block a share of `second`.
    f.write(
        "src/main.mb",
        &program("let l := t.first.share(); t.second.bump(); l.read() + t.second.read()"),
    );
    f.both("Result: i32(42)\n");
    // Overlap with the same field.
    f.write(
        "src/main.mb",
        &program("let l := t.first.borrow(); t.first.bump(); l.read()"),
    );
    let stderr = f.rejects("BE005");
    assert!(
        stderr.contains("cannot share `t.first` while it is borrowed"),
        "{stderr}"
    );
    f.write(
        "src/main.mb",
        &program("let l := t.first.share(); t.first.read() + l.read()"),
    );
    let stderr = f.rejects("BE005");
    assert!(
        stderr.contains("cannot borrow `t.first` while it is shared"),
        "{stderr}"
    );
    // Overlap with the whole owner.
    f.write(
        "src/main.mb",
        &program("let l := t.share(); t.first.read() + l.second.v"),
    );
    let stderr = f.rejects("BE005");
    assert!(stderr.contains("while it is shared"), "{stderr}");
}

#[test]
fn owned_self_on_field_or_element_stays_a_rejected_partial_move() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        &format!(
            "{BOX}
            pub type Tag {{ pub first: Box2 }}
            fn main() -> i32 {{
                var t := Tag {{ first: Box2 {{ v: 40 }} }};
                t.first.eat()
            }}"
        ),
    );
    let stderr = f.rejects("TE022");
    assert!(
        stderr.contains("cannot be moved out by field access"),
        "{stderr}"
    );
    f.write(
        "src/main.mb",
        &format!(
            "{BOX}
            fn main() -> i32 {{
                var xs := [Box2 {{ v: 40 }}];
                xs[0].eat()
            }}"
        ),
    );
    let stderr = f.rejects("TE022");
    assert!(
        stderr.contains("cannot be moved out by indexing"),
        "{stderr}"
    );
}

#[test]
fn whole_local_receivers_keep_their_behavior() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        &format!(
            "{BOX}
            fn main() -> i32 {{
                var a := Box2 {{ v: 30 }};
                a.bump();
                let r := a.read();
                let b := Box2 {{ v: 10 }};
                r + b.eat()
            }}"
        ),
    );
    // 31 + 10
    f.both("Result: i32(41)\n");
    f.write(
        "src/main.mb",
        &format!("{BOX}fn main() -> i32 {{ let a := Box2 {{ v: 1 }}; a.bump(); 0 }}"),
    );
    f.rejects("BE005");
    f.write(
        "src/main.mb",
        &format!(
            "{BOX}fn main() -> i32 {{ let a := Box2 {{ v: 1 }}; let x := a.eat(); a.read() + x }}"
        ),
    );
    let stderr = f.rejects("BE");
    assert!(
        stderr.contains("moved") || stderr.contains("BE"),
        "{stderr}"
    );
}

#[test]
fn string_owning_element_receiver_reads_through_borrow_self_repeatedly() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        "pub type Name { pub text: string } extend {\n\
             pub fn size(borrow self) -> u32 { self.text.len() }\n\
         }\n\
         fn main() -> i32 {\n\
             let names := [Name { text: \"hello\" }, Name { text: \"w\u{f6}rld!\" }];\n\
             var round := 0;\n\
             var total := 0;\n\
             loop {\n\
                 if round == 256 { break; }\n\
                 total += names[0].size() as i32 + names[1].size() as i32;\n\
                 round += 1;\n\
             }\n\
             if total == 256 * 12 { 42 } else { 0 }\n\
         }",
    );
    f.both("Result: i32(42)\n");
}

#[test]
fn interface_selected_borrow_self_reads_a_field_place() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        "pub type Point { pub x: i32 }\n\
         pub type Shape { pub origin: Point, pub n: i32 }\n\
         pub interface Draw { fn draw(borrow self) -> i32; }\n\
         extend Point of Draw { fn draw(borrow self) -> i32 { self.x } }\n\
         fn main() -> i32 {\n\
             let s := Shape { origin: Point { x: 42 }, n: 0 };\n\
             s.origin.draw() of Draw\n\
         }",
    );
    f.both("Result: i32(42)\n");
}
