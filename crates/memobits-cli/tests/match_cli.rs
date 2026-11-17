//! End-to-end `match` programs (package B2): source runs and built artifacts,
//! cross-module and aliased enums, and the diagnostics users see.
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
            "memobits-match-cli-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let fixture = Self(path);
        fixture.write(
            "project.toml",
            "[package]\nname='matching'\nentry='app::main'\n",
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
    /// Run from source and from the built artifact; both must agree.
    fn result(&self, source: &str) -> String {
        self.write("src/app.mb", source);
        let from_source = self.run(&["run"]);
        assert!(
            from_source.status.success(),
            "{source}: {}",
            String::from_utf8_lossy(&from_source.stderr)
        );
        let built = self.run(&["build"]);
        assert!(
            built.status.success(),
            "{source}: {}",
            String::from_utf8_lossy(&built.stderr)
        );
        let from_artifact = self.run(&["run", "target/memobits/app.wasm"]);
        assert!(from_artifact.status.success());
        assert_eq!(from_source.stdout, from_artifact.stdout, "{source}");
        String::from_utf8(from_source.stdout).unwrap().trim().into()
    }
    fn error(&self, source: &str, code: &str) -> String {
        self.write("src/app.mb", source);
        let output = self.run(&["run"]);
        assert_eq!(output.status.code(), Some(1), "{source}");
        assert!(output.stdout.is_empty());
        let text = String::from_utf8(output.stderr).unwrap();
        assert!(text.contains(code), "{source}: {text}");
        text
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const SHAPE: &str = "type Shape [ Empty, Circle(f64), Rect(f64, f64) ]\n";

#[test]
fn shape_areas_via_match_return_floats_and_integers() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{SHAPE}\
             fn area(s: Shape) -> f64 {{\n\
                 match s {{\n\
                     Shape::Empty => 0.0,\n\
                     Shape::Circle(r) => 3.0 * r * r,\n\
                     Shape::Rect(w, h) => {{ w * h }}\n\
                 }}\n\
             }}\n\
             fn sides(s: Shape) -> i32 {{\n\
                 match s {{ Shape::Empty => 0, Shape::Circle(_) => 1, Shape::Rect(_, _) => 4 }}\n\
             }}\n\
             fn main() -> i32 {{\n\
                 let total := area(Shape::Rect(2.0, 4.0)) + area(Shape::Circle(2.0)) + area(Shape::Empty);\n\
                 if total == 20.0 {{ sides(Shape::Rect(1.0, 1.0)) * 10 + sides(Shape::Circle(1.0)) }} else {{ -1 }}\n\
             }}"
        )),
        "Result: i32(41)"
    );
}

#[test]
fn nested_enums_and_aggregate_payloads_match() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "type P { x: i32, y: i32 }\n\
             type Inner [ Num(i32), Pt(P, Array<i32, 2>) ]\n\
             type Outer [ Nothing, Some(Inner), Two(Inner, Inner) ]\n\
             fn weigh(i: Inner) -> i32 {\n\
                 match i { Inner::Num(n) => n, Inner::Pt(p, a) => { let q := p; q.x * q.y + a[1] } }\n\
             }\n\
             fn main() -> i32 {\n\
                 let o := Outer::Two(Inner::Num(5), Inner::Pt(P { x: 3, y: 4 }, [0, 100]));\n\
                 match o {\n\
                     Outer::Nothing => -1,\n\
                     Outer::Some(i) => weigh(i),\n\
                     Outer::Two(a, b) => weigh(a) + weigh(b),\n\
                 }\n\
             }"
        ),
        "Result: i32(117)"
    );
}

#[test]
fn match_over_values_built_in_a_loop() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{SHAPE}\
             fn pick(i: i32) -> Shape {{\n\
                 if i == 0 {{ Shape::Empty }} else if i == 1 {{ Shape::Circle(2.0) }} else {{ Shape::Rect(3.0, 4.0) }}\n\
             }}\n\
             fn main() -> i32 {{\n\
                 let kinds: Array<i32, 3> = [0, 1, 2];\n\
                 var total := 0;\n\
                 var i := 0;\n\
                 loop {{\n\
                     if i == 3 {{ break; }}\n\
                     total += match pick(kinds[i]) {{\n\
                         Shape::Empty => 1,\n\
                         Shape::Circle(r) => if r > 1.0 {{ 10 }} else {{ 20 }},\n\
                         Shape::Rect(w, h) => if w * h > 11.0 {{ 100 }} else {{ 200 }},\n\
                     }};\n\
                     i += 1;\n\
                 }}\n\
                 total\n\
             }}"
        )),
        "Result: i32(111)"
    );
}

#[test]
fn divergent_arms_and_statement_position_matches() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{SHAPE}\
             fn first_corner(s: Shape) -> i32 {{\n\
                 let w := match s {{\n\
                     Shape::Rect(w, _) => w,\n\
                     Shape::Circle(r) => r,\n\
                     Shape::Empty => return -1,\n\
                 }};\n\
                 if w > 2.5 {{ 3 }} else {{ 2 }}\n\
             }}\n\
             fn main() -> i32 {{\n\
                 var hits := 0;\n\
                 match Shape::Circle(1.0) {{ Shape::Empty => {{ hits += 100; }} _ => {{ hits += 1; }} }}\n\
                 match Shape::Empty {{ Shape::Empty => {{ hits += 10; }} _ => {{}} }}\n\
                 hits * 100 + first_corner(Shape::Rect(3.0, 1.0)) * 10 + first_corner(Shape::Empty) + 1\n\
             }}"
        )),
        "Result: i32(1130)"
    );
}

#[test]
fn a_state_machine_enum_steps_to_completion() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            "type State [ Start, Running(i32), Done(i32) ]\n\
             fn step(s: State) -> State {\n\
                 match s {\n\
                     State::Start => State::Running(1),\n\
                     State::Running(n) => if n >= 4 { State::Done(n * n) } else { State::Running(n + 1) },\n\
                     State::Done(n) => State::Done(n),\n\
                 }\n\
             }\n\
             fn result(s: State) -> i32 { match s { State::Done(n) => n, _ => -1 } }\n\
             fn main() -> i32 {\n\
                 var s := State::Start;\n\
                 var steps := 0;\n\
                 loop {\n\
                     s = step(s);\n\
                     steps += 1;\n\
                     if steps == 5 { break; }\n\
                 }\n\
                 result(s) * 10 + steps\n\
             }"
        ),
        "Result: i32(165)"
    );
}

#[test]
fn imported_and_aliased_enums_match_through_qualified_paths() {
    let f = Fixture::new();
    f.write(
        "src/shapes.mb",
        "pub type Shape [ Empty, Circle(f64), Rect(i32, i32) ]\n\
         pub fn square(n: i32) -> Shape { Shape::Rect(n, n) }\n",
    );
    assert_eq!(
        f.result(
            "use shapes::Shape;\n\
             type Alias = shapes::Shape;\n\
             type Local = Shape;\n\
             fn area(s: Alias) -> i32 {\n\
                 match s {\n\
                     Alias::Empty => 0,\n\
                     shapes::Shape::Circle(_) => 1,\n\
                     Local::Rect(w, h) => w * h,\n\
                 }\n\
             }\n\
             fn main() -> i32 {\n\
                 area(shapes::square(6)) + area(Alias::Circle(1.0)) + area(Local::Empty)\n\
             }"
        ),
        "Result: i32(37)"
    );
}

#[test]
fn aliases_of_enum_types_resolve_variant_paths() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{SHAPE}type S = Shape;\ntype T = S;\n\
             fn main() -> i32 {{\n\
                 let a := S::Circle(1.0);\n\
                 let b := T::Rect(2.0, 3.0);\n\
                 let x := match a {{ S::Empty => 0, T::Circle(_) => 1, S::Rect(_, _) => 2 }};\n\
                 let y := match b {{ T::Empty => 0, S::Circle(_) => 1, Shape::Rect(_, _) => 2 }};\n\
                 x * 10 + y\n\
             }}"
        )),
        "Result: i32(12)"
    );
    // An unknown variant through an alias is still reported by the resolver.
    f.error(
        &format!("{SHAPE}type S = Shape;\nfn main() -> i32 {{ let a := S::Missing; 0 }}"),
        "NE004",
    );
}

#[test]
fn match_diagnostics_name_the_problem() {
    let f = Fixture::new();
    let text = f.error(
        &format!("{SHAPE}fn main() -> i32 {{ match Shape::Empty {{ Shape::Empty => 1 }} }}"),
        "TE031",
    );
    assert!(
        text.contains("missing Shape::Circle, Shape::Rect"),
        "{text}"
    );
    let text = f.error(
        &format!(
            "{SHAPE}fn main() -> i32 {{ match Shape::Empty {{ Shape::Empty => 1, Shape::Empty => 2, _ => 3 }} }}"
        ),
        "TE032",
    );
    assert!(text.contains("already matched"), "{text}");
    let text = f.error(
        &format!(
            "{SHAPE}type Other [ Empty ]\nfn main() -> i32 {{ match Shape::Empty {{ Other::Empty => 1, _ => 3 }} }}"
        ),
        "TE030",
    );
    assert!(text.contains("belongs to enum 'Other'"), "{text}");
    let text = f.error(
        &format!(
            "{SHAPE}fn main() -> i32 {{ match Shape::Empty {{ Shape::Circle(a, b) => 1, _ => 3 }} }}"
        ),
        "TE030",
    );
    assert!(
        text.contains("1 payload value(s) but the pattern binds 2"),
        "{text}"
    );
    f.error(
        &format!(
            "{SHAPE}fn main() -> i32 {{ let s := Shape::Empty; let a := Shape::Empty == s; 0 }}"
        ),
        "TE007",
    );
}

#[test]
fn the_scrutinee_is_consumed_and_payloads_are_owned() {
    let f = Fixture::new();
    let text = f.error(
        &format!(
            "{SHAPE}fn main() -> i32 {{\n    let s := Shape::Circle(1.0);\n    let n := match s {{ Shape::Circle(_) => 1, _ => 2 }};\n    match s {{ _ => n }}\n}}"
        ),
        "BE001",
    );
    assert!(text.contains("'s'"), "{text}");
    f.error(
        "type P { x: i32 }\ntype E [ A(P) ]\nfn main() -> i32 { match E::A(P { x: 1 }) { E::A(p) => { let q := p; let r := p; 0 } } }",
        "BE001",
    );
}

#[test]
fn borrowed_and_place_scrutinees_match_in_place() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{SHAPE}type H {{ s: Shape }}\n\
             fn look(s: borrow Shape) -> i32 {{ match s {{ Shape::Empty => 1, _ => 2 }} }}\n\
             fn peek(s: share Shape) -> i32 {{ match s {{ Shape::Circle(_) => 10, _ => 20 }} }}\n\
             fn main() -> i32 {{\n\
                 var s := Shape::Circle(1.0);\n\
                 let h := H {{ s: Shape::Empty }};\n\
                 look(s.borrow()) + peek(s.share()) * 10 + match h.s {{ Shape::Empty => 1000, _ => 0 }}\n\
             }}"
        )),
        "Result: i32(1102)"
    );
}

#[test]
fn unsupported_pattern_forms_are_syntax_errors_with_hints() {
    let f = Fixture::new();
    for (pattern, hint) in [
        ("1 => 0,", "literal patterns"),
        ("Shape::Circle(Shape::Empty) => 0,", "nested patterns"),
        ("Shape::Circle(r) if r > 1.0 => 0,", "guards"),
    ] {
        let text = f.error(
            &format!("{SHAPE}fn main() -> i32 {{ match Shape::Empty {{ {pattern} _ => 1 }} }}"),
            "SE002",
        );
        assert!(text.contains(hint), "{text}");
    }
}

#[test]
fn the_enums_example_project_runs_from_source_and_artifact() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/projects/enums");
    let copy = Fixture::new();
    fs::remove_file(copy.0.join("project.toml")).unwrap();
    copy.write(
        "project.toml",
        &fs::read_to_string(root.join("project.toml")).unwrap(),
    );
    copy.write(
        "src/main.mb",
        &fs::read_to_string(root.join("src/main.mb")).unwrap(),
    );
    let run = copy.run(&["run"]);
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(
        String::from_utf8(run.stdout).unwrap().trim(),
        "Result: i32(1094300)"
    );
    assert!(copy.run(&["build"]).status.success());
    let artifact = copy.run(&["run", "target/memobits/app.wasm"]);
    assert_eq!(
        String::from_utf8(artifact.stdout).unwrap().trim(),
        "Result: i32(1094300)"
    );
}

// ---- Package B3: borrowing matches over places and references ----

const GEOM: &str = "type P { x: i32, y: i32 }\n\
    type Shape [ Empty, Circle(i32), Rect(i32, i32), Poly(P, Array<i32, 3>) ]\n\
    type Holder { shape: Shape, tag: P }\n\
    fn is_big(s: borrow Shape) -> Bool {\n\
        match s { Shape::Rect(w, h) => w * h > 10, _ => false }\n\
    }\n\
    fn sum_point(p: borrow P) -> i32 { p.x + p.y }\n";

#[test]
fn matching_an_enum_array_in_a_loop_counts_variants_and_sums_payloads() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{GEOM}\
             fn main() -> i32 {{\n\
                 let shapes: Array<Shape, 5> = [Shape::Rect(2, 3), Shape::Empty, Shape::Circle(4), \
                     Shape::Poly(P {{ x: 1, y: 2 }}, [10, 20, 30]), Shape::Rect(4, 5)];\n\
                 var rects := 0;\n\
                 var empties := 0;\n\
                 var sum := 0;\n\
                 var i := 0;\n\
                 loop {{\n\
                     if i == 5 {{ break; }}\n\
                     match shapes[i] {{\n\
                         Shape::Rect(w, h) => {{ rects += 1; sum += w * h; }}\n\
                         Shape::Empty => {{ empties += 1; }}\n\
                         Shape::Circle(r) => {{ sum += r; }}\n\
                         Shape::Poly(p, pts) => {{ sum += sum_point(p) + pts[1]; }}\n\
                     }}\n\
                     i += 1;\n\
                 }}\n\
                 rects * 1000 + empties * 100 + sum\n\
             }}"
        )),
        // sum = 6 + 4 + (3 + 20) + 20 = 53
        "Result: i32(2153)"
    );
}

#[test]
fn matching_a_struct_field_and_borrowing_params_agree_from_source_and_artifact() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{GEOM}\
             fn main() -> i32 {{\n\
                 let h := Holder {{ shape: Shape::Rect(4, 5), tag: P {{ x: 7, y: 8 }} }};\n\
                 let arr: Array<Shape, 2> = [Shape::Empty, Shape::Rect(1, 1)];\n\
                 let by_field := match h.shape {{ Shape::Rect(w, _) => w, _ => 0 }};\n\
                 let by_param := if is_big(h.shape.borrow()) {{ 10 }} else {{ 0 }};\n\
                 let by_elem := if is_big(arr[1].borrow()) {{ 100 }} else {{ 1 }};\n\
                 by_field + by_param + by_elem\n\
             }}"
        )),
        "Result: i32(15)"
    );
}

#[test]
fn nested_enum_payloads_and_aggregate_payload_bindings_read_through_references() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{GEOM}\
             type Wrap [ Plain, Boxed(Shape) ]\n\
             fn main() -> i32 {{\n\
                 let w: Array<Wrap, 2> = [Wrap::Plain, Wrap::Boxed(Shape::Poly(P {{ x: 3, y: 4 }}, [5, 6, 7]))];\n\
                 match w[1] {{\n\
                     Wrap::Boxed(inner) => match inner {{\n\
                         Shape::Poly(p, pts) => sum_point(p) * 100 + pts[2],\n\
                         _ => 0,\n\
                     }},\n\
                     Wrap::Plain => 1,\n\
                 }}\n\
             }}"
        )),
        "Result: i32(707)"
    );
}

#[test]
fn a_disjoint_write_during_a_payload_borrow_runs_and_an_overlapping_one_is_be005() {
    let f = Fixture::new();
    assert_eq!(
        f.result(&format!(
            "{GEOM}\
             fn main() -> i32 {{\n\
                 var h := Holder {{ shape: Shape::Poly(P {{ x: 1, y: 2 }}, [3, 4, 5]), tag: P {{ x: 0, y: 0 }} }};\n\
                 match h.shape {{\n\
                     Shape::Poly(p, _) => {{ h.tag.y = 9; p.x + h.tag.y }}\n\
                     _ => 0,\n\
                 }}\n\
             }}"
        )),
        "Result: i32(10)"
    );
    let text = f.error(
        &format!(
            "{GEOM}\
             fn main() -> i32 {{\n\
                 var h := Holder {{ shape: Shape::Poly(P {{ x: 1, y: 2 }}, [3, 4, 5]), tag: P {{ x: 0, y: 0 }} }};\n\
                 match h.shape {{\n\
                     Shape::Poly(p, _) => {{ h.shape = Shape::Empty; p.x }}\n\
                     _ => 0,\n\
                 }}\n\
             }}"
        ),
        "BE005",
    );
    assert!(
        text.contains("cannot write `h.shape` while it is borrowed"),
        "{text}"
    );
    assert!(
        text.contains("`h.shape::Poly.0` was borrowed here"),
        "{text}"
    );
    assert!(text.contains("is used later here"), "{text}");
}

#[test]
fn a_dynamic_index_write_during_a_payload_borrow_is_be005() {
    let f = Fixture::new();
    let text = f.error(
        &format!(
            "{GEOM}\
             fn main() -> i32 {{\n\
                 var a: Array<Shape, 2> = [Shape::Poly(P {{ x: 1, y: 2 }}, [3, 4, 5]), Shape::Empty];\n\
                 var i := 0;\n\
                 var j := 1;\n\
                 match a[i] {{\n\
                     Shape::Poly(p, _) => {{ a[j] = Shape::Empty; p.x }}\n\
                     _ => 0,\n\
                 }}\n\
             }}"
        ),
        "BE005",
    );
    assert!(text.contains("`a[_]`"), "{text}");
}

#[test]
fn payload_bindings_cannot_be_moved_out_or_written_and_owned_matches_still_consume() {
    let f = Fixture::new();
    let text = f.error(
        &format!(
            "{GEOM}\
             fn take(p: P) -> i32 {{ p.x }}\n\
             fn main() -> i32 {{\n\
                 let a: Array<Shape, 1> = [Shape::Poly(P {{ x: 1, y: 2 }}, [3, 4, 5])];\n\
                 match a[0] {{ Shape::Poly(p, _) => take(p), _ => 0 }}\n\
             }}"
        ),
        "TE017",
    );
    assert!(text.contains("reference values cannot escape"), "{text}");
    let text = f.error(
        &format!(
            "{GEOM}\
             fn main() -> i32 {{\n\
                 var a: Array<Shape, 1> = [Shape::Poly(P {{ x: 1, y: 2 }}, [3, 4, 5])];\n\
                 match a[0] {{ Shape::Poly(p, _) => {{ p.x = 5; 1 }}, _ => 0 }}\n\
             }}"
        ),
        "TE004",
    );
    assert!(
        text.contains("cannot assign through borrow binding 'p'"),
        "{text}"
    );
    let text = f.error(
        &format!(
            "{GEOM}\
             fn main() -> i32 {{\n\
                 let s := Shape::Circle(3);\n\
                 let a := match s {{ Shape::Circle(r) => r, _ => 0 }};\n\
                 match s {{ Shape::Circle(r) => r + a, _ => 0 }}\n\
             }}"
        ),
        "BE001",
    );
    assert!(text.contains("'s'"), "{text}");
}
