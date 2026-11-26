//! Field-disjoint loans (package A4): loans carry a projection path, and two
//! accesses conflict only when their paths may overlap.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_syntax::parse;

const DECLS: &str = "type P { x: i32, y: i32 } \
    type Line { a: P, b: P } \
    type Grid { rows: array<array<i32, 3>, 2>, tag: i32 } \
    fn both(a: share P, b: share P) {} \
    fn rd2(a: borrow P, b: borrow P) -> i32 { a.x + b.x } \
    fn mix(a: share P, b: borrow P) {} \
    fn row2(a: share array<i32, 3>, b: share array<i32, 3>) {} \
    fn bump(p: share P) { p.x += 1; } ";

fn ownership(source: &str) -> Vec<String> {
    let parsed = parse(SourceId(52), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let program = lower_module(&parsed.module, "test", &["main".into()])
        .unwrap_or_else(|errors| panic!("{source}: {errors:?}"));
    program.validate().unwrap();
    memobits_ownership::check_ownership(&program)
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

fn accepted(body: &str) {
    let codes = ownership(&format!("{DECLS} fn main() {{ {body} }}"));
    assert!(codes.is_empty(), "{body}: {codes:?}");
}

fn rejected(body: &str) {
    let codes = ownership(&format!("{DECLS} fn main() {{ {body} }}"));
    assert!(codes.iter().any(|c| c == "BE005"), "{body}: {codes:?}");
}

const LINE: &str = "var l := Line { a: P { x: 1, y: 2 }, b: P { x: 3, y: 4 } }; ";
const GRID: &str = "var g := Grid { rows: [[1, 2, 3], [4, 5, 6]], tag: 0 }; ";
const MAT: &str = "var m := [[1, 2], [3, 4], [5, 6]]; ";

#[test]
fn distinct_fields_are_independent_locations() {
    for body in [
        "let r := l.a.borrow(); l.b.x = 5; let v := r.x;",
        "var r := l.a.share(); l.b.x = 5; r.x = 1;",
        "let r := l.a.borrow(); var s := l.b.share(); s.x = 2; let v := r.x;",
        "let r := l.a.x.copy(); l.b.x = 1; let v := l.a.y + r;",
        "both(l.a.share(), l.b.share());",
        "mix(l.a.share(), l.b.borrow());",
        "let r := l.b.borrow(); bump(l.a.share()); let v := r.x;",
        "let r := l.a.borrow(); l.b = P { x: 0, y: 0 }; let v := r.x;",
    ] {
        accepted(&format!("{LINE}{body}"));
    }
}

#[test]
fn the_same_field_a_parent_or_a_child_overlaps() {
    for body in [
        "let r := l.a.borrow(); l.a.x = 5; let v := r.x;",
        "let r := l.a.borrow(); bump(l.a.share()); let v := r.x;",
        "both(l.a.share(), l.a.share());",
        "mix(l.a.share(), l.a.borrow());",
        // A loan below a field blocks the enclosing field and the root.
        "let r := l.a.borrow(); l.a = P { x: 0, y: 0 }; let v := r.x;",
        "let r := l.a.borrow(); l = Line { a: P { x: 0, y: 0 }, b: P { x: 0, y: 0 } }; let v := r.x;",
        // Moving the whole root with a live loan below it.
        "let r := l.a.borrow(); let q := l; let v := r.x;",
        // Loans above: a whole-struct borrow blocks every field write.
        "let r := l.borrow(); l.b.x = 1; let v := r.a.x;",
    ] {
        rejected(&format!("{LINE}{body}"));
    }
}

#[test]
fn constant_indices_are_disjoint_and_dynamic_indices_overlap() {
    for body in [
        "let r := m[0].borrow(); m[1][0] = 9; let v := r[0];",
        "var r := m[0].share(); let v := m[1][1] + m[2][0]; r[0] = v;",
        "let r := m[2].borrow(); m[0][1] = 1; m[1][1] = 2; let v := r[0];",
    ] {
        accepted(&format!("{MAT}{body}"));
    }
    accepted(&format!(
        "{GRID}row2(g.rows[0].share(), g.rows[1].share());"
    ));
    accepted(&format!(
        "{GRID}let r := g.rows[0].borrow(); g.tag = 3; g.rows[1][2] = 1; let v := r[0];"
    ));
    for body in [
        // Dynamic index against a constant or another dynamic index.
        "var i := 0; let r := m[i].borrow(); m[0][0] = 1; let v := r[0];",
        "var i := 0; let r := m[0].borrow(); m[i][0] = 1; let v := r[0];",
        "var i := 0; var j := 1; let r := m[i].borrow(); m[j][0] = 1; let v := r[0];",
        "let r := m[0].borrow(); m[0][1] = 1; let v := r[0];",
        // Whole-array moves and writes conflict with any element loan.
        "let r := m[0].borrow(); m = [[0, 0], [0, 0], [0, 0]]; let v := r[0];",
    ] {
        rejected(&format!("{MAT}{body}"));
    }
}

#[test]
fn calls_with_two_projections_follow_the_same_rule() {
    accepted(&format!("{LINE}both(l.a.share(), l.b.share());"));
    accepted(&format!(
        "{GRID}row2(g.rows[0].share(), g.rows[1].share());"
    ));
    for body in [
        "var i := 0; var j := 1; row2(g.rows[i].share(), g.rows[j].share());",
        "var i := 0; row2(g.rows[i].share(), g.rows[0].share());",
        "row2(g.rows[0].share(), g.rows[0].share());",
    ] {
        rejected(&format!("{GRID}{body}"));
    }
}

#[test]
fn live_loans_across_loop_back_edges_keep_their_paths() {
    // A loan to l.a stays live through the loop; writes to l.b are fine.
    accepted(&format!(
        "{LINE}let r := l.a.borrow(); var n := 0; \
         loop {{ l.b.x += 1; n += 1; if n > 3 {{ break; }} }} let v := r.x;"
    ));
    // The same field is written inside the loop while the loan is live.
    rejected(&format!(
        "{LINE}let r := l.a.borrow(); var n := 0; \
         loop {{ l.a.x += 1; n += 1; if n > 3 {{ break; }} }} let v := r.x;"
    ));
    // A dynamic row write in the loop may hit the borrowed constant row.
    rejected(&format!(
        "{MAT}let r := m[0].borrow(); var i := 0; \
         loop {{ m[i][0] = 5; i += 1; if i > 1 {{ break; }} }} let v := r[0];"
    ));
    // Constant rows stay disjoint however often the loop runs.
    accepted(&format!(
        "{MAT}let r := m[0].borrow(); var i := 0; \
         loop {{ m[1][0] = 5; i += 1; if i > 1 {{ break; }} }} let v := r[0];"
    ));
    // A loan created inside the loop body dies before the back edge.
    accepted(&format!(
        "{LINE}var n := 0; loop {{ var r := l.a.share(); r.x += 1; l.b.x += 1; n += 1; if n > 2 {{ break; }} }}"
    ));
}

#[test]
fn a_dynamic_share_conflicts_with_a_write_to_a_constant_element() {
    // Rows (sub-aggregates) are the lendable elements.
    rejected(
        "var a := [[1, 2], [3, 4]]; var i := 1; var r := a[i].share(); a[0][0] = 9; r[0] = 2;",
    );
    rejected("var a := [[1, 2], [3, 4]]; var i := 1; let r := a[i].borrow(); a[0][0] = 9; let v := r[0];");
    accepted("var a := [[1, 2], [3, 4]]; let r := a[1].borrow(); a[0][0] = 9; let v := r[0];");
}

#[test]
fn reference_parameters_keep_projection_paths_when_reborrowed() {
    for source in [
        "fn f(l: share Line) { let r := l.a.borrow(); l.b.x = 5; let v := r.x; }",
        "fn f(l: share Line) { var ra := l.a.share(); let rb := l.b.share(); ra.x = rb.x; }",
        "fn f(l: share Line) { both(l.a.share(), l.b.share()); }",
        "fn f(l: borrow Line) -> i32 { rd2(l.a.borrow(), l.b.borrow()) }",
        "fn f(l: share Line) { var r := l.share(); var ra := r.a.share(); let rb := r.b.share(); ra.x = rb.x; }",
    ] {
        let codes = ownership(&format!("{DECLS} {source} fn main() {{}}"));
        assert!(codes.is_empty(), "{source}: {codes:?}");
    }
    for source in [
        "fn f(l: share Line) { let r := l.a.borrow(); l.a.x = 5; let v := r.x; }",
        "fn f(l: share Line) { both(l.a.share(), l.a.share()); }",
        "fn f(l: share Line) { let r := l.borrow(); l.b.x = 1; let v := r.a.x; }",
        "fn f(l: share Line) { var ra := l.a.share(); let rb := l.a.share(); ra.x = rb.x; }",
    ] {
        let codes = ownership(&format!("{DECLS} {source} fn main() {{}}"));
        assert!(codes.iter().any(|c| c == "BE005"), "{source}: {codes:?}");
    }
}

#[test]
fn chains_through_a_shared_prefix_only_conflict_at_the_leaf() {
    // `g.rows[0]` and `g.rows[1]` both go through `g.rows`; the intermediate
    // address is path computation and does not conflict with the other chain.
    for body in [
        "var r := g.rows[0].share(); g.rows[1][2] = 1; r[0] = 2;",
        "var r := g.rows[0].share(); g.tag = 1; r[0] = 2;",
        "let r := g.rows[1].borrow(); g.rows[0][0] += 1; let v := r[0] + g.rows[0][1];",
    ] {
        accepted(&format!("{GRID}{body}"));
    }
    for body in [
        "var r := g.rows[0].share(); g.rows[0][2] = 1; r[0] = 2;",
        "var i := 0; var r := g.rows[i].share(); g.rows[1][2] = 1; r[0] = 2;",
        "var r := g.rows[0].share(); g.rows = [[0, 0, 0], [0, 0, 0]]; r[0] = 2;",
        "var r := g.rows[0].share(); let q := g; r[0] = 2;",
    ] {
        rejected(&format!("{GRID}{body}"));
    }
}

#[test]
fn fixed_iteration_loan_covers_the_body_and_ends_on_exit() {
    accepted(
        "var grid := [[1, 2], [3, 4]]; \
         loop value in grid[0] { grid[1][0] = value; break; } \
         grid[0][0] = 7;",
    );
    accepted("let empty: array<u8, 0> = []; loop value in empty { let moved := empty; }");
    for control in ["break;", "continue;", "return;", "loop {}"] {
        rejected(&format!(
            "var array := [1, 2]; loop value in array {{ array[0] = value; {control} }}"
        ));
    }
    rejected("let array := [1]; loop value in array { let moved := array; break; }");
    let codes = ownership(
        "fn move_out(array: array<i32, 1>) -> array<i32, 1> { \
         loop value in array { return array; } array } fn main() {}",
    );
    assert!(codes.iter().any(|code| code == "BE005"), "{codes:?}");
}

#[test]
fn list_iteration_loan_covers_the_body_and_ends_on_exit() {
    accepted(
        "var items: List<u8> = []; items.push(1); \
         loop value in items { items.len(); items.get(0); break; } \
         items.push(2); let moved := items;",
    );
    for (action, control) in [
        ("items.push(value);", "break;"),
        ("items.pop();", "continue;"),
        ("items.clear();", "return;"),
        ("items = [];", "loop {}"),
        ("let moved := items;", "break;"),
        ("let exclusive := items.share(); exclusive.len();", "break;"),
    ] {
        rejected(&format!(
            "var items: List<u8> = []; loop value in items {{ {action} {control} }}"
        ));
    }
    rejected(
        "var items: List<u32> = []; var handle := items.share(); \
         loop value in handle { handle.push(value); break; }",
    );
    let codes = ownership(
        "use alloc::List; fn move_out(items: List<u32>) -> List<u32> { \
         loop value in items { return items; } items } fn main() {}",
    );
    assert!(codes.iter().any(|code| code == "BE005"), "{codes:?}");
}
