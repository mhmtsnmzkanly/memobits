//! H4: `Box<T>`.
//!
//! `use alloc::Box;`, `Box(value)`, `unbox(b)`, auto-deref for fields,
//! methods, indexing and `match`, recursive types through a box, boxes inside
//! every container, exact release under capped memory and the diagnostics.
//! Every positive program runs from source and as a standalone Wasm artifact.
use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new(source: &str) -> Self {
        Self::with(&[("main", source)], "")
    }

    fn with(modules: &[(&str, &str)], extra_manifest: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-h4-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            format!("[package]\nname='h4'\nentry='main::main'\n{extra_manifest}"),
        )
        .unwrap();
        for (name, source) in modules {
            fs::write(path.join(format!("src/{name}.mb")), source).unwrap();
        }
        Self(path)
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

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

fn rejects_with(f: &Fixture, code: &str, needle: &str) {
    let output = f.run(&["check", "--tests"]);
    let stderr = text(&output.stderr);
    assert!(!output.status.success(), "accepted");
    assert!(
        stderr.contains(code) && stderr.contains(needle),
        "expected {code} `{needle}`:\n{stderr}"
    );
}

/// Compile `source` and return stderr; `check` must fail with `code` and the
/// message must contain `needle`.
fn rejects(source: &str, code: &str, needle: &str) {
    rejects_with(&Fixture::new(source), code, needle);
}

/// `check`, `test` (expected count when nonzero), source `run` and standalone
/// Wasm `run`, each with empty stderr and the same `Result: i32(expected)`.
fn verify(f: &Fixture, tests: usize, expected: i64, label: &str) {
    let checked = f.run(&["check"]);
    assert!(
        checked.status.success(),
        "{label}: {}",
        text(&checked.stderr)
    );
    if tests > 0 {
        let report = f.run(&["test"]);
        let stdout = text(&report.stdout);
        assert!(
            report.status.success()
                && stdout.contains(&format!("test result: ok. {tests} passed; 0 failed")),
            "{label}: {stdout}{}",
            text(&report.stderr)
        );
    }
    let want = format!("Result: i32({expected})\n");
    let source_run = f.run(&["run"]);
    assert!(
        source_run.status.success() && source_run.stderr.is_empty(),
        "{label} source run: {}",
        text(&source_run.stderr)
    );
    assert_eq!(text(&source_run.stdout), want, "{label} (source)");
    let build = f.run(&["build", "--output", "h4.wasm"]);
    assert!(build.status.success(), "{label}: {}", text(&build.stderr));
    let wasm = f.run(&["run", "h4.wasm"]);
    assert!(
        wasm.status.success() && wasm.stderr.is_empty(),
        "{label} wasm run: {}",
        text(&wasm.stderr)
    );
    assert_eq!(text(&wasm.stdout), want, "{label} (wasm)");
}

fn single(source: &str, tests: usize, expected: i64, label: &str) {
    verify(&Fixture::new(source), tests, expected, label);
}

// ---------------------------------------------------------------------------
// Construction, ownership and auto-deref

#[test]
fn box_construction_fields_and_assignment_through_the_box() {
    single(
        r#"use alloc::Box;
type P { x: i32, y: i32 }
type Q { p: Box<P>, name: string }
fn make() -> Box<P> => Box(P { x: 1, y: 2 })
fn main() -> i32 {
    var b := Box(P { x: 40, y: 2 });
    b.x = 30;
    b.y += 5;
    let m := make();
    let p := unbox(b);
    let q := Q { p: Box(P { x: 3, y: 4 }), name: "hi" };
    let r := q.p.x + q.p.y;
    let n := Box(5);
    let k := unbox(n);
    p.x + p.y + m.x + r + k
}
"#,
        0,
        50,
        "construction",
    );
}

#[test]
fn methods_indexing_replace_and_swap_see_through_the_box() {
    single(
        r#"use alloc::Box;
type Counter { n: i32 }
extend Counter {
    fn value(borrow self) -> i32 { self.n }
    fn bump(share self) { self.n += 1; }
    fn done(self) -> i32 { self.n * 2 }
}
type S { a: Box<i32>, b: Box<i32> }
fn main() -> i32 {
    var c := Box(Counter { n: 1 });
    c.bump();
    c.bump();
    let g := c.value();
    let arr := Box([1, 2, 3]);
    let second := arr[1];
    var lb := Box(Counter { n: 5 });
    lb.n = 7;
    let old := replace(lb.n, 9);
    let d := c.done();
    var s := S { a: Box(1), b: Box(2) };
    swap(s.a, s.b);
    let previous := replace(s.a, Box(10));
    let swapped := unbox(previous) + unbox(replace(s.b, Box(0)));
    g + second + old + lb.n + d + swapped
}
"#,
        0,
        // 3 + 2 + 7 + 9 + 6 + (2 + 1)
        30,
        "methods",
    );
}

#[test]
fn boxes_hold_strings_lists_functions_enums_and_nest() {
    single(
        r#"use alloc::Box;
use alloc::List;
type Shape [Dot, Line(i32), Rect(i32, i32)]
type Labeled { text: string, n: i32 }
fn id<T>(x: T) -> T { x }
fn main() -> i32 {
    let hello := "hello".concat(" world");
    let s := Box(hello);
    let text := unbox(s);
    var inner: List<i32> = [];
    inner.push(1);
    inner.push(2);
    inner.push(3);
    let bl := Box(inner);
    let list := unbox(bl);
    let f := Box(fn(x: i32) -> i32 => x + 1);
    let call := unbox(f);
    let shapes := Box(Shape::Rect(3, 4));
    let area := match shapes { Rect(w, h) => w * h, Line(n) => n, Dot => 0 };
    let nested := Box(Box(Labeled { text: "t", n: 5 }));
    let g := id(Box(7));
    (text.len() + list.len()) as i32 + call(1) + area + nested.n + unbox(g)
}
"#,
        0,
        // 11 + 3 + 2 + 12 + 5 + 7
        40,
        "contents",
    );
}

#[test]
fn boxes_inside_containers_options_results_and_tuples() {
    single(
        r#"use alloc::Box;
use alloc::List;
type Node { val: i32, next: Box<Node>? }
type Pair { a: Box<string>, b: Box<List<i32>> }
fn total(n: borrow Node) -> i32 {
    match n.next {
        Some(rest) => n.val + total(rest.borrow()),
        None => n.val,
    }
}
fn pick(flag: bool) -> Box<i32> ! Error {
    if flag { Ok(Box(8)) } else { Ok(Box(9)) }
}
fn main() -> i32 {
    let third := Node { val: 3, next: None };
    let second := Node { val: 2, next: Some(Box(third)) };
    var first := Node { val: 1, next: Some(Box(second)) };
    first.val = 10;
    let t := total(first.borrow());
    let boxes := [Box(1), Box(2)];
    var list_of: List<Box<i32>> = [];
    list_of.push(Box(5));
    list_of.push(Box(6));
    let tuple := (Box(11), 4);
    let (left, right) := tuple;
    let r := match pick(true) { Ok(b) => unbox(b), Err(_) => 0 };
    t + list_of.len() as i32 + unbox(left) + right + r
}
"#,
        0,
        // 15 + 2 + 11 + 4 + 8
        40,
        "containers",
    );
}

// ---------------------------------------------------------------------------
// Recursive types: list and tree

const TREE: &str = r#"use alloc::Box;
type Tree [Leaf, Node(Box<Tree>, i32, Box<Tree>)]
fn insert(t: Tree, v: i32) -> Tree {
    match t {
        Leaf => Node(Box(Leaf), v, Box(Leaf)),
        Node(l, x, r) => {
            if v < x {
                Node(Box(insert(unbox(l), v)), x, r)
            } else {
                Node(l, x, Box(insert(unbox(r), v)))
            }
        }
    }
}
fn sum(t: borrow Tree) -> i32 {
    match t {
        Leaf => 0,
        Node(l, x, r) => sum(l.borrow()) + x + sum(r.borrow()),
    }
}
fn depth(t: borrow Tree) -> i32 {
    match t {
        Leaf => 0,
        Node(l, _, r) => {
            let a := depth(l.borrow());
            let b := depth(r.borrow());
            1 + if a > b { a } else { b }
        }
    }
}
fn leftmost(t: borrow Tree) -> i32 {
    match t {
        Node(Node(l, x, _), _, _) => x + leftmost(l.borrow()),
        Node(Leaf, x, _) => x,
        Leaf => 0,
    }
}
"#;

#[test]
fn binary_tree_insert_sum_depth_and_nested_patterns() {
    let source = format!(
        r#"{TREE}
test fn tree_shape() {{
    let t0 := insert(Tree::Leaf, 8);
    let t1 := insert(t0, 4);
    let t2 := insert(t1, 12);
    let t3 := insert(t2, 2);
    let t4 := insert(t3, 6);
    assert(sum(t4.borrow()) == 32);
    assert(depth(t4.borrow()) == 3);
    assert(leftmost(t4.borrow()) == 4 + 2);
}}
fn main() -> i32 {{
    let t0 := insert(Tree::Leaf, 8);
    let t1 := insert(t0, 4);
    let t2 := insert(t1, 12);
    let t3 := insert(t2, 2);
    let t4 := insert(t3, 6);
    sum(t4.borrow()) * 10 + depth(t4.borrow())
}}
"#
    );
    single(&source, 1, 323, "tree");
}

#[test]
fn linked_list_and_owned_match_consume_the_box() {
    single(
        r#"use alloc::Box;
type Cell [Nil, Cons(i32, Box<Cell>)]
fn build(n: i32) -> Cell {
    if n == 0 { Cell::Nil } else { Cell::Cons(n, Box(build(n - 1))) }
}
fn len(c: borrow Cell) -> i32 {
    match c {
        Nil => 0,
        Cons(_, rest) => 1 + len(rest.borrow()),
    }
}
fn total(c: Cell) -> i32 {
    match c {
        Nil => 0,
        Cons(v, rest) => v + total(unbox(rest)),
    }
}
fn consume(b: Box<Cell>) -> i32 {
    match b {
        Nil => 0,
        Cons(v, rest) => v + total(unbox(rest)),
    }
}
fn main() -> i32 {
    let c := build(200);
    let n := len(c.borrow());
    let t := total(c);
    let owned := Box(build(10));
    n * 1000 + t + consume(owned)
}
"#,
        0,
        // 200 * 1000 + 20100 + 55
        220155,
        "list",
    );
}

#[test]
fn deep_recursion_stays_within_the_stack() {
    single(
        r#"use alloc::Box;
type Cell [Nil, Cons(i32, Box<Cell>)]
fn build(n: i32) -> Cell {
    if n == 0 { Cell::Nil } else { Cell::Cons(n, Box(build(n - 1))) }
}
fn len(c: borrow Cell) -> i32 {
    match c {
        Nil => 0,
        Cons(_, rest) => 1 + len(rest.borrow()),
    }
}
fn main() -> i32 {
    let c := build(400);
    len(c.borrow())
}
"#,
        0,
        400,
        "deep",
    );
}

// ---------------------------------------------------------------------------
// Capped memory: build and drop trees repeatedly

const ITERATIONS: u32 = 4_096;

fn read_uleb(bytes: &[u8], cursor: &mut usize) -> u32 {
    let mut value = 0;
    let mut shift = 0;
    loop {
        let byte = bytes[*cursor];
        *cursor += 1;
        value |= u32::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return value;
        }
        shift += 7;
        assert!(shift < 35, "invalid Wasm LEB128");
    }
}

fn write_uleb(mut value: u32, output: &mut Vec<u8>) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        output.push(byte);
        if value == 0 {
            break;
        }
    }
}

/// Lower the memory maximum to the initial size plus one page, so repeated
/// iterations must reuse released blocks.
fn cap_memory(bytes: &[u8]) -> (Vec<u8>, u32, u32) {
    assert_eq!(&bytes[..8], b"\0asm\x01\0\0\0");
    let mut module = bytes[..8].to_vec();
    let mut section_start = 8;
    let mut result = None;
    while section_start < bytes.len() {
        let id = bytes[section_start];
        let mut header_cursor = section_start + 1;
        let payload_len = read_uleb(bytes, &mut header_cursor) as usize;
        let payload_start = header_cursor;
        let section_end = payload_start + payload_len;
        if id != 5 {
            module.extend_from_slice(&bytes[section_start..section_end]);
        } else {
            let mut cursor = payload_start;
            assert_eq!(read_uleb(bytes, &mut cursor), 1, "expected one memory");
            let limits = read_uleb(bytes, &mut cursor);
            assert_ne!(limits & 1, 0, "expected a declared maximum");
            let initial = read_uleb(bytes, &mut cursor);
            let maximum_start = cursor;
            let old_maximum = read_uleb(bytes, &mut cursor);
            let new_maximum = initial + 1;
            assert!(new_maximum <= old_maximum);
            let mut payload = bytes[payload_start..maximum_start].to_vec();
            write_uleb(new_maximum, &mut payload);
            payload.extend_from_slice(&bytes[cursor..section_end]);
            module.push(id);
            write_uleb(payload.len() as u32, &mut module);
            module.extend_from_slice(&payload);
            result = Some((initial, new_maximum));
        }
        section_start = section_end;
    }
    let (initial, maximum) = result.expect("Wasm memory section");
    (module, initial, maximum)
}

fn stress_program(keep_declaration: &str, keep_statement: &str) -> String {
    format!(
        r#"{TREE}
use alloc::List;
fn grow(seed: i32) -> Tree {{
    let t0 := insert(Tree::Leaf, 8 + seed % 3);
    let t1 := insert(t0, 4);
    let t2 := insert(t1, 12);
    let t3 := insert(t2, 2);
    let t4 := insert(t3, 6);
    let t5 := insert(t4, 10);
    let t6 := insert(t5, 14);
    insert(t6, 1)
}}
fn main() -> i32 {{
    var iteration: i32 = 0;
    var total: i32 = 0;
    {keep_declaration}
    loop {{
        if iteration == {ITERATIONS} {{ break; }}
        let t := grow(iteration);
        total += sum(t.borrow()) + depth(t.borrow());
        {keep_statement}
        iteration += 1;
    }}
    total
}}
"#
    )
}

fn stress_expected() -> i64 {
    // The tree holds 8 + seed % 3, 4, 12, 2, 6, 10, 14 and 1; its depth is 4
    // for seed % 3 == 0, 4 for 1 and 4 for 2 (8, 9, 10 stay on the same shape).
    let mut total = 0i64;
    for seed in 0..i64::from(ITERATIONS) {
        let root = 8 + seed % 3;
        let sum = root + 4 + 12 + 2 + 6 + 10 + 14 + 1;
        // Insert order: root, 4, 12, 2, 6, 10, 14, 1. For root 10 the value 10
        // goes right of 4's sibling differently, so compute the depth by
        // simulation.
        let mut nodes: Vec<(i64, Option<usize>, Option<usize>)> = vec![(root, None, None)];
        for value in [4, 12, 2, 6, 10, 14, 1] {
            let mut at = 0usize;
            loop {
                let go_left = value < nodes[at].0;
                let next = if go_left { nodes[at].1 } else { nodes[at].2 };
                match next {
                    Some(child) => at = child,
                    None => {
                        nodes.push((value, None, None));
                        let index = nodes.len() - 1;
                        if go_left {
                            nodes[at].1 = Some(index);
                        } else {
                            nodes[at].2 = Some(index);
                        }
                        break;
                    }
                }
            }
        }
        fn height(nodes: &[(i64, Option<usize>, Option<usize>)], at: Option<usize>) -> i64 {
            match at {
                None => 0,
                Some(index) => 1 + height(nodes, nodes[index].1).max(height(nodes, nodes[index].2)),
            }
        }
        total += sum + height(&nodes, Some(0));
    }
    total
}

fn run_capped(source: &str) -> (Fixture, Output, Option<(u32, u32)>) {
    let f = Fixture::new(source);
    let build = f.run(&["build", "--output", "stress.wasm"]);
    assert!(build.status.success(), "{}", text(&build.stderr));
    let path = f.0.join("stress.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&path).unwrap());
    fs::write(&path, capped).unwrap();
    let output = f.run(&["run", "stress.wasm"]);
    (f, output, Some((initial, maximum)))
}

#[test]
fn building_and_dropping_trees_releases_exactly_under_the_cap() {
    let source = stress_program("", "");
    let f = Fixture::new(&source);
    let expected = stress_expected();
    let source_run = f.run(&["run"]);
    assert!(
        source_run.status.success() && source_run.stderr.is_empty(),
        "source run: {}",
        text(&source_run.stderr)
    );
    assert_eq!(
        text(&source_run.stdout),
        format!("Result: i32({expected})\n")
    );
    let (_f, output, limits) = run_capped(&source);
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "capped run failed: {}",
        text(&output.stderr)
    );
    assert_eq!(text(&output.stdout), format!("Result: i32({expected})\n"));
    let (initial, maximum) = limits.unwrap();
    assert_eq!(maximum, initial + 1);
}

#[test]
fn mutation_check_keeping_trees_exhausts_the_capped_memory() {
    // The same program, but every round keeps its tree in a List that is never
    // emptied (a release removed from the clean program): the cap must trap.
    let source = stress_program("var kept: List<Tree> = [];", "kept.push(t);");
    let (_f, output, _) = run_capped(&source);
    assert!(!output.status.success(), "{output:?}");
    assert!(
        text(&output.stderr).contains("guest heap allocation failed"),
        "{}",
        text(&output.stderr)
    );
}

#[test]
fn box_contents_and_owned_matches_release_exactly_under_the_cap() {
    let source = format!(
        r#"use alloc::Box;
use alloc::List;
type Item {{ text: string, n: i32 }}
type Wrap [Empty, Full(Box<Item>, Box<List<i32>>)]
fn take(w: Wrap) -> i32 {{
    match w {{
        Empty => 0,
        Full(item, list) => {{
            let inner := unbox(item);
            let numbers := unbox(list);
            (inner.text.len() + numbers.len()) as i32 + inner.n
        }}
    }}
}}
fn peek(w: borrow Wrap) -> i32 {{
    match w {{
        Empty => 0,
        Full(item, _) => item.n,
    }}
}}
fn mk(seed: i32) -> Wrap {{
    let text := "{text}".concat("");
    var numbers: List<i32> = [];
    numbers.push(seed);
    numbers.push(2);
    Wrap::Full(Box(Item {{ text: text, n: 3 }}), Box(numbers))
}}
fn spare() -> i32 {{
    let text := "{text}".concat("");
    let dropped := Box(Item {{ text: text, n: 9 }});
    dropped.n
}}
fn round(seed: i32) -> i32 {{
    let w := mk(seed);
    let p := peek(w.borrow());
    let w2 := mk(seed + 1);
    let nested := Box(Box(Item {{ text: "static", n: 1 }}));
    p + take(w) + take(w2) + spare() + nested.n
}}
fn main() -> i32 {{
    var i: i32 = 0;
    var total: i32 = 0;
    loop {{
        if i == {ITERATIONS} {{ break; }}
        total += round(i % 7);
        i += 1;
    }}
    total
}}
"#,
        text = "x".repeat(512)
    );
    // peek 3, take(w) 512 + 2 + 3, take(w2) 512 + 2 + 3, spare 9, nested 1
    let per_round = 3 + 517 + 517 + 9 + 1;
    let f = Fixture::new(&source);
    let source_run = f.run(&["run"]);
    assert!(
        source_run.status.success() && source_run.stderr.is_empty(),
        "source run: {}",
        text(&source_run.stderr)
    );
    let expected = i64::from(ITERATIONS) * per_round;
    assert_eq!(
        text(&source_run.stdout),
        format!("Result: i32({expected})\n")
    );
    let (_f, output, _) = run_capped(&source);
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "capped run failed: {}",
        text(&output.stderr)
    );
    assert_eq!(text(&output.stdout), format!("Result: i32({expected})\n"));
}

// ---------------------------------------------------------------------------
// Diagnostics

#[test]
fn box_needs_its_import() {
    rejects(
        "type P { x: i32 }\nfn make() -> Box<P> => Box(P { x: 1 })\nfn main() {}\n",
        "NE003",
        "unknown type 'Box'",
    );
    rejects(
        "type P { x: i32 }\nfn make() -> Box<P> => Box(P { x: 1 })\nfn main() {}\n",
        "NE003",
        "add `use alloc::Box;` to use Box",
    );
    rejects(
        "type P { x: i32 }\nfn main() { let b := Box(P { x: 1 }); }\n",
        "NE001",
        "add `use alloc::Box;` to construct a Box",
    );
}

#[test]
fn box_is_unavailable_without_the_alloc_layer() {
    let f = Fixture::with(
        &[("main", "use alloc::Box;\nfn main() -> i32 { 1 }\n")],
        "[build]\nalloc = false\n",
    );
    rejects_with(&f, "ME012", "the project sets `[build] alloc = false`");
}

#[test]
fn a_user_type_named_box_still_works_without_the_import() {
    single(
        "type Box<T> { value: T }\nfn main() -> i32 {\n    let b := Box<i32> { value: 41 };\n    b.value + 1\n}\n",
        0,
        42,
        "user Box",
    );
}

#[test]
fn recursion_is_rejected_unless_it_goes_through_a_box() {
    rejects(
        "type A { a: A }\nfn main() {}\n",
        "TE026",
        "recursive struct: 'A' contains 'A' by value",
    );
    rejects(
        "type L [Nil, Cons(i32, L)]\nfn main() {}\n",
        "TE026",
        "contains 'L' by value",
    );
    rejects(
        "type A { b: B }\ntype B { a: A }\nfn main() {}\n",
        "TE026",
        "by value",
    );
    // Through a box, an Option of a box or a List of boxes it is fine.
    single(
        r#"use alloc::Box;
use alloc::List;
type A { b: Box<A>?, kids: List<Box<A>>, n: i32 }
fn main() -> i32 {
    let leaf := A { b: None, kids: [], n: 1 };
    let top := A { b: Some(Box(leaf)), kids: [], n: 2 };
    top.n
}
"#,
        0,
        2,
        "recursion",
    );
}

#[test]
fn ownership_errors_through_boxes() {
    rejects(
        "use alloc::Box;\ntype P { x: i32 }\nfn main() -> i32 {\n    let b := Box(P { x: 1 });\n    let c := b;\n    b.x\n}\n",
        "BE001",
        "'b' is unavailable after a move",
    );
    rejects(
        "use alloc::Box;\ntype T { l: Box<i32>, k: i32 }\nfn main() -> i32 {\n    let t := T { l: Box(1), k: 2 };\n    let x := t.l;\n    t.k\n}\n",
        "TE022",
        "cannot be moved out by field access",
    );
    rejects(
        "use alloc::Box;\ntype T { s: string }\nfn main() -> i32 {\n    let b := Box(T { s: \"a\" });\n    let s := b.s;\n    1\n}\n",
        "TE022",
        "cannot be moved out by field access",
    );
    rejects(
        "use alloc::Box;\ntype P { x: i32 }\nfn main() -> i32 {\n    let b := Box(P { x: 1 });\n    b.x = 5;\n    b.x\n}\n",
        "TE004",
        "cannot assign to a value inside an immutable Box binding 'b'",
    );
    rejects(
        "use alloc::Box;\nfn main() -> i32 {\n    let n := 5;\n    unbox(n)\n}\n",
        "TE007",
        "unbox() requires an owned Box",
    );
    rejects(
        "use alloc::Box;\ntype P { x: i32 }\nfn main() -> i32 {\n    let p := P { x: 1 };\n    let b := Box(p.borrow());\n    1\n}\n",
        "TE017",
        "Box contents cannot be references",
    );
    rejects(
        "use alloc::Box;\ntype P { x: i32 }\nextend P { fn eat(self) -> i32 { self.x } }\nfn main() -> i32 {\n    let b := Box(Box(P { x: 1 }));\n    b.eat()\n}\n",
        "TE017",
        "consumes one Box level",
    );
}

#[test]
fn patterns_inside_a_box_need_an_in_place_match() {
    rejects(
        r#"use alloc::Box;
type Tree [Leaf, Node(Box<Tree>, i32)]
fn depth(t: Tree) -> i32 {
    match t {
        Node(Node(_, x), _) => x,
        _ => 0,
    }
}
fn main() {}
"#,
        "TE017",
        "a pattern inside a Box needs an in-place match",
    );
}

#[test]
fn reassignment_drop_and_early_return_release_exactly_under_the_cap() {
    let source = format!(
        r#"use alloc::Box;
use alloc::List;
type S {{ a: Box<string>, n: i32 }}
fn early(flag: bool) -> i32 {{
    let b := Box(5);
    let c := Box(6);
    if flag {{ return unbox(b); }}
    unbox(c)
}}
fn round() -> i32 {{
    var b := Box(1);
    b = Box(2);
    let one := unbox(b);
    let text := "{text}".concat("");
    var s := S {{ a: Box(text), n: 1 }};
    s.a = Box("z");
    var l: List<Box<i32>> = [];
    l.push(Box(3));
    l[0] = Box(4);
    let d := Box(9);
    drop(d);
    let e := early(true) + early(false);
    one + s.n + l.len() as i32 + e
}}
fn main() -> i32 {{
    var i: i32 = 0;
    var total: i32 = 0;
    loop {{
        if i == {ITERATIONS} {{ break; }}
        total += round();
        i += 1;
    }}
    total
}}
"#,
        text = "x".repeat(512)
    );
    let expected = i64::from(ITERATIONS) * 15;
    let f = Fixture::new(&source);
    let source_run = f.run(&["run"]);
    assert!(
        source_run.status.success() && source_run.stderr.is_empty(),
        "source run: {}",
        text(&source_run.stderr)
    );
    assert_eq!(
        text(&source_run.stdout),
        format!("Result: i32({expected})\n")
    );
    let (_f, output, _) = run_capped(&source);
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "capped run failed: {}",
        text(&output.stderr)
    );
    assert_eq!(text(&output.stdout), format!("Result: i32({expected})\n"));
}

#[test]
fn live_loans_block_moving_or_writing_a_box() {
    rejects(
        "use alloc::Box;\ntype P { x: i32 }\nfn main() -> i32 {\n    let b := Box(P { x: 1 });\n    let r := b.borrow();\n    let p := unbox(b);\n    r.x + p.x\n}\n",
        "BE005",
        "cannot move `b` while it is borrowed",
    );
    rejects(
        "use alloc::Box;\ntype P { x: i32 }\nfn main() -> i32 {\n    var b := Box(P { x: 1 });\n    let r := b.borrow();\n    b.x = 4;\n    r.x\n}\n",
        "BE005",
        "cannot write this value while it is borrowed",
    );
}

// ---------------------------------------------------------------------------
// H4b: release of recursive owners does not recurse per node

const GROW_LIST: &str = r#"use alloc::Box;
type Cell [Nil, Cons(i32, Box<Cell>)]
type Holder { head: Cell }
fn grow(h: share Holder, n: i32) {
    var i: i32 = 0;
    loop {
        if i == n { break; }
        h.head = Cell::Cons(i, Box(replace(h.head, Cell::Nil)));
        i += 1;
    }
}
"#;

#[test]
fn dropping_a_million_node_list_neither_traps_nor_recurses() {
    single(
        &format!(
            r#"{GROW_LIST}
fn round() -> i32 {{
    var h := Holder {{ head: Cell::Nil }};
    grow(h.share(), 1000000);
    match h.head {{
        Nil => 0,
        Cons(v, _) => v,
    }}
}}
fn main() -> i32 {{
    // Two rounds: the second reuses the million blocks the first released.
    round() - 999999 + round() - 999999 + 42
}}
"#
        ),
        0,
        42,
        "million list",
    );
}

const SHAPES: &str = r#"use alloc::Box;
use alloc::List;
type Tree [Leaf, Node(Box<Tree>, i32, Box<Tree>)]
type Holder { t: Tree }
type Kid { name: string, kids: List<Kid> }
type KidHolder { k: Kid }
type A [AEnd, AMore(string, Box<B>)]
type B [BEnd, BMore(i32, Box<A>, string)]
type AHolder { a: A }
fn left(n: i32) -> i32 {
    var h := Holder { t: Tree::Leaf };
    var i: i32 = 0;
    loop {
        if i == n { break; }
        h.t = Tree::Node(Box(replace(h.t, Tree::Leaf)), i, Box(Tree::Leaf));
        i += 1;
    }
    i
}
fn right(n: i32) -> i32 {
    var h := Holder { t: Tree::Leaf };
    var i: i32 = 0;
    loop {
        if i == n { break; }
        h.t = Tree::Node(Box(Tree::Leaf), i, Box(replace(h.t, Tree::Leaf)));
        i += 1;
    }
    i
}
fn kids(n: i32) -> i32 {
    var k := KidHolder { k: Kid { name: "root", kids: [] } };
    var i: i32 = 0;
    loop {
        if i == n { break; }
        let old := replace(k.k, Kid { name: "kid", kids: [] });
        k.k.kids.push(old);
        i += 1;
    }
    i
}
fn mutual(n: i32) -> i32 {
    var h := AHolder { a: A::AEnd };
    var i: i32 = 0;
    loop {
        if i == n { break; }
        let b := B::BMore(i, Box(replace(h.a, A::AEnd)), "q");
        h.a = A::AMore("z", Box(b));
        i += 1;
    }
    i
}
"#;

// Each shape runs in its own program: the allocator reuses released blocks
// first-fit, so mixing block sizes in one run would only measure its scan.
#[test]
fn dropping_degenerate_trees_and_other_recursive_shapes_is_iterative() {
    for (call, expected, label) in [
        ("left(100000)", 100_000, "left spine"),
        ("right(100000)", 100_000, "right spine"),
        ("kids(200000)", 200_000, "list of children"),
        ("mutual(100000)", 100_000, "mutual recursion"),
    ] {
        single(
            &format!("{SHAPES}fn main() -> i32 {{\n    {call}\n}}\n"),
            0,
            expected,
            label,
        );
    }
}

#[test]
fn a_balanced_tree_drops_after_a_deep_walk() {
    single(
        &format!(
            r#"{TREE}
fn full(depth: i32, base: i32) -> Tree {{
    if depth == 0 {{ Tree::Leaf }} else {{
        Tree::Node(Box(full(depth - 1, base * 2)), base, Box(full(depth - 1, base * 2 + 1)))
    }}
}}
fn count(t: borrow Tree) -> i32 {{
    match t {{
        Leaf => 0,
        Node(l, _, r) => 1 + count(l.borrow()) + count(r.borrow()),
    }}
}}
fn main() -> i32 {{
    let t := full(16, 1);
    count(t.borrow()) - 65535 + 5
}}
"#
        ),
        0,
        5,
        "balanced",
    );
}

fn long_list_program(keep_declaration: &str, keep_statement: &str) -> String {
    format!(
        r#"{GROW_LIST}
use alloc::List;
fn main() -> i32 {{
    var total: i32 = 0;
    var round: i32 = 0;
    {keep_declaration}
    loop {{
        if round == 300 {{ break; }}
        var h := Holder {{ head: Cell::Nil }};
        grow(h.share(), 1500);
        total += match h.head {{
            Nil => 0,
            Cons(v, _) => v,
        }};
        {keep_statement}
        round += 1;
    }}
    total
}}
"#
    )
}

#[test]
fn long_lists_build_and_drop_repeatedly_under_the_cap() {
    let source = long_list_program("", "");
    let (_f, output, limits) = run_capped(&source);
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "capped run failed: {}",
        text(&output.stderr)
    );
    assert_eq!(text(&output.stdout), "Result: i32(449700)\n");
    let (initial, maximum) = limits.unwrap();
    assert_eq!(maximum, initial + 1);
}

#[test]
fn mutation_check_keeping_long_lists_exhausts_the_capped_memory() {
    // The released lists are kept instead (a drop removed): the cap must trap.
    let source = long_list_program("var kept: List<Holder> = [];", "kept.push(h);");
    let (_f, output, _) = run_capped(&source);
    assert!(!output.status.success(), "{output:?}");
    assert!(
        text(&output.stderr).contains("guest heap allocation failed"),
        "{}",
        text(&output.stderr)
    );
}

// ---------------------------------------------------------------------------
// H4b: built-in String and List methods see through a box

#[test]
fn builtin_string_and_list_methods_auto_deref_through_boxes() {
    single(
        r#"use alloc::Box;
use alloc::List;
type Bag { items: List<i32>, name: string }
fn sum(b: borrow Box<List<i32>>) -> i32 {
    var total: i32 = 0;
    var i: u32 = 0;
    loop {
        if i == b.len() { break; }
        total += b[i];
        i += 1;
    }
    total
}
fn grow(b: share Box<List<i32>>) { b.push(100); }
fn main() -> i32 {
    var b: Box<List<i32>> = Box([1, 2, 3]);
    b.push(4);
    let n := b.len();
    let s := Box("héllo");
    let sl := s.len();
    let has := b.contains(3);
    let at := match b.index_of(3) { Some(v) => v, None => 99 };
    let g := match b.get(1) { Some(v) => v, None => 0 };
    grow(b.share());
    let p := match b.pop() { Some(v) => v, None => 0 };
    var bag := Box(Bag { items: [], name: "x" });
    bag.items.push(5);
    bag.items.push(6);
    let k := bag.items.len() + bag.name.len();
    let boundary := s.is_char_boundary(2);
    let first := match s.byte_at(0) { Some(v) => v.to_u32(), None => 0 };
    var cleared: Box<List<i32>> = Box([7, 8]);
    cleared.clear();
    let kept := cleared.len();
    if has && !boundary && first == 104 {
        n as i32 * 1000 + sl as i32 * 100 + g * 10 + p + k as i32 + sum(b.borrow())
            + at as i32 * 10000 + kept as i32
    } else { 0 }
}
"#,
        0,
        // n 4, sl 6 ("héllo"), g 2, p 100, k 3, sum 10, at 2, kept 0
        24733,
        "builtin methods through a box",
    );
}

#[test]
fn builtin_methods_through_a_box_keep_the_write_rules() {
    rejects(
        r#"use alloc::Box;
use alloc::List;
fn main() {
    let b: Box<List<i32>> = Box([1, 2, 3]);
    b.push(4);
}
"#,
        "TE017",
        "push() requires a mutable List local",
    );
    rejects(
        r#"use alloc::Box;
use alloc::List;
fn make() -> Box<List<i32>> { Box([1]) }
fn main() {
    let n := make().len();
}
"#,
        "TE017",
        "a method through a Box needs the box in a named local",
    );
}
