//! F4: whole-owner local reassignment (`x = value`), const generic parameters
//! as values, method-level type parameters and `where` bounds on type
//! declarations. Every positive program runs from source and as a standalone
//! Wasm artifact.
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
            "memobits-f4-{}-{}",
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

/// Lower this test artifact's memory maximum while preserving every other
/// section. The extra page permits the first String blocks and then forces
/// repeated iterations to reuse released blocks.
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
        assert!(section_end <= bytes.len(), "truncated Wasm section");
        if id != 5 {
            module.extend_from_slice(&bytes[section_start..section_end]);
        } else {
            assert!(result.is_none(), "unexpected second Wasm memory section");
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
            // Replace only the maximum LEB, retaining any remaining memories.
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

fn build_wasm(f: &Fixture, name: &str) -> PathBuf {
    let build = f.run(&["build", "--output", name]);
    assert!(
        build.status.success(),
        "build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    f.0.join(name)
}

fn assert_capped_memory(wasm_path: &PathBuf, initial: u32, maximum: u32) {
    let memory = wasmparser::Parser::new(0)
        .parse_all(&fs::read(wasm_path).unwrap())
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .expect("Wasm memory section")
        .unwrap();
    assert_eq!(memory.initial, u64::from(initial));
    assert_eq!(memory.maximum, Some(u64::from(maximum)));
}

fn project(f: &Fixture, name: &str, source: &str) {
    f.write(
        "project.toml",
        &format!("[package]\nname='{name}'\nentry='main::main'\n[build]\nstack_size=4096\n"),
    );
    f.write("src/main.mb", source);
}

fn run_source_and_wasm(f: &Fixture, artifact: &str, source_out: &[u8], wasm_out: &[u8]) {
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "source failed: {}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, source_out);
    build_wasm(f, artifact);
    let wasm = f.run(&["run", artifact]);
    assert!(
        wasm.status.success(),
        "Wasm failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, wasm_out);
}

fn rejects(f: &Fixture, source: &str, code: &str, text: &str) {
    f.write("src/main.mb", source);
    let check = f.run(&["check"]);
    assert!(!check.status.success(), "expected {code} for:\n{source}");
    let stderr = String::from_utf8_lossy(&check.stderr);
    assert!(stderr.contains(code), "expected {code}, got: {stderr}");
    assert!(stderr.contains(text), "expected `{text}`, got: {stderr}");
}

const OWNER_KINDS: &str = r####"use alloc::Box;
use alloc::List;
type Label { text: string, n: u32 }
type Tok [ Word(string), Num(u32) ]
type Tree [ Leaf(u32), Node(Box<Tree>, Box<Tree>) ]
fn hs(a: string) -> string { let r := a.concat("!"); r }
fn add_const(k: u32) -> fn(u32) -> u32 { fn(x: u32) -> u32 => x + k }
fn counter(start: u32) -> var fn() -> u32 {
    var c := start;
    fn() -> u32 { c += 1; c }
}
fn weight(t: borrow Tree) -> u32 {
    match t {
        Tree::Leaf(n) => n,
        Tree::Node(l, r) => weight(l.borrow()) + weight(r.borrow()),
    }
}
fn pair(a: string, n: u32) -> (string, u32) { (a, n) }
fn set_label(l: share Label, v: Label) -> u32 { l = v; l.n + l.text.len() }
fn set_list(l: share List<string>, v: List<string>) -> u32 { l = v; l.len() }
fn main() -> u32 {
    // struct with a String: "bb!" (3) + n 2
    let a := hs("a");
    var l := Label { text: a, n: 1 };
    let b := hs("bb");
    l = Label { text: b, n: 2 };
    // anonymous record
    let r1 := hs("r");
    var rec := { name: r1, id: 7 };
    let r2 := hs("rrr");
    rec = { name: r2, id: 9 };
    // tuple "zzzz!" (5) + 3
    let t1 := hs("x");
    var tp := pair(t1, 1);
    let t2 := hs("zzzz");
    tp = pair(t2, 3);
    // enum payload: Word -> Num(4), then back to Word("w!")
    let e1 := hs("word");
    var tok := Tok::Word(e1);
    tok = Tok::Num(4);
    let n1 := match tok { Tok::Word(s) => s.len(), Tok::Num(n) => n };
    let e2 := hs("w");
    tok = Tok::Word(e2);
    let n2 := match tok { Tok::Word(s) => s.len(), Tok::Num(n) => n };
    // boxed recursive enum
    var tree: Tree = Tree::Leaf(1);
    tree = Tree::Node(Box(Tree::Leaf(2)), Box(Tree::Leaf(3)));
    // array of strings
    let s1 := hs("a");
    let s2 := hs("b");
    var arr: array<string, 2> = [s1, s2];
    let s3 := hs("cc");
    let s4 := hs("ddd");
    arr = [s3, s4];
    // list of strings
    let q1 := hs("q");
    var ls: List<string> = [q1];
    let q2 := hs("x");
    let q3 := hs("y");
    ls = [q2, q3];
    // Box<u32> and List<u32>
    var bx: Box<u32> = Box(5);
    bx = Box(6);
    var nums: List<u32> = [1, 2];
    nums = [3, 4, 5];
    // function values: plain, capturing, var fn
    var f: fn(u32) -> u32 = add_const(1);
    f = add_const(10);
    var c := counter(100);
    c = counter(200);
    // share parameters
    let m0 := hs("m");
    var m := Label { text: m0, n: 1 };
    let m1 := hs("zz");
    let via_label := set_label(m.share(), Label { text: m1, n: 40 });
    let w0 := hs("w");
    var words: List<string> = [w0];
    let w1 := hs("u");
    let w2 := hs("v");
    let w3 := hs("t");
    let repl: List<string> = [w1, w2, w3];
    let via_list := set_list(words.share(), repl);
    l.text.len() + l.n + rec.name.len() + tp.0.len() + tp.1 + n1 + n2
        + weight(tree.borrow()) + arr[0].len() + arr[1].len() + ls.len() + ls[1].len()
        + unbox(bx) + nums.len() + f(1) + c() + via_label
        + via_list
}
"####;

const LOOPS: &str = r####"use alloc::List;
type Label { text: string, n: u32 }
fn hs(a: string) -> string { let r := a.concat("!"); r }
fn combine(acc: Label, x: u32) -> Label {
    let t := acc.text.concat("+");
    Label { text: t, n: acc.n + x }
}
fn peek(old: borrow Label, x: u32) -> Label {
    let t := old.text.concat("-");
    Label { text: t, n: old.n + x }
}
fn pair(a: string, n: u32) -> (string, u32) { (a, n) }
fn step(t: (string, u32)) -> (string, u32) {
    let (s, n) := t;
    let s2 := s.concat("*");
    (s2, n + 1)
}
fn push_one(xs: List<string>, s: string) -> List<string> {
    var out := xs;
    out.push(s);
    out
}
fn compose(f: fn(u32) -> u32, k: u32) -> fn(u32) -> u32 { fn(x: u32) -> u32 => f(x) + k }
fn base(x: u32) -> u32 { x }
fn first_over(limit: u32) -> u32 {
    let a := hs("a");
    var acc := Label { text: a, n: 0 };
    var i: u32 = 0;
    loop {
        let t := hs("t");
        let next := Label { text: t, n: i };
        acc = { if i == limit { return acc.n; } next };
        i += 1;
        if i == 100 { break; }
    }
    acc.n
}
fn main() -> u32 {
    let a := hs("a");
    var acc := Label { text: a, n: 0 };
    loop i in 0..5 { acc = combine(acc, 2); }
    let b := hs("b");
    var seen := Label { text: b, n: 0 };
    loop i in 0..3 { seen = peek(seen.borrow(), 1); }
    let t0 := hs("t");
    var tp := pair(t0, 0);
    loop i in 0..4 { tp = step(tp); }
    var ls: List<string> = [];
    loop i in 0..3 {
        let s := hs("s");
        ls = push_one(ls, s);
    }
    var f: fn(u32) -> u32 = base;
    loop i in 0..4 { f = compose(f, 3); }
    acc.n + acc.text.len() + seen.n + seen.text.len() + tp.1 + tp.0.len() + ls.len()
        + f(1) + first_over(3) + first_over(500)
}
"####;

const EDGES: &str = r####"use alloc::List;
type Label { text: string, n: u32 }
fn hs(a: string) -> string { let r := a.concat("!"); r }
fn mk(n: u32) -> Label { let t := hs("t"); Label { text: t, n: n } }
fn eat(l: Label) -> u32 { l.n }
fn main() -> u32 {
    var l := mk(1);
    let n := eat(l);
    l = mk(5);
    var s := mk(7);
    s = s;
    var k := Label { text: "z", n: 1 };
    let t := hs("abc");
    let src := Label { text: t, n: 10 };
    k = src;
    var xs: List<string> = [];
    xs = xs;
    n + l.n + s.n + s.text.len() + k.n + k.text.len() + xs.len()
}
"####;

const CONST_VALUES: &str = r####"type Grid<T, const W: u32, const H: u32> { cells: array<T, 4> } extend {
    fn area(borrow self) -> u32 { W * H }
    fn wide(borrow self) -> u64 { W as u64 + 100 }
    fn label(borrow self) -> u32 { let s := "{W}x{H}"; s.len() }
}
fn take(x: u32) -> u32 { x + 1 }
fn sum<const N: u32>(a: borrow array<u32, N>) -> u32 {
    var s: u32 = 0;
    loop i in 0..N { s += a[i]; }
    loop i in 0..=N { s += 1; }
    s
}
fn fill<const N: u32>(x: u32) -> array<u32, N> { [x; N] }
fn shape<const N: u32>(a: borrow array<u32, N>) -> u32 {
    let narrow: u8 = N as u8;
    let signed: i64 = N as i64;
    let real: f64 = N as f64;
    let big: bool = N > 2 && N != 7 && N >= 3 && N <= 9;
    let sq := N * N - 1;
    let f := fn(x: u32) -> u32 => x + N;
    let text := "N={N}";
    take(N) + sq + (if big { 100 } else { 0 }) + narrow as u32 + signed as u32 + real as u32 + f(1) + text.len()
}
fn main() -> u32 {
    let a: array<u32, 3> = [1, 2, 3];
    let b: array<u32, 5> = [1, 1, 1, 1, 1];
    let c: array<u32, 3> = [0, 0, 0];
    let d: array<u32, 5> = [0, 0, 0, 0, 0];
    let g := Grid<u32, 2, 3> { cells: [1, 2, 3, 4] };
    let e: array<u32, 4> = fill(9);
    sum(a.borrow()) * 1000000 + sum(b.borrow()) * 10000 + shape(c.borrow()) * 100 + shape(d.borrow())
        + g.area() + g.wide() as u32 + g.label() + e[3]
}
"####;

const METHOD_PARAMETERS: &str = r####"use alloc::List;
interface Weigh { fn weigh(borrow self) -> u32; }
type Crate { n: u32 }
extend Crate of Weigh { fn weigh(borrow self) -> u32 { self.n } }
type Wrap<T> { v: T } extend {
    fn pair<U>(self, other: U) -> (T, U) { (self.v, other) }
    fn map<U>(self, f: fn(T) -> U) -> Wrap<U> { Wrap<U> { v: f(self.v) } }
    fn total<U>(borrow self, other: borrow U) -> u32 where U: Weigh { other.weigh() of Weigh + 1 }
    fn pick<U>(self, a: U, b: U, first: bool) -> U { if first { a } else { b } }
    fn spread<const K: u32>(borrow self, a: borrow array<u32, K>) -> u32 { K * 2 + a[0] }
}
type Plain { k: u32 } extend {
    fn echo<T>(self, x: T) -> T { x }
    fn both<A, B>(borrow self, a: A, b: B) -> (A, B) { (a, b) }
}
type Named { name: string } extend {
    fn tag<T>(borrow self, x: T) -> (u32, T) { (self.name.len(), x) }
    fn shout<T>(share self, x: T) -> T { self.name = self.name.concat("!"); x }
}
fn main() -> u32 {
    let w := Wrap<u32> { v: 4 };
    let p := w.pair(true);
    let w2 := Wrap<u32> { v: 5 };
    let m := w2.map(fn(x: u32) -> u32 => x * 2);
    let c := Crate { n: 7 };
    let w3 := Wrap<u32> { v: 1 };
    let t := w3.total(c.borrow());
    let w4 := Wrap<u32> { v: 1 };
    let q: u32 = w4.pick(10, 20, false);
    let pl := Plain { k: 1 };
    let e: u32 = pl.echo(30);
    let pl2 := Plain { k: 1 };
    let f := pl2.echo(true);
    let pl3 := Plain { k: 1 };
    let bt := pl3.both(3, true);
    let w5 := Wrap<u32> { v: 1 };
    let arr: array<u32, 4> = [3, 0, 0, 0];
    let k := w5.spread(arr.borrow());
    let n := Named { name: "abc" };
    let five: u32 = 5;
    let tg := n.tag(five);
    var n2 := Named { name: "xy" };
    let sh: u32 = n2.shout(11);
    let w6 := Wrap<u32> { v: 3 };
    let mapped := w6.map(fn(x: u32) -> bool => x > 2);
    let wb := Wrap<bool> { v: true };
    let eight: u32 = 8;
    let pb := wb.pair(eight);
    let wc := Wrap<bool> { v: false };
    let pc := wc.pair(true);
    let both := (if pb.0 { pb.1 } else { 0 }) + (if pc.1 { 1 } else { 0 });
    p.0 + both + m.v + t + q + e + (if f { 1 } else { 0 }) + (if bt.1 { 1 } else { 0 }) + tg.0 + tg.1 + k + sh + n2.name.len() + (if mapped.v { 100 } else { 0 })
}
"####;

const TYPE_BOUNDS: &str = r####"use core::ops::Add;
interface Weigh { fn weigh(borrow self) -> u32; }
type Money { cents: u32 }
extend Money of Add { type Rhs = Money; type Output = Money; fn add(self, rhs: Money) -> Money { Money { cents: self.cents + rhs.cents } } }
extend Money of Weigh { fn weigh(borrow self) -> u32 { self.cents } }
type Gram { g: u32 }
extend Gram of Weigh { fn weigh(borrow self) -> u32 { self.g * 10 } }
type Pair<T> where T: Add + Weigh { a: T, b: T } extend {
    fn plus(borrow self, x: T, y: T::Rhs) -> T::Output { x + y }
    fn heavy(borrow self) -> u32 { self.a.weigh() of Weigh + self.b.weigh() of Weigh }
    fn twice<U>(borrow self, u: U) -> (U, u32) { (u, 2) }
}
type Scale<T> where T: Weigh { item: T } extend {
    fn grams(borrow self) -> u32 { self.item.weigh() of Weigh }
    fn with<U>(borrow self, other: borrow U) -> u32 where U: Weigh { self.item.weigh() of Weigh + other.weigh() of Weigh }
}
type Crate<T> where T: Weigh { inner: Scale<T> }
fn build<U>(a: U, b: U) -> Pair<U> where U: Add + Weigh { Pair<U> { a: a, b: b } }
fn main() -> u32 {
    let q := Pair<Money> { a: Money { cents: 5 }, b: Money { cents: 6 } };
    let m := q.plus(Money { cents: 10 }, Money { cents: 20 });
    let w := q.twice(true);
    let s1 := Scale<Gram> { item: Gram { g: 3 } };
    let s2 := Scale<Money> { item: Money { cents: 4 } };
    let money := Money { cents: 1 };
    let c := Crate<Gram> { inner: Scale<Gram> { item: Gram { g: 2 } } };
    let built := build(Money { cents: 100 }, Money { cents: 200 });
    m.cents + built.heavy() + q.heavy() + w.1 + s1.grams() + s2.grams() + s1.with(money.borrow()) + c.inner.grams()
}
"####;

const STRESS: &str = r####"use alloc::List;
type Label { text: string, n: u32 }
type Tok [ Word(string), Num(u32) ]
fn big() -> string { let s := "@TEXT@".concat(""); s }
fn combine(acc: Label, x: u32) -> Label {
    let t := acc.text.concat("+");
    Label { text: t, n: acc.n + x }
}
fn fresh(n: u32) -> Label { let t := big(); Label { text: t, n: n } }
fn pair(a: string, n: u32) -> (string, u32) { (a, n) }
fn step(t: (string, u32)) -> (string, u32) {
    let (s, n) := t;
    let s2 := s.concat("*");
    (s2, n + 1)
}
fn push_one(xs: List<string>, s: string) -> List<string> {
    var out := xs;
    out.push(s);
    out
}
fn holder(s: string) -> fn() -> u32 { fn() -> u32 => s.len() }
fn set_label(l: share Label, v: Label) -> u32 { l = v; l.n + l.text.len() }
fn labels(flag: bool) -> u32 {
    var acc := fresh(0);
    loop j in 0..3 { acc = combine(acc, 1); }
    let next := fresh(9);
    acc = { if flag { return 1; } next };
    acc.n + acc.text.len()
}
fn tuples(flag: bool) -> u32 {
    let t0 := big();
    var tp := pair(t0, 0);
    loop j in 0..2 { tp = step(tp); }
    let t1 := big();
    let fresh_pair := pair(t1, 7);
    tp = { if flag { return 2; } fresh_pair };
    tp.1 + tp.0.len()
}
fn tokens(flag: bool) -> u32 {
    let t0 := big();
    var tok := Tok::Word(t0);
    let t1 := big();
    tok = Tok::Word(t1);
    let replacement := Tok::Num(5);
    tok = { if flag { return 3; } replacement };
    match tok { Tok::Word(s) => s.len(), Tok::Num(n) => n }
}
fn lists(flag: bool) -> u32 {
    var ls: List<string> = [];
    loop j in 0..3 {
        let s := big();
        ls = push_one(ls, s);
    }
    let a := big();
    let rebuilt: List<string> = [a];
    ls = { if flag { return 4; } rebuilt };
    ls.len() + ls[0].len()
}
fn arrays(flag: bool) -> u32 {
    let a := big();
    let b := big();
    var words: array<string, 2> = [a, b];
    let c := big();
    let d := big();
    let other: array<string, 2> = [c, d];
    words = { if flag { return 5; } other };
    words[0].len() + words[1].len()
}
fn closures(flag: bool) -> u32 {
    let a := big();
    var f: fn() -> u32 = holder(a);
    loop j in 0..3 {
        let s := big();
        f = holder(s);
    }
    let last := big();
    let g := holder(last);
    f = { if flag { return 6; } g };
    f()
}
fn shared(flag: bool) -> u32 {
    var m := fresh(1);
    let r := set_label(m.share(), fresh(2));
    let more := fresh(3);
    let r2 := set_label(m.share(), more);
    if flag { return 7; }
    r + r2 + m.n
}
fn main() -> u32 {
    var iteration: u32 = 0;
    var total: u32 = 0;
    loop {
        if iteration == 4096 { break; }
        total += labels(true);
        total += labels(false);
        total += tuples(true);
        total += tuples(false);
        total += tokens(true);
        total += tokens(false);
        total += lists(true);
        total += lists(false);
        total += arrays(true);
        total += arrays(false);
        total += closures(true);
        total += closures(false);
        total += shared(true);
        total += shared(false);
        iteration += 1;
    }
    total
}
"####;

fn expect(f: &Fixture, artifact: &str, value: u32) {
    run_source_and_wasm(
        f,
        artifact,
        format!("Result: u32({value})\n").as_bytes(),
        format!("Result: i32({value})\n").as_bytes(),
    );
}

#[test]
fn whole_owner_reassignment_works_for_every_owner_kind() {
    let f = Fixture::new();
    project(&f, "f4-kinds", OWNER_KINDS);
    // struct 5, record 4, tuple 8, enum 4 + 2, tree 5, array 7, List<string> 4,
    // Box 6, List<u32> 3, plain closure 11, var fn 201, share Label 43, share List 3.
    expect(&f, "f4-kinds.wasm", 306);
}

#[test]
fn reassignment_in_loops_and_early_exits_finishes_the_rhs_first() {
    let f = Fixture::new();
    project(&f, "f4-loops", LOOPS);
    // acc 17, borrowed-old 8, tuple 10, List 3, composed closures 13,
    // early exit keeps the old value 2, full run 99.
    expect(&f, "f4-loops.wasm", 152);
}

#[test]
fn reassignment_edge_cases_reinitialize_after_moves_and_self_assignment() {
    let f = Fixture::new();
    project(&f, "f4-edges", EDGES);
    // moved-out then reassigned 1 + 5, `s = s` 7 + 2, literal text struct
    // replaced by a heap one 10 + 4, `xs = xs` 0.
    expect(&f, "f4-edges.wasm", 29);
}

#[test]
fn reassignment_loops_release_every_value_under_capped_memory() {
    const ITERATIONS: u32 = 4_096;
    const TEXT_BYTES: usize = 4_096;
    let text = "x".repeat(TEXT_BYTES);
    let f = Fixture::new();
    project(&f, "f4-stress", &STRESS.replace("@TEXT@", &text));
    let t = TEXT_BYTES as u32;
    // labels 1 + (9 + T), tuples 2 + (7 + T), tokens 3 + 5, lists 4 + (1 + T),
    // arrays 5 + 2T, closures 6 + T, shared 7 + ((2 + T) + (3 + T) + 3).
    let per_iteration = (1 + 9 + t)
        + (2 + 7 + t)
        + (3 + 5)
        + (4 + 1 + t)
        + (5 + 2 * t)
        + (6 + t)
        + (7 + (2 + t) + (3 + t) + 3);
    let expected = per_iteration * ITERATIONS;
    run_source_and_wasm(
        &f,
        "f4-stress.wasm",
        format!("Result: u32({expected})\n").as_bytes(),
        format!("Result: i32({expected})\n").as_bytes(),
    );
    let wasm_path = f.0.join("f4-stress.wasm");
    let (capped, initial, maximum) = cap_memory(&fs::read(&wasm_path).unwrap());
    fs::write(&wasm_path, capped).unwrap();
    let wasm = f.run(&["run", "f4-stress.wasm"]);
    assert!(
        wasm.status.success(),
        "capped Wasm run failed: {}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, format!("Result: i32({expected})\n").as_bytes());
    assert_capped_memory(&wasm_path, initial, maximum);
}

#[test]
fn reassignment_rejects_loans_types_immutable_targets_and_lent_functions() {
    let f = Fixture::new();
    project(&f, "f4-negatives", "fn main() -> u32 { 0 }");
    let prelude = "use alloc::List;\ntype Label { text: string, n: u32 }\nfn mk(n: u32) -> Label { let t := \"t\".concat(\"!\"); Label { text: t, n: n } }\nfn eat(l: Label) -> u32 { l.n }\n";
    for (body, code, text) in [
        // Live loans on the target block the assignment.
        (
            "fn main() -> u32 { var l := mk(1); let r := l.borrow(); l = mk(2); r.n }",
            "BE005",
            "cannot assign to `l` while it is borrowed",
        ),
        (
            "fn main() -> u32 { var l := mk(1); let r := l.share(); l = mk(2); r.n }",
            "BE005",
            "cannot assign to `l` while it is shared",
        ),
        (
            "fn main() -> u32 { var xs: List<string> = []; let r := xs.borrow(); xs = []; r.len() }",
            "BE005",
            "cannot assign to `xs` while it is borrowed",
        ),
        (
            "fn bad(l: share Label) -> u32 { let r := l.borrow(); l = mk(2); r.n }\nfn main() -> u32 { 0 }",
            "BE005",
            "while it is borrowed",
        ),
        // Types, mutability, moves.
        (
            "fn main() -> u32 { var l := mk(1); l = 5; 0 }",
            "TE002",
            "expected Label",
        ),
        (
            "fn main() -> u32 { let l := mk(1); l = mk(2); l.n }",
            "TE004",
            "cannot assign to immutable binding 'l'",
        ),
        (
            "fn bad(l: Label) -> u32 { l = mk(2); l.n }\nfn main() -> u32 { 0 }",
            "TE004",
            "cannot assign to immutable binding 'l'",
        ),
        (
            "fn main() -> u32 { var l := mk(1); let n := eat(l); l.n + n }",
            "BE001",
            "unavailable after a move",
        ),
        // A `share fn` parameter lends the caller's function value.
        (
            "fn bad(f: share fn(u32) -> u32) -> u32 { f = fn(x: u32) => x; 0 }\nfn main() -> u32 { 0 }",
            "TE018",
            "cannot be reassigned as a whole yet",
        ),
    ] {
        rejects(&f, &format!("{prelude}{body}\n"), code, text);
    }
}

#[test]
fn const_generic_parameters_are_u32_values_per_specialization() {
    let f = Fixture::new();
    project(&f, "f4-const-values", CONST_VALUES);
    // sum<3> 10, sum<5> 11, shape<3> 128, shape<5> 154, Grid<_, 2, 3>: 6 + 102 + 3, fill 9.
    expect(&f, "f4-const-values.wasm", 10_123_074);
    let prelude = "fn f<const N: u32>(a: array<u32, N>) -> u32 {\n";
    let call = "fn main() -> u32 { let a: array<u32, 2> = [1, 2]; f(a) }\n";
    for (body, code, text) in [
        (
            "    let x: i32 = N;\n    0\n}\n",
            "TE002",
            "expected i32, found u32",
        ),
        (
            "    N = 3;\n    0\n}\n",
            "TE004",
            "cannot assign to const generic parameter 'N'",
        ),
        (
            "    let r := N.share();\n    0\n}\n",
            "TE017",
            "requires a named local owner",
        ),
        (
            "    [0; M].len()\n}\n",
            "NE001",
            "unknown constant 'M' in an array repeat count",
        ),
        // A local named like the parameter wins.
        (
            "    let N := 7;\n    N\n}\n",
            "TE002",
            "expected u32, found i32",
        ),
    ] {
        rejects(&f, &format!("{prelude}{body}{call}"), code, text);
    }
    rejects(
        &f,
        "fn f<const N: u32>() -> u32 { N }\nfn main() -> u32 { N }\n",
        "NE001",
        "unknown name 'N'",
    );
    // The parameter shadows a module constant of the same name.
    f.write(
        "src/main.mb",
        "const N: u32 = 9;\nfn f<const N: u32>(a: array<u32, N>) -> u32 { N }\nfn main() -> u32 { let a: array<u32, 2> = [1, 2]; f(a) + N }\n",
    );
    expect(&f, "f4-const-shadow.wasm", 11);
}

#[test]
fn methods_take_their_own_type_and_const_parameters() {
    let f = Fixture::new();
    project(&f, "f4-methods", METHOD_PARAMETERS);
    expect(&f, "f4-methods.wasm", 216);
    let prelude = "interface Weigh { fn weigh(borrow self) -> u32; }\ntype Crate { n: u32 }\nextend Crate of Weigh { fn weigh(borrow self) -> u32 { self.n } }\ntype Plain { k: u32 }\n";
    for (body, code, text) in [
        (
            "type W<T> { v: T } extend { fn total<U>(borrow self, o: borrow U) -> u32 where U: Weigh { o.weigh() of Weigh } }\nfn main() -> u32 { let w := W<u32> { v: 1 }; let p := Plain { k: 1 }; w.total(p.borrow()) }",
            "TE007",
            "no visible implementation of 'main::Weigh' for Plain satisfies generic bound 'U: main::Weigh' of 'total'",
        ),
        (
            "type W { v: u32 } extend { fn make<U>(borrow self) -> u32 { 1 } }\nfn main() -> u32 { let w := W { v: 1 }; w.make() }",
            "TE002",
            "cannot infer the type argument 'U'",
        ),
        (
            "type W<T> { v: T } extend { fn dup<T>(borrow self, x: T) -> u32 { 1 } }\nfn main() -> u32 { let w := W<u32> { v: 1 }; w.dup(true) }",
            "TE007",
            "generic parameter 'T' of method 'dup' repeats a parameter of its type",
        ),
        (
            "type W { v: u32 } extend { fn bad<U>(borrow self, o: borrow U) -> u32 where V: Weigh { 1 } }\nfn main() -> u32 { let w := W { v: 1 }; let p := Plain { k: 1 }; w.bad(p.borrow()) }",
            "TE007",
            "bound 'V: ...' names 'V', which is not a type parameter of 'bad'",
        ),
        (
            "type W { v: u32 } extend { fn id<T>(self, x: T) -> T { x } }\nfn main() -> u32 { let w := W { v: 1 }; let r: bool = w.id(1); 0 }",
            "TE002",
            "expected bool",
        ),
        (
            "interface I { fn m<T>(borrow self, x: T) -> u32; }\nfn main() -> u32 { 0 }",
            "SE002",
            "expected '('",
        ),
        (
            "type W { v: u32 } extend W of Weigh { fn weigh<T>(borrow self) -> u32 { 1 } }\nfn main() -> u32 { 0 }",
            "SE002",
            "expected '('",
        ),
    ] {
        rejects(&f, &format!("{prelude}{body}\n"), code, text);
    }
}

#[test]
fn type_declarations_check_where_bounds_at_each_instantiation() {
    let f = Fixture::new();
    project(&f, "f4-bounds", TYPE_BOUNDS);
    // plus 30 + heavy of `build` 300 + heavy 11 + twice 2 + Scale<Gram> 30
    // + Scale<Money> 4 + `with` 31 + Crate<Gram> 20.
    expect(&f, "f4-bounds.wasm", 428);
    let prelude = "interface Weigh { fn weigh(borrow self) -> u32; }\ntype Crate { n: u32 }\nextend Crate of Weigh { fn weigh(borrow self) -> u32 { self.n } }\ntype Plain { k: u32 }\ntype X<T> where T: Weigh { v: T }\n";
    let missing = "no visible implementation of 'main::Weigh' for Plain satisfies bound 'T: main::Weigh' of type 'X'";
    for body in [
        // Annotations, signatures, fields, payloads and nested instances.
        "fn main() -> u32 { let x: X<Plain> = X<Crate> { v: Crate { n: 1 } }; 0 }",
        "fn take(x: X<Plain>) -> u32 { 0 }\nfn main() -> u32 { 0 }",
        "fn give() -> X<Plain> { X<Plain> { v: Plain { k: 1 } } }\nfn main() -> u32 { 0 }",
        "type Holder { x: X<Plain> }\nfn main() -> u32 { 0 }",
        "type Slot [Empty, Full(X<Plain>)]\nfn main() -> u32 { 0 }",
        "type Z<T> { x: X<T> }\nfn f(z: Z<Plain>) -> u32 { 0 }\nfn main() -> u32 { 0 }",
        // A generic function instantiating the bounded type with a bad argument.
        "fn mk<U>(u: U) -> X<U> { X<U> { v: u } }\nfn main() -> u32 { let p := Plain { k: 1 }; let x := mk(p); 0 }",
    ] {
        rejects(&f, &format!("{prelude}{body}\n"), "TE007", missing);
    }
    for (body, code, text) in [
        (
            "type Y<T> where U: Weigh { v: T }\nfn main() -> u32 { 0 }",
            "TE007",
            "bound 'U: ...' names 'U', which is not a type parameter of 'Y'",
        ),
        (
            "type Y<T> where T: Weigh<u32> { v: T }\nfn main() -> u32 { 0 }",
            "TE007",
            "interface bounds with type arguments are not supported",
        ),
        (
            "type Y where T: Weigh { v: u32 }\nfn main() -> u32 { 0 }",
            "TE002",
            "where-constraints require generic parameters",
        ),
    ] {
        rejects(&f, &format!("{prelude}{body}\n"), code, text);
    }
}
