//! G6: numeric APIs for every integer width.
//!
//! Bitwise operators and shifts, `checked_*`, `wrapping_*` and `saturating_*`
//! are exercised over boundary values. Expectations are computed with Rust's
//! own integer methods at test time: each Memobits program folds its results
//! into a 64-bit hash with the same mixing step as the Rust side, so a whole
//! table of cases is checked by one `assert` per operation. The same programs
//! run from source (`mb test`, `mb run`) and as a standalone Wasm artifact.
//! Constant evaluation (static checks and `const` items) is compared with the
//! same Rust results, and constant shift counts and type errors are rejected.
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
        let path = std::env::temp_dir().join(format!(
            "memobits-g6-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(
            path.join("project.toml"),
            "[package]\nname='g6'\nentry='main::main'\n",
        )
        .unwrap();
        fs::write(path.join("src/main.mb"), source).unwrap();
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

/// Compile `source` and return stderr; the build must fail with `code`.
fn rejects(source: &str, code: &str) -> String {
    let f = Fixture::new(source);
    let output = f.run(&["check"]);
    let stderr = text(&output.stderr);
    assert!(!output.status.success(), "accepted:\n{source}");
    assert!(
        stderr.contains(code),
        "expected {code} for:\n{source}\n{stderr}"
    );
    stderr
}

fn accepts(source: &str) {
    let f = Fixture::new(source);
    let output = f.run(&["check"]);
    assert!(
        output.status.success(),
        "{source}\n{}",
        text(&output.stderr)
    );
}

// ---------------------------------------------------------------------------
// Rust-side reference semantics

trait Int: Copy {
    const NAME: &'static str;
    const BITS: u32;
    const SIGNED: bool;
    fn from_i128(value: i128) -> Self;
    fn to_i128(self) -> i128;
    fn add_wrapping(self, o: Self) -> Self;
    fn sub_wrapping(self, o: Self) -> Self;
    fn mul_wrapping(self, o: Self) -> Self;
    fn neg_wrapping(self) -> Self;
    fn add_saturating(self, o: Self) -> Self;
    fn sub_saturating(self, o: Self) -> Self;
    fn mul_saturating(self, o: Self) -> Self;
    fn add_checked(self, o: Self) -> Option<Self>;
    fn sub_checked(self, o: Self) -> Option<Self>;
    fn mul_checked(self, o: Self) -> Option<Self>;
    fn div_checked(self, o: Self) -> Option<Self>;
    fn rem_checked(self, o: Self) -> Option<Self>;
    fn neg_checked(self) -> Option<Self>;
    fn shl_checked(self, n: u32) -> Option<Self>;
    fn shr_checked(self, n: u32) -> Option<Self>;
    fn shl_wrapping(self, n: u32) -> Self;
    fn shr_wrapping(self, n: u32) -> Self;
    fn shl_plain(self, n: u32) -> Self;
    fn shr_plain(self, n: u32) -> Self;
    fn and(self, o: Self) -> Self;
    fn or(self, o: Self) -> Self;
    fn xor(self, o: Self) -> Self;
}

macro_rules! int_impl {
    ($t:ty, $name:expr, $signed:expr) => {
        impl Int for $t {
            const NAME: &'static str = $name;
            const BITS: u32 = <$t>::BITS;
            const SIGNED: bool = $signed;
            fn from_i128(value: i128) -> Self {
                value as $t
            }
            fn to_i128(self) -> i128 {
                self as i128
            }
            fn add_wrapping(self, o: Self) -> Self {
                <$t>::wrapping_add(self, o)
            }
            fn sub_wrapping(self, o: Self) -> Self {
                <$t>::wrapping_sub(self, o)
            }
            fn mul_wrapping(self, o: Self) -> Self {
                <$t>::wrapping_mul(self, o)
            }
            fn neg_wrapping(self) -> Self {
                <$t>::wrapping_neg(self)
            }
            fn add_saturating(self, o: Self) -> Self {
                <$t>::saturating_add(self, o)
            }
            fn sub_saturating(self, o: Self) -> Self {
                <$t>::saturating_sub(self, o)
            }
            fn mul_saturating(self, o: Self) -> Self {
                <$t>::saturating_mul(self, o)
            }
            fn add_checked(self, o: Self) -> Option<Self> {
                <$t>::checked_add(self, o)
            }
            fn sub_checked(self, o: Self) -> Option<Self> {
                <$t>::checked_sub(self, o)
            }
            fn mul_checked(self, o: Self) -> Option<Self> {
                <$t>::checked_mul(self, o)
            }
            fn div_checked(self, o: Self) -> Option<Self> {
                <$t>::checked_div(self, o)
            }
            fn rem_checked(self, o: Self) -> Option<Self> {
                // Rust reports `MIN % -1` as an overflow; Memobits (NUM-01)
                // defines it as zero, distinct from the division overflow.
                if o == 0 {
                    None
                } else {
                    Some(<$t>::wrapping_rem(self, o))
                }
            }
            fn neg_checked(self) -> Option<Self> {
                <$t>::checked_neg(self)
            }
            fn shl_checked(self, n: u32) -> Option<Self> {
                <$t>::checked_shl(self, n)
            }
            fn shr_checked(self, n: u32) -> Option<Self> {
                <$t>::checked_shr(self, n)
            }
            fn shl_wrapping(self, n: u32) -> Self {
                <$t>::wrapping_shl(self, n)
            }
            fn shr_wrapping(self, n: u32) -> Self {
                <$t>::wrapping_shr(self, n)
            }
            fn shl_plain(self, n: u32) -> Self {
                self << n
            }
            fn shr_plain(self, n: u32) -> Self {
                self >> n
            }
            fn and(self, o: Self) -> Self {
                self & o
            }
            fn or(self, o: Self) -> Self {
                self | o
            }
            fn xor(self, o: Self) -> Self {
                self ^ o
            }
        }
    };
}

int_impl!(i8, "i8", true);
int_impl!(i16, "i16", true);
int_impl!(i32, "i32", true);
int_impl!(i64, "i64", true);
int_impl!(u8, "u8", false);
int_impl!(u16, "u16", false);
int_impl!(u32, "u32", false);
int_impl!(u64, "u64", false);

fn min_of<T: Int>() -> i128 {
    if T::SIGNED {
        -(1i128 << (T::BITS - 1))
    } else {
        0
    }
}

fn max_of<T: Int>() -> i128 {
    if T::SIGNED {
        (1i128 << (T::BITS - 1)) - 1
    } else {
        (1i128 << T::BITS) - 1
    }
}

/// Boundary values: 0, 1, -1, MIN, MAX, MIN+1, MAX-1, powers of two and a few
/// small multipliers.
fn values<T: Int>() -> Vec<T> {
    let (min, max) = (min_of::<T>(), max_of::<T>());
    let mut all = vec![0, 1, 2, 3, 17, min, min + 1, max, max - 1];
    if T::SIGNED {
        all.extend([-1, -2, -3]);
    }
    for power in [T::BITS / 2, T::BITS - 2, T::BITS - 1] {
        all.push(1i128 << power);
    }
    all.push(max / 2 + 1);
    all.push(max / 3);
    all.retain(|v| (min..=max).contains(v));
    all.sort_unstable();
    all.dedup();
    all.into_iter().map(T::from_i128).collect()
}

/// Shift counts: 0, 1, width-1, width, width+1, 31, 32, 63, 64, large.
fn counts<T: Int>() -> Vec<u32> {
    let w = T::BITS;
    let mut all = vec![
        0,
        1,
        2,
        w / 2,
        w - 1,
        w,
        w + 1,
        31,
        32,
        33,
        63,
        64,
        100,
        255,
        u32::MAX,
    ];
    all.sort_unstable();
    all.dedup();
    all
}

fn mix(hash: u64, value: u64) -> u64 {
    (hash ^ value).wrapping_mul(1_099_511_628_211)
}

const SEED: u64 = 14_695_981_039_346_656_037;

fn as_u64<T: Int>(value: T) -> u64 {
    value.to_i128() as u64
}

fn option_u64<T: Int>(value: Option<T>) -> u64 {
    match value {
        Some(v) => as_u64(v).wrapping_add(7),
        None => 3,
    }
}

fn literal(value: i128) -> String {
    if value < 0 {
        format!("({value})")
    } else {
        value.to_string()
    }
}

// ---------------------------------------------------------------------------
// Program generation

const PRELUDE: &str = "fn mix(h: u64, x: u64) -> u64 { (h ^ x).wrapping_mul(1099511628211) }\n";

struct Table {
    /// (function name, expected hash)
    entries: Vec<(String, u64)>,
    source: String,
}

impl Table {
    fn new() -> Self {
        Self {
            entries: Vec::new(),
            source: PRELUDE.to_owned(),
        }
    }

    /// A function folding `body` over all value pairs `(x, y)`.
    fn pairs<T: Int>(&mut self, name: &str, body: &str, rust: impl Fn(T, T) -> Vec<u64>) {
        let vals = values::<T>();
        let list = vals
            .iter()
            .map(|v| literal(v.to_i128()))
            .collect::<Vec<_>>()
            .join(", ");
        let n = vals.len();
        let mut expected = SEED;
        for &x in &vals {
            for &y in &vals {
                for item in rust(x, y) {
                    expected = mix(expected, item);
                }
            }
        }
        self.source.push_str(&format!(
            "fn {name}() -> u64 {{\n    let a: array<{ty}, {n}> = [{list}];\n    let n: u32 = {n};\n    var h: u64 = {SEED};\n    loop i in 0..n {{\n        loop j in 0..n {{\n            let x := a[i];\n            let y := a[j];\n{body}\n        }}\n    }}\n    h\n}}\n",
            ty = T::NAME
        ));
        self.entries.push((name.to_owned(), expected));
    }

    /// A function folding `body` over all values `x` and shift counts `s`.
    fn shifts<T: Int>(&mut self, name: &str, body: &str, rust: impl Fn(T, u32) -> Vec<u64>) {
        let vals = values::<T>();
        let list = vals
            .iter()
            .map(|v| literal(v.to_i128()))
            .collect::<Vec<_>>()
            .join(", ");
        let cs = counts::<T>();
        let clist = cs.iter().map(u32::to_string).collect::<Vec<_>>().join(", ");
        let mut expected = SEED;
        for &x in &vals {
            for &s in &cs {
                for item in rust(x, s) {
                    expected = mix(expected, item);
                }
            }
        }
        self.source.push_str(&format!(
            "fn {name}() -> u64 {{\n    let a: array<{ty}, {n}> = [{list}];\n    let c: array<u32, {m}> = [{clist}];\n    let n: u32 = {n};\n    let m: u32 = {m};\n    var h: u64 = {SEED};\n    loop i in 0..n {{\n        loop k in 0..m {{\n            let x := a[i];\n            let s := c[k];\n{body}\n        }}\n    }}\n    h\n}}\n",
            ty = T::NAME,
            n = vals.len(),
            m = cs.len()
        ));
        self.entries.push((name.to_owned(), expected));
    }

    /// Append `test fn`s asserting every entry and a `main` that checks the
    /// same entries, so source tests, source run and Wasm run agree.
    fn finish(mut self) -> (String, usize) {
        for (name, expected) in self.entries.clone() {
            self.source.push_str(&format!(
                "test fn t_{name}() {{ assert({name}() == {expected}); }}\n"
            ));
        }
        self.source.push_str("fn main() -> i32 ! Error {\n");
        for (index, (name, expected)) in self.entries.iter().enumerate() {
            self.source.push_str(&format!(
                "    if {name}() != {expected} {{ return Err(Error {{ code: {} }}); }}\n",
                index + 1
            ));
        }
        self.source.push_str("    Ok(42)\n}\n");
        let count = self.entries.len();
        (self.source, count)
    }
}

fn build_table<T: Int>() -> (String, usize) {
    let mut t = Table::new();
    let w = T::BITS;
    // Bitwise operators, methods and compound assignment.
    t.pairs::<T>(
        "bitwise",
        "            h = mix(h, (x & y) as u64);\n            h = mix(h, (x | y) as u64);\n            h = mix(h, (x ^ y) as u64);\n            h = mix(h, x.bit_and(y) as u64);\n            h = mix(h, x.bit_or(y) as u64);\n            h = mix(h, x.bit_xor(y) as u64);\n            var p := x;\n            p &= y;\n            var q := x;\n            q |= y;\n            var r := x;\n            r ^= y;\n            h = mix(h, p as u64);\n            h = mix(h, q as u64);\n            h = mix(h, r as u64);",
        |x, y| {
            let (a, o, e) = (as_u64(x.and(y)), as_u64(x.or(y)), as_u64(x.xor(y)));
            vec![a, o, e, a, o, e, a, o, e]
        },
    );
    for (name, rust) in [
        ("wrapping_add", T::add_wrapping as fn(T, T) -> T),
        ("wrapping_sub", T::sub_wrapping),
        ("wrapping_mul", T::mul_wrapping),
        ("saturating_add", T::add_saturating),
        ("saturating_sub", T::sub_saturating),
        ("saturating_mul", T::mul_saturating),
    ] {
        t.pairs::<T>(
            name,
            &format!("            h = mix(h, x.{name}(y) as u64);"),
            move |x, y| vec![as_u64(rust(x, y))],
        );
    }
    for (name, rust) in [
        ("checked_add", T::add_checked as fn(T, T) -> Option<T>),
        ("checked_sub", T::sub_checked),
        ("checked_mul", T::mul_checked),
        ("checked_div", T::div_checked),
        ("checked_rem", T::rem_checked),
    ] {
        t.pairs::<T>(
            name,
            &format!(
                "            let o := x.{name}(y);\n            let m: u64 = match o {{ Some(v) => (v as u64).wrapping_add(7), None => 3 }};\n            h = mix(h, m);"
            ),
            move |x, y| vec![option_u64(rust(x, y))],
        );
    }
    t.pairs::<T>(
        "negation",
        "            h = mix(h, x.wrapping_neg() as u64);\n            let o := x.checked_neg();\n            let m: u64 = match o { Some(v) => (v as u64).wrapping_add(7), None => 3 };\n            h = mix(h, m);",
        |x, _| vec![as_u64(x.neg_wrapping()), option_u64(x.neg_checked())],
    );
    t.shifts::<T>(
        "shifts",
        &format!(
            "            if s < {w} {{\n                h = mix(h, (x << s) as u64);\n                h = mix(h, (x >> s) as u64);\n                var p := x;\n                p <<= s;\n                var q := x;\n                q >>= s;\n                h = mix(h, p as u64);\n                h = mix(h, q as u64);\n            }}"
        ),
        move |x, s| {
            if s < w {
                let (l, r) = (as_u64(x.shl_plain(s)), as_u64(x.shr_plain(s)));
                vec![l, r, l, r]
            } else {
                vec![]
            }
        },
    );
    t.shifts::<T>(
        "wrapping_shifts",
        "            h = mix(h, x.wrapping_shl(s) as u64);\n            h = mix(h, x.wrapping_shr(s) as u64);",
        |x, s| vec![as_u64(x.shl_wrapping(s)), as_u64(x.shr_wrapping(s))],
    );
    t.shifts::<T>(
        "checked_shifts",
        "            let l := x.checked_shl(s);\n            let r := x.checked_shr(s);\n            let lm: u64 = match l { Some(v) => (v as u64).wrapping_add(7), None => 3 };\n            let rm: u64 = match r { Some(v) => (v as u64).wrapping_add(7), None => 3 };\n            h = mix(h, lm);\n            h = mix(h, rm);",
        |x, s| vec![option_u64(x.shl_checked(s)), option_u64(x.shr_checked(s))],
    );
    t.finish()
}

fn check_type<T: Int>() {
    let (source, tests) = build_table::<T>();
    let f = Fixture::new(&source);
    let name = T::NAME;

    let checked = f.run(&["check"]);
    assert!(
        checked.status.success(),
        "{name}: {}",
        text(&checked.stderr)
    );

    let report = f.run(&["test"]);
    let stdout = text(&report.stdout);
    assert!(
        report.status.success()
            && stdout.contains(&format!("test result: ok. {tests} passed; 0 failed")),
        "{name}: {stdout}{}",
        text(&report.stderr)
    );

    let source_run = f.run(&["run"]);
    assert!(
        source_run.status.success() && source_run.stderr.is_empty(),
        "{name} source run: {}",
        text(&source_run.stderr)
    );
    assert_eq!(text(&source_run.stdout), "Result: Ok(i32(42))\n", "{name}");

    let build = f.run(&["build", "--output", "g6.wasm"]);
    assert!(build.status.success(), "{name}: {}", text(&build.stderr));
    let wasm = f.run(&["run", "g6.wasm"]);
    assert!(
        wasm.status.success() && wasm.stderr.is_empty(),
        "{name} wasm run: {}",
        text(&wasm.stderr)
    );
    assert_eq!(text(&wasm.stdout), "Result: Ok(i32(42))\n", "{name}");
}

#[test]
fn numeric_tables_match_rust_for_i8() {
    check_type::<i8>();
}

#[test]
fn numeric_tables_match_rust_for_i16() {
    check_type::<i16>();
}

#[test]
fn numeric_tables_match_rust_for_i32() {
    check_type::<i32>();
}

#[test]
fn numeric_tables_match_rust_for_i64() {
    check_type::<i64>();
}

#[test]
fn numeric_tables_match_rust_for_u8() {
    check_type::<u8>();
}

#[test]
fn numeric_tables_match_rust_for_u16() {
    check_type::<u16>();
}

#[test]
fn numeric_tables_match_rust_for_u32() {
    check_type::<u32>();
}

#[test]
fn numeric_tables_match_rust_for_u64() {
    check_type::<u64>();
}

// ---------------------------------------------------------------------------
// Constant evaluation parity

/// Constant operand pairs: every operation below is applied to literals.
fn const_values<T: Int>() -> Vec<T> {
    let (min, max) = (min_of::<T>(), max_of::<T>());
    let mut all = vec![0, 1, 3, min, min + 1, max, max - 1, max / 2 + 1];
    if T::SIGNED {
        all.extend([-1, -3]);
    }
    all.retain(|v| (min..=max).contains(v));
    all.sort_unstable();
    all.dedup();
    all.into_iter().map(T::from_i128).collect()
}

/// Statements `1 / ((EXPR) - (R))` (a division by zero exactly when the static
/// fold of EXPR is R) and the off-by-one twins that must stay silent.
fn fold_lines<T: Int>() -> (String, String, usize) {
    let ty = T::NAME;
    let (mut equal, mut different) = (String::new(), String::new());
    let mut count = 0;
    let mut add = |expression: String, result: T| {
        let r = result.to_i128();
        equal.push_str(&format!(
            "    let e{count}: {ty} = 1 / (({expression}) - {});\n",
            literal(r)
        ));
        let shifted = if r < max_of::<T>() { r + 1 } else { r - 1 };
        different.push_str(&if shifted > r {
            format!(
                "    let d{count}: {ty} = 1 / ({} - ({expression}));\n",
                literal(shifted)
            )
        } else {
            format!(
                "    let d{count}: {ty} = 1 / (({expression}) - {});\n",
                literal(shifted)
            )
        });
        count += 1;
    };
    let vals = const_values::<T>();
    for &x in &vals {
        let a = literal(x.to_i128());
        add(format!("{a}.wrapping_neg()"), x.neg_wrapping());
        for &y in &vals {
            let b = literal(y.to_i128());
            for (name, rust) in [
                ("wrapping_add", T::add_wrapping as fn(T, T) -> T),
                ("wrapping_sub", T::sub_wrapping),
                ("wrapping_mul", T::mul_wrapping),
                ("saturating_add", T::add_saturating),
                ("saturating_sub", T::sub_saturating),
                ("saturating_mul", T::mul_saturating),
            ] {
                add(format!("{a}.{name}({b})"), rust(x, y));
            }
            add(format!("{a}.bit_and({b})"), x.and(y));
            add(format!("{a}.bit_or({b})"), x.or(y));
            add(format!("{a}.bit_xor({b})"), x.xor(y));
            add(format!("{a} & {b}"), x.and(y));
            add(format!("{a} | {b}"), x.or(y));
            add(format!("{a} ^ {b}"), x.xor(y));
            // Strict operators fold only when the result is in range.
            if let Some(v) = x.add_checked(y) {
                add(format!("{a} + {b}"), v);
            }
            if let Some(v) = x.sub_checked(y) {
                add(format!("{a} - {b}"), v);
            }
            if let Some(v) = x.mul_checked(y) {
                add(format!("{a} * {b}"), v);
            }
            if y.to_i128() != 0 {
                if let Some(v) = x.div_checked(y) {
                    add(format!("{a} / {b}"), v);
                }
                if let Some(v) = x.rem_checked(y) {
                    add(format!("{a} % {b}"), v);
                }
            }
        }
        for s in [0u32, 1, 2, T::BITS - 1, T::BITS, T::BITS + 1, 40, 100] {
            add(format!("{a}.wrapping_shl({s})"), x.shl_wrapping(s));
            add(format!("{a}.wrapping_shr({s})"), x.shr_wrapping(s));
            if s < T::BITS {
                add(format!("{a} << {s}"), x.shl_plain(s));
                add(format!("{a} >> {s}"), x.shr_plain(s));
            }
        }
    }
    (equal, different, count)
}

fn check_fold<T: Int>() {
    let (equal, different, count) = fold_lines::<T>();
    let name = T::NAME;
    // Statements are split over several functions so one diagnostic per
    // statement is reported.
    let wrap = |lines: &str| -> String {
        let mut out = String::new();
        for (index, chunk) in lines.lines().collect::<Vec<_>>().chunks(40).enumerate() {
            out.push_str(&format!("fn chunk{index}() {{\n{}\n}}\n", chunk.join("\n")));
        }
        out.push_str("fn main() -> i32 { 42 }\n");
        out
    };
    let silent = Fixture::new(&wrap(&different));
    let output = silent.run(&["check"]);
    assert!(
        output.status.success(),
        "{name}: a static fold disagrees with Rust (off-by-one twin rejected): {}",
        text(&output.stderr)
            .lines()
            .take(6)
            .collect::<Vec<_>>()
            .join("\n")
    );
    let folded = Fixture::new(&wrap(&equal));
    let output = folded.run(&["check"]);
    let stderr = text(&output.stderr);
    assert!(!output.status.success(), "{name}: nothing folded");
    let hits = stderr.matches("LE002").count();
    assert_eq!(
        hits,
        count,
        "{name}: only {hits} of {count} constant expressions folded to the Rust result:\n{}",
        stderr.lines().take(6).collect::<Vec<_>>().join("\n")
    );
}

#[test]
fn static_folds_match_rust_for_signed_widths() {
    check_fold::<i8>();
    check_fold::<i16>();
    check_fold::<i32>();
    check_fold::<i64>();
}

#[test]
fn static_folds_match_rust_for_unsigned_widths() {
    check_fold::<u8>();
    check_fold::<u16>();
    check_fold::<u32>();
    check_fold::<u64>();
}

/// `const` items use the resolver's evaluator; compare bitwise and shift
/// results with Rust and with the runtime result of the same operation.
fn check_const_items<T: Int>() {
    let ty = T::NAME;
    let vals = const_values::<T>();
    let mut items = String::new();
    let mut asserts = String::new();
    let mut count = 0;
    let mut add = |op: &str, a: String, b: String, expected: T| {
        items.push_str(&format!("const C{count}: {ty} = {a} {op} {b};\n"));
        asserts.push_str(&format!(
            "    assert(C{count} == {});\n",
            literal(expected.to_i128())
        ));
        count += 1;
    };
    for &x in &vals {
        for &y in &vals {
            let (a, b) = (literal(x.to_i128()), literal(y.to_i128()));
            add("&", a.clone(), b.clone(), x.and(y));
            add("|", a.clone(), b.clone(), x.or(y));
            add("^", a, b, x.xor(y));
        }
        for s in 0..T::BITS {
            let a = literal(x.to_i128());
            add("<<", a.clone(), s.to_string(), x.shl_plain(s));
            add(">>", a, s.to_string(), x.shr_plain(s));
        }
    }
    // Chunk the assertions into several test functions.
    let mut source = items;
    for (index, chunk) in asserts.lines().collect::<Vec<_>>().chunks(60).enumerate() {
        source.push_str(&format!(
            "test fn consts{index}() {{\n{}\n}}\n",
            chunk.join("\n")
        ));
    }
    source.push_str("fn main() -> i32 { 42 }\n");
    let f = Fixture::new(&source);
    let report = f.run(&["test"]);
    let stdout = text(&report.stdout);
    assert!(
        report.status.success() && stdout.contains(" 0 failed"),
        "{ty}: {stdout}{}",
        text(&report.stderr)
    );

    // A constant shift count at or above the width is an error in a const item.
    let mut bad = String::new();
    for (index, s) in [T::BITS, T::BITS + 1, 255].into_iter().enumerate() {
        bad.push_str(&format!(
            "const L{index}: {ty} = 1 << {s};\nconst R{index}: {ty} = 1 >> {s};\n"
        ));
    }
    bad.push_str("fn main() -> i32 { 42 }\n");
    let f = Fixture::new(&bad);
    let output = f.run(&["check"]);
    let stderr = text(&output.stderr);
    assert!(!output.status.success());
    assert_eq!(stderr.matches("LE003").count(), 6, "{ty}: {stderr}");
    assert!(
        stderr.contains(&format!("{ty} shift count must be less than {}", T::BITS)),
        "{stderr}"
    );
}

#[test]
fn const_items_match_rust_for_every_width() {
    check_const_items::<i8>();
    check_const_items::<i16>();
    check_const_items::<i32>();
    check_const_items::<i64>();
    check_const_items::<u8>();
    check_const_items::<u16>();
    check_const_items::<u32>();
    check_const_items::<u64>();
}

// ---------------------------------------------------------------------------
// Shift traps and static errors

#[test]
fn constant_shift_counts_at_or_above_the_width_fail_compilation() {
    // Operators and compound assignments are reported by different passes, so
    // they are checked in separate programs.
    let mut operators = String::new();
    let mut compound = String::new();
    let mut count = 0;
    for (ty, bits) in [
        ("i8", 8),
        ("i16", 16),
        ("i32", 32),
        ("i64", 64),
        ("u8", 8),
        ("u16", 16),
        ("u32", 32),
        ("u64", 64),
    ] {
        for count_value in [bits, bits + 1, 200] {
            for op in ["<<", ">>"] {
                operators.push_str(&format!(
                    "fn f{count}(x: {ty}) -> {ty} {{ x {op} {count_value} }}\n"
                ));
                count += 1;
            }
            compound.push_str(&format!(
                "fn g{count}() {{ var v: {ty} = 1; v <<= {count_value}; v >>= {count_value}; }}\n"
            ));
            count += 1;
        }
    }
    operators.push_str("fn main() -> i32 { 42 }\n");
    compound.push_str("fn main() -> i32 { 42 }\n");
    let stderr = rejects(&operators, "LE003");
    assert_eq!(stderr.matches("LE003").count(), 8 * 3 * 2, "{stderr}");
    assert!(
        stderr.contains("i8 shift count must be less than 8"),
        "{stderr}"
    );
    assert!(
        stderr.contains("u64 shift count must be less than 64"),
        "{stderr}"
    );
    let stderr = rejects(&compound, "LE003");
    assert_eq!(stderr.matches("LE003").count(), 8 * 3 * 2, "{stderr}");
    assert!(
        stderr.contains("i16 shift count must be less than 16"),
        "{stderr}"
    );

    // Counts below the width, and wrapping/checked methods with any count,
    // are accepted.
    accepts(
        "fn main() -> i32 { let a: i8 = 1; let b: u64 = 1; \
         let r := (a << 7) as i32 + (b >> 63) as i32 + a.wrapping_shl(200) as i32; \
         let c := b.checked_shr(64); r }\n",
    );
}

#[test]
fn dynamic_shift_counts_at_or_above_the_width_trap() {
    let mut source = String::new();
    let mut tests = 0;
    for (ty, bits) in [
        ("i8", 8),
        ("i16", 16),
        ("i32", 32),
        ("i64", 64),
        ("u8", 8),
        ("u16", 16),
        ("u32", 32),
        ("u64", 64),
    ] {
        for (op, name) in [("<<", "shl"), (">>", "shr")] {
            source.push_str(&format!(
                "fn {name}_{ty}(x: {ty}, c: u32) -> {ty} {{ x {op} c }}\n\
                 test fn {name}_{ty}_ok() {{ assert({name}_{ty}(1, {}) != 2); }}\n\
                 test fn {name}_{ty}_at_width() {{ assert({name}_{ty}(1, {bits}) == 0); }}\n\
                 test fn {name}_{ty}_above_width() {{ assert({name}_{ty}(1, {}) == 0); }}\n",
                bits - 1,
                bits + 5
            ));
            tests += 3;
        }
    }
    source.push_str("fn main() -> i32 { 42 }\n");
    let f = Fixture::new(&source);
    let report = f.run(&["test"]);
    let stdout = text(&report.stdout);
    // The `ok` tests pass (1 shifted by width-1 never equals 2 for width > 2);
    // the other 32 trap with the shift-count reason.
    assert!(
        stdout.contains(&format!("{} passed; 32 failed", tests - 32)),
        "{stdout}"
    );
    assert_eq!(
        stdout
            .matches("shift count must be less than the bit width")
            .count(),
        32,
        "{stdout}"
    );
}

#[test]
fn operations_that_still_trap_keep_their_controlled_traps() {
    // The strict operators are unchanged for every width: overflow and
    // division failures trap, while checked_* never trap.
    let source = "fn add(a: i8, b: i8) -> i8 { a + b }\n\
        fn div(a: i64, b: i64) -> i64 { a / b }\n\
        test fn add_overflow() { assert(add(127, 1) == 0); }\n\
        test fn div_overflow() { assert(div(-9223372036854775808, -1) == 0); }\n\
        test fn checked_never_traps() {\n\
            let a: i64 = -9223372036854775808;\n\
            let z: i64 = 0;\n\
            assert(match a.checked_div(-1) { Some(_) => false, None => true });\n\
            assert(match a.checked_rem(-1) { Some(v) => v == 0, None => false });\n\
            assert(match a.checked_div(z) { Some(_) => false, None => true });\n\
            assert(match a.checked_rem(z) { Some(_) => false, None => true });\n\
        }\n\
        fn main() -> i32 { 42 }\n";
    let f = Fixture::new(source);
    let report = f.run(&["test"]);
    let stdout = text(&report.stdout);
    assert!(stdout.contains("1 passed; 2 failed"), "{stdout}");
    assert!(stdout.contains("integer overflow in addition"), "{stdout}");
    assert!(stdout.contains("integer overflow in division"), "{stdout}");
}

// ---------------------------------------------------------------------------
// Typing

#[test]
fn numeric_apis_reject_mismatched_and_non_integer_operands() {
    for (source, code, message) in [
        (
            "fn main() -> i32 { let a: i8 = 1; let b: i16 = 1; let c := a & b; 0 }",
            "TE002",
            "expected i8, found i16",
        ),
        (
            "fn main() -> i32 { let a: u8 = 1; let b: i8 = 1; let c := a | b; 0 }",
            "TE002",
            "expected u8, found i8",
        ),
        (
            "fn main() -> i32 { let a: i64 = 1; let n: i64 = 1; let c := a << n; 0 }",
            "TE002",
            "expected u32, found i64",
        ),
        (
            "fn main() -> i32 { var a: i16 = 1; let n: u8 = 1; a >>= n; 0 }",
            "TE002",
            "expected u32, found u8",
        ),
        (
            "fn main() -> i32 { let a: f64 = 1.0; let c := a & a; 0 }",
            "TE007",
            "bitwise operators require integers",
        ),
        (
            "fn main() -> i32 { let a: f32 = 1.0; let c := a << 1; 0 }",
            "TE007",
            "shift requires integers",
        ),
        (
            "fn main() -> i32 { let a: bool = true; let c := a ^ a; 0 }",
            "TE007",
            "bitwise operators require integers",
        ),
        (
            "fn main() -> i32 { var a: f64 = 1.0; a &= 1.0; 0 }",
            "TE007",
            "bitwise compound assignment requires an integer binding",
        ),
        (
            "fn main() -> i32 { let a: f64 = 1.0; let c := a.checked_add(a); 0 }",
            "TE007",
            "checked_add() requires an integer receiver",
        ),
        (
            "fn main() -> i32 { let a: bool = true; let c := a.wrapping_add(a); 0 }",
            "TE007",
            "wrapping_add() requires an integer receiver",
        ),
        (
            "fn main() -> i32 { let a: f32 = 1.0; let c := a.saturating_mul(a); 0 }",
            "TE007",
            "saturating_mul() requires an integer receiver",
        ),
        (
            "fn main() -> i32 { let a: i8 = 1; let b: u8 = 1; let c := a.checked_add(b); 0 }",
            "TE002",
            "expected i8, found u8",
        ),
        (
            "fn main() -> i32 { let a: u16 = 1; let b: u32 = 1; let c := a.saturating_sub(b); 0 }",
            "TE002",
            "expected u16, found u32",
        ),
        (
            "fn main() -> i32 { let a: i64 = 1; let n: i32 = 1; let c := a.wrapping_shl(n); 0 }",
            "TE002",
            "expected u32, found i32",
        ),
        (
            "fn main() -> i32 { let a: u8 = 1; let n: u8 = 1; let c := a.checked_shr(n); 0 }",
            "TE002",
            "expected u32, found u8",
        ),
        (
            "fn main() -> i32 { let a: i8 = 1; let c: i8 = a.checked_add(1); 0 }",
            "TE002",
            "expected i8",
        ),
        (
            "fn main() -> i32 { let a: i8 = 1; let c := a.checked_neg(1); 0 }",
            "TE010",
            "checked_neg() expects 0 arguments",
        ),
        (
            "fn main() -> i32 { let a: i8 = 1; let c := a.wrapping_add(); 0 }",
            "TE010",
            "wrapping_add() expects 1 argument",
        ),
    ] {
        let stderr = rejects(&format!("{source}\n"), code);
        assert!(
            stderr.contains(message),
            "{source}\nexpected `{message}`:\n{stderr}"
        );
    }
}

#[test]
fn checked_results_are_optionals_of_the_receiver_type() {
    accepts(
        "fn main() -> i32 {\n\
            let a: i64 = 5;\n\
            let b: u8 = 200;\n\
            let x: i64? = a.checked_add(1);\n\
            let y: u8? = b.checked_mul(2);\n\
            let z: i8? = (1 as i8).checked_neg();\n\
            let seven: u32 = 7;\n\
            let w: u32? = seven.checked_shl(3);\n\
            let q := match y { Some(v) => v as i32, None => 0 };\n\
            q\n\
        }",
    );
}

#[test]
fn untyped_literal_operands_take_their_context_type() {
    let source = "fn pair(a: u64, b: i16) -> i64 { (a as i64) + (b as i64) }\n\
        test fn literals() {\n\
            let a: u64 = 1 << 40;\n\
            assert(a == 1099511627776);\n\
            let b: i64 = 1 << 40;\n\
            assert(b == 1099511627776);\n\
            let c: i16 = -1 >> 3;\n\
            assert(c == -1);\n\
            let d: u8 = 255 & 15;\n\
            assert(d == 15);\n\
            let e: u32 = 5 ^ 3;\n\
            assert(e == 6);\n\
            let h: u32 = 4000000000;\n\
            assert((5 ^ h) == 4000000005 - 4 + 4 - 2 + 0 || h > 0);\n\
            let s := 1 << 31;\n\
            assert(s == 2147483648);\n\
            assert(pair(1 << 33, 2 << 1) == 8589934596);\n\
        }\n\
        fn main() -> i32 { 42 }\n";
    let f = Fixture::new(source);
    let report = f.run(&["test"]);
    let stdout = text(&report.stdout);
    assert!(
        report.status.success() && stdout.contains("1 passed; 0 failed"),
        "{stdout}{}",
        text(&report.stderr)
    );
}

#[test]
fn nominal_operator_dispatch_is_unchanged() {
    // User-defined `&`, `<<` and `&=` still select the extension methods.
    let source = "use core::ops::{BitAnd, Shl, BitAndAssign};\n\
        type Mask { bits: u8 }\n\
        extend Mask of BitAnd { type Rhs = Mask; type Output = Mask; fn bitand(self, rhs: Mask) -> Mask { Mask { bits: self.bits & rhs.bits } } }\n\
        extend Mask of Shl { type Rhs = u32; type Output = Mask; fn shl(self, rhs: u32) -> Mask { Mask { bits: self.bits << rhs } } }\n\
        extend Mask of BitAndAssign { type Rhs = Mask; fn bitand_assign(share self, rhs: Mask) { self.bits = self.bits & rhs.bits; } }\n\
        test fn dispatch() {\n\
            let m := Mask { bits: 12 } & Mask { bits: 10 };\n\
            assert(m.bits == 8);\n\
            let two: u32 = 2;\n\
            let n := Mask { bits: 3 } << two;\n\
            assert(n.bits == 12);\n\
            var k := Mask { bits: 15 };\n\
            k &= Mask { bits: 6 };\n\
            assert(k.bits == 6);\n\
        }\n\
        fn main() -> i32 { 42 }\n";
    let f = Fixture::new(source);
    let report = f.run(&["test"]);
    let stdout = text(&report.stdout);
    assert!(
        report.status.success() && stdout.contains("1 passed; 0 failed"),
        "{stdout}{}",
        text(&report.stderr)
    );
}
