//! D1: nested generic type arguments inside generic nominal method bodies and
//! signatures (`Pair<Wrap<T>>`, `Wrap<Pair<T>>`), and the specialization limit
//! for unbounded polymorphic recursion.

use std::{
    fs,
    io::Read,
    path::PathBuf,
    process::{Command, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Finished {
    success: bool,
    stdout: String,
    stderr: String,
}

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-d1-nested-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let fixture = Self(path);
        fixture.write(
            "project.toml",
            "[package]\nname='d1-nested'\nentry='main::main'\n",
        );
        fixture
    }

    fn write(&self, name: &str, text: &str) {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }

    /// Runs `mb` with a wall-clock guard so a specialization loop fails the
    /// test instead of hanging the suite.
    fn run(&self, args: &[&str]) -> Finished {
        let mut child = Command::new(env!("CARGO_BIN_EXE_mb"))
            .current_dir(&self.0)
            .args(args)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let started = Instant::now();
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            if started.elapsed() > Duration::from_secs(60) {
                let _ = child.kill();
                let _ = child.wait();
                panic!("`mb {}` did not finish within 60 seconds", args.join(" "));
            }
            std::thread::sleep(Duration::from_millis(20));
        };
        let mut stdout = String::new();
        let mut stderr = String::new();
        child
            .stdout
            .take()
            .unwrap()
            .read_to_string(&mut stdout)
            .unwrap();
        child
            .stderr
            .take()
            .unwrap()
            .read_to_string(&mut stderr)
            .unwrap();
        Finished {
            success: status.success(),
            stdout,
            stderr,
        }
    }

    fn both(&self, expected: &str) {
        let source = self.run(&["run"]);
        assert!(source.success, "source: {}", source.stderr);
        assert_eq!(source.stdout, expected);
        let build = self.run(&["build", "--output", "out.wasm"]);
        assert!(build.success, "build: {}", build.stderr);
        let wasm = self.run(&["run", "out.wasm"]);
        assert!(wasm.success, "wasm: {}", wasm.stderr);
        assert!(wasm.stderr.is_empty(), "wasm stderr: {}", wasm.stderr);
        assert_eq!(wasm.stdout, source.stdout);
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const SHAPES: &str = "\
pub type Pair<T> { pub first: T, pub second: T }
pub type Packet<const N: u32> { pub values: Array<u32, N> }
pub type Duo<T> { pub a: i32, pub b: i32 }
pub type Wrap<T> { pub value: T } extend {
    pub fn read(borrow self) -> T { self.value }
    pub fn twin(borrow self) -> Pair<Wrap<T>> {
        Pair<Wrap<T>> { first: Wrap<T> { value: self.value }, second: Wrap<T> { value: self.value } }
    }
    pub fn pairup(borrow self) -> Wrap<Pair<T>> {
        let inner: Pair<T> = Pair<T> { first: self.value, second: self.value };
        Wrap<Pair<T>> { value: inner }
    }
    pub fn total(borrow self) -> T { let t := self.twin(); t.first.value }
    pub fn deep(borrow self) -> T { let p := self.pairup(); p.value.first }
}
pub type Slot<T> { pub n: i32 } extend {
    pub fn duo(borrow self) -> Duo<Slot<T>> { Duo<Slot<T>> { a: self.n, b: self.n + 1 } }
    pub fn nested(borrow self) -> Slot<Duo<Slot<T>>> {
        let inner: Duo<Slot<T>> = self.duo();
        Slot<Duo<Slot<T>>> { n: inner.a }
    }
}
";

#[test]
fn bounded_nested_type_arguments_run_for_several_receivers_in_one_module() {
    let f = Fixture::new();
    f.write(
        "src/main.mb",
        &format!(
            "{SHAPES}
            fn main() -> i32 {{
                let a := Wrap<i32> {{ value: 20 }};
                let b := Wrap<u32> {{ value: 2 }};
                let t := a.twin();
                let q := b.pairup();
                let s1 := Slot<Packet<1>> {{ n: 5 }};
                let s3 := Slot<Packet<3>> {{ n: 7 }};
                let d1 := s1.duo();
                let d3 := s3.duo();
                let n1 := s1.nested();
                let n3 := s3.nested();
                a.total() + t.second.value + q.value.second as i32 + b.deep() as i32
                    + d1.a + d3.b + n1.n + n3.n - 27
            }}"
        ),
    );
    f.both("Result: i32(42)\n");
}

#[test]
fn bounded_nested_type_arguments_cross_a_public_direct_import() {
    let f = Fixture::new();
    f.write("src/shapes.mb", SHAPES);
    f.write(
        "src/main.mb",
        "use shapes;
         use shapes::{Wrap, Pair, Packet, Slot};
         fn main() -> i32 {
             let a := Wrap<i32> { value: 20 };
             let b := Wrap<u32> { value: 2 };
             let t := a.twin();
             let q := b.pairup();
             let s1 := Slot<Packet<1>> { n: 5 };
             let s3 := Slot<Packet<3>> { n: 7 };
             let d1 := s1.duo();
             let d3 := s3.duo();
             let n1 := s1.nested();
             let n3 := s3.nested();
             a.total() + t.second.value + q.value.second as i32 + b.deep() as i32
                 + d1.a + d3.b + n1.n + n3.n - 27
         }",
    );
    f.both("Result: i32(42)\n");

    // Without the direct module import the methods stay inactive.
    f.write(
        "src/main.mb",
        "use shapes::Wrap;
         fn main() -> i32 { let a := Wrap<i32> { value: 20 }; let t := a.twin(); t.first.value }",
    );
    let output = f.run(&["analyze-project"]);
    assert!(!output.success, "{}", output.stdout);
    assert!(output.stderr.contains("TE024"), "{}", output.stderr);
}

#[test]
fn unbounded_polymorphic_recursion_hits_the_specialization_limit() {
    let f = Fixture::new();
    // Phantom parameter: every level instantiates a deeper `Wrap<Wrap<..>>`.
    f.write(
        "src/main.mb",
        "type Wrap<T> { n: i32 } extend {
             fn grow(borrow self) -> i32 {
                 if self.n == 0 { 0 } else { let w := Wrap<Wrap<T>> { n: self.n - 1 }; w.grow() }
             }
         }
         fn main() -> i32 { let w := Wrap<i32> { n: 3 }; w.grow() }",
    );
    for args in [&["analyze-project"][..], &["run"][..], &["build"][..]] {
        let output = f.run(args);
        assert!(!output.success, "{args:?}: {}", output.stdout);
        assert!(
            output.stderr.contains("TE007"),
            "{args:?}: {}",
            output.stderr
        );
        assert!(
            output.stderr.contains(
                "generic inherent method specialization limit exceeded (maximum 256 distinct methods)"
            ),
            "{args:?}: {}",
            output.stderr
        );
    }

    // The same recursion through an owned field that really nests the value.
    f.write(
        "src/main.mb",
        "type Wrap<T> { value: T } extend {
             fn grow(self, n: i32) -> i32 {
                 if n == 0 { 0 } else { let w := Wrap<Wrap<T>> { value: self }; w.grow(n - 1) }
             }
         }
         fn main() -> i32 { let w := Wrap<i32> { value: 21 }; w.grow(3) }",
    );
    let output = f.run(&["analyze-project"]);
    assert!(!output.success, "{}", output.stdout);
    assert!(
        output.stderr.contains(
            "generic inherent method specialization limit exceeded (maximum 256 distinct methods)"
        ),
        "{}",
        output.stderr
    );
}
