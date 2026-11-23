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
            "memobits-host-capability-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::create_dir(path.join("src")).unwrap();
        Self(path)
    }

    fn write(&self, name: &str, bytes: &[u8]) {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, bytes).unwrap();
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

fn wasm_section(module: &mut Vec<u8>, id: u8, payload: &[u8]) {
    assert!(payload.len() < 128, "fixture section uses one-byte lengths");
    module.extend([id, payload.len() as u8]);
    module.extend_from_slice(payload);
}

fn wasm_name(name: &str, output: &mut Vec<u8>) {
    assert!(name.len() < 128, "fixture name uses one-byte lengths");
    output.push(name.len() as u8);
    output.extend_from_slice(name.as_bytes());
}

// Imports memobits:console.write_i32, calls it with 42, then returns 7 from
// `main`. `import_type` selects the import's Wasm type for rejection coverage.
fn guest_module(import_type: u8, body: &[u8]) -> Vec<u8> {
    let mut module = b"\0asm\x01\0\0\0".to_vec();

    let types = [0x02, 0x60, 0x01, 0x7f, 0x00, 0x60, 0x00, 0x01, 0x7f];
    wasm_section(&mut module, 1, &types);

    let mut import = vec![0x01];
    wasm_name("memobits:console", &mut import);
    wasm_name("write_i32", &mut import);
    import.extend([0x00, import_type]);
    wasm_section(&mut module, 2, &import);
    wasm_section(&mut module, 3, &[0x01, 0x01]);

    let mut exports = vec![0x01];
    wasm_name("main", &mut exports);
    exports.extend([0x00, 0x01]);
    wasm_section(&mut module, 7, &exports);

    let mut code = vec![0x01, body.len() as u8];
    code.extend_from_slice(body);
    wasm_section(&mut module, 10, &code);
    module
}

fn guest_module_with_console_write() -> Vec<u8> {
    guest_module(0, &[0x00, 0x41, 0x2a, 0x10, 0x00, 0x41, 0x07, 0x0b])
}

const HOST_MANIFEST: &str = "[package]\nname='host-guest'\nentry='main::main'\n[host]\nprofile='cli'\n[[host.imports]]\nmodule='memobits:console'\nname='write_i32'\nparams=['i32']\nresult='unit'\n";

#[test]
fn cli_profile_links_one_typed_capability_for_wasm_guests() {
    let fixture = Fixture::new();
    fixture.write("project.toml", HOST_MANIFEST.as_bytes());
    fixture.write("guest.wasm", &guest_module_with_console_write());

    let output = fixture.run(&["run", "guest.wasm", "--project", "project.toml"]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(output.stdout, b"Host i32: 42\nResult: i32(7)\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn source_extern_declaration_calls_typed_import_in_run_build_and_artifact_run() {
    let fixture = Fixture::new();
    fixture.write("project.toml", HOST_MANIFEST.as_bytes());
    fixture.write(
        "src/main.mb",
        b"extern fn write_i32(value: i32); fn main() -> i32 { write_i32(42); 7 }",
    );

    let source = fixture.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Host i32: 42\nResult: i32(7)\n");

    let build = fixture.run(&["build", "--output", "host-guest.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = fixture.run(&["run", "host-guest.wasm", "--project", "project.toml"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn source_extern_must_match_manifest_profile_and_signature() {
    let fixture = Fixture::new();
    fixture.write(
        "project.toml",
        b"[package]\nname='host-mismatch'\nentry='main::main'\n",
    );
    fixture.write(
        "src/main.mb",
        b"extern fn write_i32(value: i32); fn main() { write_i32(42); }",
    );
    let missing = fixture.run(&["run"]);
    assert!(!missing.status.success(), "{missing:?}");
    assert!(missing.stdout.is_empty());
    assert!(String::from_utf8_lossy(&missing.stderr).contains("match [host.imports]"));

    fixture.write("project.toml", HOST_MANIFEST.as_bytes());
    fixture.write(
        "src/main.mb",
        b"extern fn write_i32(value: u32); fn main() { write_i32(42); }",
    );
    let wrong_signature = fixture.run(&["run"]);
    assert!(!wrong_signature.status.success(), "{wrong_signature:?}");
    assert!(wrong_signature.stdout.is_empty());
    assert!(String::from_utf8_lossy(&wrong_signature.stderr)
        .contains("must be declared in the application root"));
}

#[test]
fn undeclared_and_mismatched_guest_imports_fail_before_guest_execution() {
    let fixture = Fixture::new();
    fixture.write(
        "project.toml",
        b"[package]\nname='no-host'\nentry='main::main'\n",
    );
    fixture.write("guest.wasm", &guest_module_with_console_write());

    let undeclared = fixture.run(&["run", "guest.wasm", "--project", "project.toml"]);
    assert!(!undeclared.status.success());
    assert!(undeclared.stdout.is_empty());
    assert!(String::from_utf8_lossy(&undeclared.stderr).contains("RE002"));

    fixture.write("project.toml", HOST_MANIFEST.as_bytes());
    // Import type 1 is () -> i32. This body calls that signature, discards its
    // result, then returns 7; the configured profile must reject the mismatch.
    let mismatched = guest_module(1, &[0x00, 0x10, 0x00, 0x1a, 0x41, 0x07, 0x0b]);
    fixture.write("mismatched.wasm", &mismatched);
    let mismatch = fixture.run(&["run", "mismatched.wasm", "--project", "project.toml"]);
    assert!(!mismatch.status.success());
    assert!(mismatch.stdout.is_empty());
    assert!(String::from_utf8_lossy(&mismatch.stderr).contains("RE002"));
}
