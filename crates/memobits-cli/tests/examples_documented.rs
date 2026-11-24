//! Every `examples/{guide,topics/*,apps/*}` project documents its exact stdout in its
//! README under `## Expected output`, in the first ```text block after that
//! heading. This test runs each project from source and as a standalone Wasm
//! artifact and compares stdout to that block.
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

fn mb(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_mb"))
        .args(args)
        .output()
        .unwrap()
}

/// Returns the first ```text fenced block after the `## Expected output`
/// heading, or `None` when either part is missing.
fn expected_output(readme: &str) -> Option<String> {
    let mut lines = readme.lines();
    lines.find(|line| line.trim_end() == "## Expected output")?;
    lines.find(|line| line.trim_end() == "```text")?;
    let mut block = String::new();
    for line in lines {
        if line.trim_end() == "```" {
            return Some(block);
        }
        block.push_str(line);
        block.push('\n');
    }
    None
}

fn check_clean_success(label: &str, output: &Output) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{label}: {output:?}");
    assert!(stderr.is_empty(), "{label}: unexpected stderr:\n{stderr}");
}

fn artifact_stdout(label: &str, output: &Output) -> String {
    check_clean_success(label, output);
    String::from_utf8(output.stdout.clone()).unwrap()
}

#[test]
fn expected_output_convention_is_parsed_strictly() {
    let text = "# T\n\n## Expected output\n\nprose\n\n```text\nA\nB\n```\n\n```text\nC\n```\n";
    assert_eq!(expected_output(text).as_deref(), Some("A\nB\n"));
    assert_eq!(expected_output("# T\n```text\nA\n```\n"), None);
    assert_eq!(expected_output("## Expected output\nno block\n"), None);
    assert_eq!(expected_output("## Expected output\n```text\nA\n"), None);
}

#[test]
fn every_example_project_documents_and_matches_its_output() {
    let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut manifests: Vec<PathBuf> = vec![examples.join("guide/project.toml")];
    for group in ["topics", "apps"] {
        manifests.extend(
            fs::read_dir(examples.join(group))
                .unwrap()
                .map(|entry| entry.unwrap().path().join("project.toml")),
        );
    }
    manifests.retain(|manifest| manifest.is_file());
    manifests.sort();
    assert!(manifests.len() >= 13, "found {manifests:?}");

    let temp = std::env::temp_dir().join(format!("memobits-examples-{}", std::process::id()));
    fs::create_dir_all(&temp).unwrap();
    let mut failures = Vec::new();
    for manifest in &manifests {
        let dir = manifest.parent().unwrap();
        let name = dir.file_name().unwrap().to_str().unwrap();
        let Some(expected) = fs::read_to_string(dir.join("README.md"))
            .ok()
            .and_then(|readme| expected_output(&readme))
        else {
            failures.push(format!(
                "{name}: README.md lacks a `## Expected output` heading followed by a ```text block"
            ));
            continue;
        };
        let manifest_arg = manifest.to_str().unwrap();
        let wasm = temp.join(format!("{name}.wasm"));
        let wasm_arg = wasm.to_str().unwrap();

        let check = mb(&["check", "--project", manifest_arg]);
        let source = mb(&["run", "--project", manifest_arg]);
        let build = mb(&["build", "--project", manifest_arg, "--output", wasm_arg]);
        // The manifest is passed again so host-capability profiles apply.
        let artifact = mb(&["run", wasm_arg, "--project", manifest_arg]);
        let tests = mb(&["test", "--project", manifest_arg]);
        let result = std::panic::catch_unwind(|| {
            check_clean_success(&format!("{name} check"), &check);
            check_clean_success(&format!("{name} build"), &build);
            let tests = artifact_stdout(&format!("{name} test"), &tests);
            assert!(tests.contains("test result: ok."), "{name}: {tests}");
            assert!(
                tests.contains(" tests\n") || tests.contains("running 1 test\n"),
                "{name}: {tests}"
            );
            let source = artifact_stdout(&format!("{name} source run"), &source);
            let artifact = artifact_stdout(&format!("{name} wasm run"), &artifact);
            assert_eq!(source, expected, "{name}: source stdout");
            assert_eq!(artifact, expected, "{name}: standalone Wasm stdout");
        });
        if let Err(panic) = result {
            let message = panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default();
            failures.push(format!("{name}: {message}"));
        }
    }
    let _ = fs::remove_dir_all(&temp);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
