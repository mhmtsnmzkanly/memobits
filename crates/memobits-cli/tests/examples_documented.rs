//! Every `examples/{guide,topics/*,apps/*}` project documents its exact stdout in its
//! README under `## Expected output`, in the first ```text block after that
//! heading. This test runs each project from source and as a standalone Wasm
//! artifact and compares stdout to that block. The README's `## Tests` heading
//! is followed by a ```text block holding the exact `mb test` summary line,
//! which must appear in the report; every project except those listed in
//! `WITHOUT_TESTS` must also run at least one test.
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

/// Projects with no `test fn` items: the host import needs a host profile.
const WITHOUT_TESTS: &[&str] = &["host-capability"];

/// Returns the first ```text fenced block after the `## Expected output`
/// heading, or `None` when either part is missing.
fn expected_output(readme: &str) -> Option<String> {
    text_block_after(readme, "## Expected output")
}

/// Returns the first ```text fenced block after `heading`.
fn text_block_after(readme: &str, heading: &str) -> Option<String> {
    let mut lines = readme.lines();
    lines.find(|line| line.trim_end() == heading)?;
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
    let tests = "## Tests\n\n```text\ntest result: ok. 2 passed; 0 failed; 0 filtered out\n```\n";
    assert_eq!(
        text_block_after(tests, "## Tests").as_deref(),
        Some("test result: ok. 2 passed; 0 failed; 0 filtered out\n")
    );
}

/// The number in `test result: ok. N passed; ...`.
fn passed_count(summary: &str) -> usize {
    summary
        .trim_start_matches("test result: ok. ")
        .split(' ')
        .next()
        .and_then(|count| count.parse().ok())
        .unwrap_or_else(|| panic!("not a passing summary line: {summary:?}"))
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
        let readme = fs::read_to_string(dir.join("README.md")).unwrap_or_default();
        let Some(summary) = text_block_after(&readme, "## Tests")
            .or_else(|| text_block_after(&readme, "## Running the guide's tests"))
        else {
            failures.push(format!(
                "{name}: README.md lacks a `## Tests` (guide: `## Running the guide's tests`) heading followed by a ```text block with the `mb test` summary line"
            ));
            continue;
        };
        let Some(expected) = expected_output(&readme) else {
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
            let summary = summary.trim_end();
            assert!(
                tests.lines().any(|line| line == summary),
                "{name}: documented summary `{summary}` not in the report:\n{tests}"
            );
            if WITHOUT_TESTS.contains(&name) {
                assert_eq!(passed_count(summary), 0, "{name}: documented count");
            } else {
                assert!(
                    passed_count(summary) >= 1,
                    "{name}: needs at least one test"
                );
            }
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

/// Every example project and standalone analysis input stays formatted: run
/// `mb fmt --project PATH` (or `mb fmt examples/analysis/*.mb`) after editing.
#[test]
fn every_example_is_formatted() {
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
    let mut failures = Vec::new();
    for manifest in &manifests {
        let output = mb(&["fmt", "--check", "--project", manifest.to_str().unwrap()]);
        if !output.status.success() {
            failures.push(format!(
                "{}: run `mb fmt --project {}`\n{}{}",
                manifest.display(),
                manifest.display(),
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
    }
    let mut analysis: Vec<String> = fs::read_dir(examples.join("analysis"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "mb"))
        .map(|path| path.to_str().unwrap().to_string())
        .collect();
    analysis.sort();
    assert!(!analysis.is_empty());
    let mut args = vec!["fmt", "--check"];
    args.extend(analysis.iter().map(String::as_str));
    let output = mb(&args);
    if !output.status.success() {
        failures.push(format!(
            "examples/analysis: run `mb fmt examples/analysis/*.mb`\n{}",
            String::from_utf8_lossy(&output.stdout)
        ));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
