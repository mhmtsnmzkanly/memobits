//! S5-1: `mb fmt`. Exit codes, `--check`, parse errors, project and file
//! modes, and the guarantee that formatting never changes behavior.
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

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("memobits-s5fmt-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

const MESSY: &str = "fn  main( )->i32{let a:=1+2*3;  // keep me\n    Ok( a )}\n";
const TIDY: &str = "fn main() -> i32 {\n    let a := 1 + 2 * 3; // keep me\n    Ok(a)\n}\n";

#[test]
fn formats_files_in_place_and_is_then_stable() {
    let dir = scratch("inplace");
    let file = dir.join("a.mb");
    fs::write(&file, MESSY).unwrap();
    let path = file.to_str().unwrap();

    let first = mb(&["fmt", path]);
    assert_eq!(first.status.code(), Some(0), "{}", stderr(&first));
    assert!(stdout(&first).contains("formatted "), "{}", stdout(&first));
    assert!(stdout(&first).contains("1 file(s) reformatted, 0 unchanged"));
    assert_eq!(fs::read_to_string(&file).unwrap(), TIDY);

    let second = mb(&["fmt", path]);
    assert_eq!(second.status.code(), Some(0));
    assert!(stdout(&second).contains("0 file(s) reformatted, 1 unchanged"));
    assert!(!stdout(&second).contains("formatted a.mb"));
    assert_eq!(fs::read_to_string(&file).unwrap(), TIDY);
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn check_lists_files_exits_one_and_writes_nothing() {
    let dir = scratch("check");
    let messy = dir.join("messy.mb");
    let tidy = dir.join("tidy.mb");
    fs::write(&messy, MESSY).unwrap();
    fs::write(&tidy, TIDY).unwrap();

    let output = mb(&[
        "fmt",
        "--check",
        messy.to_str().unwrap(),
        tidy.to_str().unwrap(),
    ]);
    assert_eq!(output.status.code(), Some(1));
    let report = stdout(&output);
    assert!(report.contains("would reformat "), "{report}");
    assert!(report.contains("messy.mb"), "{report}");
    assert!(!report.contains("tidy.mb"), "{report}");
    assert!(report.contains("lines)"), "diff summary: {report}");
    assert!(report.contains("1 file(s) would be reformatted, 1 already formatted"));
    assert_eq!(
        fs::read_to_string(&messy).unwrap(),
        MESSY,
        "--check must not write"
    );

    let clean = mb(&["fmt", "--check", tidy.to_str().unwrap()]);
    assert_eq!(clean.status.code(), Some(0));
    assert!(!stdout(&clean).contains("would reformat"));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn parse_errors_are_reported_and_the_file_is_left_untouched() {
    let dir = scratch("errors");
    let broken = dir.join("broken.mb");
    let source = "fn main( {  let x := ;\n";
    fs::write(&broken, source).unwrap();
    let fine = dir.join("fine.mb");
    fs::write(&fine, MESSY).unwrap();

    let output = mb(&["fmt", broken.to_str().unwrap(), fine.to_str().unwrap()]);
    assert_eq!(output.status.code(), Some(1));
    let errors = stderr(&output);
    assert!(errors.contains("SE00"), "{errors}");
    assert!(errors.contains("broken.mb"), "{errors}");
    assert_eq!(fs::read_to_string(&broken).unwrap(), source);
    // The other file is still formatted.
    assert_eq!(fs::read_to_string(&fine).unwrap(), TIDY);

    let check = mb(&["fmt", "--check", broken.to_str().unwrap()]);
    assert_eq!(check.status.code(), Some(1));
    assert!(stderr(&check).contains("SE00"));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn project_mode_formats_every_source_module() {
    let dir = scratch("project");
    fs::create_dir_all(dir.join("src")).unwrap();
    fs::write(
        dir.join("project.toml"),
        "[package]\nname = \"fmtdemo\"\nversion = \"0.1.0\"\nentry = \"main\"\n",
    )
    .unwrap();
    fs::write(
        dir.join("src/main.mb"),
        "use util::add;\nfn main()->i32{ Ok(add(1,2)) }\n",
    )
    .unwrap();
    fs::write(
        dir.join("src/util.mb"),
        "pub fn add(a:i32,b:i32)->i32{a+b}\n",
    )
    .unwrap();
    let manifest = dir.join("project.toml");
    let manifest = manifest.to_str().unwrap();

    let check = mb(&["fmt", "--check", "--project", manifest]);
    assert_eq!(
        check.status.code(),
        Some(1),
        "{}{}",
        stdout(&check),
        stderr(&check)
    );
    assert!(stdout(&check).contains("main.mb"));
    assert!(stdout(&check).contains("util.mb"));

    let run = mb(&["fmt", "--project", manifest]);
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    assert!(fs::read_to_string(dir.join("src/main.mb"))
        .unwrap()
        .contains("fn main() -> i32 {"));
    assert!(fs::read_to_string(dir.join("src/util.mb"))
        .unwrap()
        .contains("pub fn add(a: i32, b: i32) -> i32 { a + b }"));
    let again = mb(&["fmt", "--check", "--project", manifest]);
    assert_eq!(again.status.code(), Some(0));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn usage_errors_exit_one() {
    for args in [
        vec!["fmt", "--bogus"],
        vec!["fmt", "--project"],
        vec!["fmt", "--project", "a.toml", "b.mb"],
    ] {
        let output = mb(&args);
        assert_eq!(output.status.code(), Some(1), "{args:?}");
        assert!(
            stderr(&output).contains("PE004"),
            "{args:?}: {}",
            stderr(&output)
        );
    }
}

/// Re-flow a source into one token per line (comments dropped): the worst
/// layout the formatter must repair without touching behavior.
fn one_token_per_line(text: &str) -> String {
    let lexed = memobits_syntax::lex(memobits_diagnostics::SourceId(0), text);
    lexed
        .tokens
        .iter()
        .filter(|token| !matches!(token.kind, memobits_syntax::TokenKind::Eof))
        .map(|token| &text[token.span.start..token.span.end])
        .collect::<Vec<_>>()
        .join("\n")
        + "\n"
}

fn copy_tree(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap().flatten() {
        let path = entry.path();
        let target = to.join(entry.file_name());
        if path.is_dir() {
            if entry.file_name() != "target" {
                copy_tree(&path, &target);
            }
        } else {
            fs::copy(&path, &target).unwrap();
        }
    }
}

fn mb_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).unwrap().flatten() {
        let path = entry.path();
        if path.is_dir() {
            mb_files(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "mb") {
            out.push(path);
        }
    }
}

/// Formatting every example from a hostile layout (one token per line, no
/// comments) is stable and `mb run` / `mb test` behave identically.
#[test]
fn formatting_scrambled_examples_preserves_behavior() {
    let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut projects: Vec<PathBuf> = vec![examples.join("guide")];
    for group in ["topics", "apps"] {
        for entry in fs::read_dir(examples.join(group)).unwrap().flatten() {
            if entry.path().join("project.toml").is_file() {
                projects.push(entry.path());
            }
        }
    }
    projects.sort();
    assert!(projects.len() >= 13);
    let temp = scratch("scrambled");
    let mut failures = Vec::new();
    for project in &projects {
        let name = project.file_name().unwrap().to_str().unwrap();
        let copy = temp.join(name);
        copy_tree(project, &copy);
        let mut sources = Vec::new();
        mb_files(&copy.join("src"), &mut sources);
        for source in &sources {
            let text = fs::read_to_string(source).unwrap();
            fs::write(source, one_token_per_line(&text)).unwrap();
        }
        let manifest = copy.join("project.toml");
        let manifest = manifest.to_str().unwrap();
        let fmt = mb(&["fmt", "--project", manifest]);
        if fmt.status.code() != Some(0) {
            failures.push(format!("{name}: fmt failed: {}", stderr(&fmt)));
            continue;
        }
        let again = mb(&["fmt", "--check", "--project", manifest]);
        if again.status.code() != Some(0) {
            failures.push(format!(
                "{name}: formatting is not stable: {}",
                stdout(&again)
            ));
        }
        let original_manifest = project.join("project.toml");
        let original_manifest = original_manifest.to_str().unwrap();
        for command in [vec!["run"], vec!["test"]] {
            let mut before = command.clone();
            before.extend(["--project", original_manifest]);
            let mut after = command.clone();
            after.extend(["--project", manifest]);
            let (before, after) = (mb(&before), mb(&after));
            if stdout(&before) != stdout(&after)
                || before.status.code() != after.status.code()
                || stderr(&before) != stderr(&after)
            {
                failures.push(format!("{name}: `mb {}` output changed", command[0]));
            }
        }
    }
    let _ = fs::remove_dir_all(&temp);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
