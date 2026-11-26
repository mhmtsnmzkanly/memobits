//! Formatter guarantees over every `.mb` file in the repository: formatting
//! succeeds (which includes the formatter's own parse, syntax-tree, comment
//! and idempotence self-checks) and formatting the result changes nothing.
use memobits_diagnostics::SourceId;
use memobits_syntax::format::{format_source, FormatError};
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        if path.is_dir() {
            if name == "target" || name == "legacy" || name == ".git" || name == ".local-design" {
                continue;
            }
            collect(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "mb") {
            out.push(path);
        }
    }
}

pub fn repo_sources() -> Vec<PathBuf> {
    let mut files = Vec::new();
    collect(&repo_root(), &mut files);
    files.sort();
    files
}

#[test]
fn every_repository_source_formats_idempotently() {
    let files = repo_sources();
    assert!(files.len() >= 40, "found only {} files", files.len());
    let mut failures = Vec::new();
    let mut skipped = Vec::new();
    for file in &files {
        let text = std::fs::read_to_string(file).unwrap();
        match format_source(SourceId(0), &text) {
            Ok(once) => {
                let twice = format_source(SourceId(0), &once).unwrap();
                if once != twice {
                    failures.push(format!("{}: not idempotent", file.display()));
                }
            }
            Err(FormatError::Syntax(_)) => skipped.push(file.display().to_string()),
            Err(FormatError::Internal(message)) => {
                failures.push(format!("{}: {message}", file.display()))
            }
        }
    }
    eprintln!(
        "formatted {} files, {} do not parse: {skipped:?}",
        files.len(),
        skipped.len()
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Rust string literals of `source` (raw and escaped), in order.
fn rust_string_literals(source: &str) -> Vec<String> {
    let bytes = source.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'/' if source[i..].starts_with("//") => {
                i = source[i..].find('\n').map_or(bytes.len(), |n| i + n);
            }
            b'/' if source[i..].starts_with("/*") => {
                i = source[i..].find("*/").map_or(bytes.len(), |n| i + n + 2);
            }
            b'\'' => {
                // A char literal or a lifetime; skip a short quoted char.
                if bytes.get(i + 1) == Some(&b'\\') {
                    i += source[i..].find('\'').map_or(1, |_| 1);
                    let close = source[i + 2..].find('\'').map_or(1, |n| n + 3);
                    i += close;
                } else if bytes.get(i + 2) == Some(&b'\'') {
                    i += 3;
                } else if let Some(c) = source[i + 1..].chars().next() {
                    if source[i + 1 + c.len_utf8()..].starts_with('\'') {
                        i += c.len_utf8() + 2;
                    } else {
                        i += 1;
                    }
                } else {
                    i += 1;
                }
            }
            b'r' if matches!(bytes.get(i + 1), Some(b'"') | Some(b'#'))
                && (i == 0 || !(bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_')) =>
            {
                let mut j = i + 1;
                let mut hashes = 0;
                while bytes.get(j) == Some(&b'#') {
                    hashes += 1;
                    j += 1;
                }
                if bytes.get(j) != Some(&b'"') {
                    i += 1;
                    continue;
                }
                let terminator = format!("\"{}", "#".repeat(hashes));
                let start = j + 1;
                match source[start..].find(&terminator) {
                    Some(n) => {
                        out.push(source[start..start + n].to_string());
                        i = start + n + terminator.len();
                    }
                    None => break,
                }
            }
            b'"' => {
                let mut value = String::new();
                let mut j = i + 1;
                while j < bytes.len() && bytes[j] != b'"' {
                    if bytes[j] == b'\\' {
                        j += 1;
                        match bytes.get(j) {
                            Some(b'n') => value.push('\n'),
                            Some(b't') => value.push('\t'),
                            Some(b'r') => value.push('\r'),
                            Some(b'0') => value.push('\0'),
                            Some(b'\\') => value.push('\\'),
                            Some(b'"') => value.push('"'),
                            Some(b'\'') => value.push('\''),
                            Some(b'\n') => {
                                while bytes.get(j + 1).is_some_and(|b| b.is_ascii_whitespace()) {
                                    j += 1;
                                }
                            }
                            Some(b'u') => {
                                let end = source[j..].find('}').map_or(j, |n| j + n);
                                if let Ok(code) = u32::from_str_radix(&source[j + 2..end], 16) {
                                    value.extend(char::from_u32(code));
                                }
                                j = end;
                            }
                            Some(b'x') => {
                                if let Ok(code) = u8::from_str_radix(&source[j + 1..j + 3], 16) {
                                    value.push(code as char);
                                }
                                j += 2;
                            }
                            _ => {}
                        }
                        j += 1;
                    } else {
                        let c = source[j..].chars().next().unwrap();
                        value.push(c);
                        j += c.len_utf8();
                    }
                }
                out.push(value);
                i = j + 1;
            }
            _ => i += 1,
        }
    }
    out
}

fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            if entry.file_name() != "target" {
                rust_files(&path, out);
            }
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            out.push(path);
        }
    }
}

/// Every Memobits program embedded in the Rust tests (string literals that
/// parse as a non-empty module) formats, keeps its syntax tree and comments,
/// and formats idempotently. The embedded sources themselves are not changed.
#[test]
fn embedded_test_sources_format_idempotently() {
    let mut files = Vec::new();
    rust_files(&repo_root().join("crates"), &mut files);
    files.sort();
    let (mut literals, mut programs, mut failures) = (0usize, 0usize, Vec::new());
    for file in &files {
        let Ok(source) = std::fs::read_to_string(file) else {
            continue;
        };
        for text in rust_string_literals(&source) {
            literals += 1;
            if !text.contains("fn ") && !text.contains("type ") && !text.contains("use ") {
                continue;
            }
            let parsed = memobits_syntax::parse(SourceId(0), &text);
            if !parsed.diagnostics.is_empty() || parsed.module.items.is_empty() {
                continue;
            }
            programs += 1;
            match format_source(SourceId(0), &text) {
                Ok(once) => match format_source(SourceId(0), &once) {
                    Ok(twice) if twice == once => {}
                    other => {
                        failures.push(format!("{}: second pass {other:?}\n{text}", file.display()))
                    }
                },
                Err(error) => failures.push(format!("{}: {error:?}\n{text}", file.display())),
            }
        }
    }
    eprintln!(
        "{} Rust files, {literals} string literals, {programs} Memobits programs formatted",
        files.len()
    );
    assert!(programs >= 500, "only {programs} embedded programs found");
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures
            .iter()
            .take(5)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n----\n")
    );
}

/// Join the tokens with pseudo-random separators (space, newline, blank line).
fn random_layout(text: &str, seed: u64) -> String {
    let lexed = memobits_syntax::lex(SourceId(0), text);
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
    let mut out = String::new();
    for token in lexed.tokens.iter() {
        if matches!(token.kind, memobits_syntax::TokenKind::Eof) {
            break;
        }
        out.push_str(&text[token.span.start..token.span.end]);
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        out.push_str(match state % 7 {
            0 | 1 => "\n",
            2 => "\n\n",
            _ => " ",
        });
    }
    out
}

fn relayout(text: &str, separator: &str) -> String {
    let lexed = memobits_syntax::lex(SourceId(0), text);
    lexed
        .tokens
        .iter()
        .filter(|token| !matches!(token.kind, memobits_syntax::TokenKind::Eof))
        .map(|token| &text[token.span.start..token.span.end])
        .collect::<Vec<_>>()
        .join(separator)
}

/// Re-flowing a program (one line, one token per line, or three pseudo-random
/// layouts) must never break
/// the formatter: every variant still formats, keeps its syntax tree and is
/// idempotent, and the one-line and one-token-per-line variants agree
/// whenever the program has no comments.
#[test]
fn relaid_out_programs_format_idempotently() {
    let mut sources: Vec<String> = repo_sources()
        .iter()
        .filter_map(|file| std::fs::read_to_string(file).ok())
        .collect();
    let mut rust = Vec::new();
    rust_files(&repo_root().join("crates"), &mut rust);
    for file in &rust {
        if let Ok(source) = std::fs::read_to_string(file) {
            sources.extend(rust_string_literals(&source));
        }
    }
    let (mut checked, mut failures) = (0usize, Vec::new());
    for text in sources {
        if text.contains("//") || text.contains("/*") {
            continue;
        }
        let parsed = memobits_syntax::parse(SourceId(0), &text);
        if !parsed.diagnostics.is_empty() || parsed.module.items.is_empty() {
            continue;
        }
        checked += 1;
        let mut variants: Vec<(String, String)> = [" ", "\n"]
            .iter()
            .map(|separator| (separator.to_string(), relayout(&text, separator)))
            .collect();
        for seed in 1..=3u64 {
            variants.push((
                format!("seed{seed}"),
                random_layout(&text, seed + checked as u64),
            ));
        }
        for (separator, variant) in variants {
            let separator = separator.as_str();
            match format_source(SourceId(0), &variant) {
                Ok(once) => {
                    if !matches!(format_source(SourceId(0), &once), Ok(ref twice) if *twice == once)
                    {
                        failures.push(format!("not idempotent for {separator:?}:\n{variant}"));
                    }
                }
                Err(error) => failures.push(format!("{error:?} for {separator:?}:\n{variant}")),
            }
        }
    }
    eprintln!("{checked} comment-free programs relaid out five ways");
    assert!(checked >= 500, "only {checked} programs");
    assert!(
        failures.is_empty(),
        "{} failures, first:\n{}",
        failures.len(),
        failures.first().unwrap()
    );
}

/// Insert `comment` after every `every`-th token (`before` puts it ahead of
/// the token instead).
fn sprinkle(text: &str, every: usize, comment: &str, before: bool) -> String {
    let lexed = memobits_syntax::lex(SourceId(0), text);
    let mut out = String::new();
    let mut previous_end = 0;
    let mut count = 0;
    for token in &lexed.tokens {
        out.push_str(&text[previous_end..token.span.start]);
        if matches!(token.kind, memobits_syntax::TokenKind::Eof) {
            break;
        }
        count += 1;
        let hit = count % every == 0;
        if hit && before {
            out.push_str(comment);
        }
        out.push_str(&text[token.span.start..token.span.end]);
        if hit && !before {
            out.push_str(comment);
        }
        previous_end = token.span.end;
    }
    out
}

/// Comments in arbitrary token gaps survive in order, and the result is
/// still idempotent and tree-preserving (checked inside `format_source`).
#[test]
fn comments_between_arbitrary_tokens_are_preserved() {
    let mut sources: Vec<String> = repo_sources()
        .iter()
        .filter_map(|file| std::fs::read_to_string(file).ok())
        .collect();
    let mut rust = Vec::new();
    rust_files(&repo_root().join("crates"), &mut rust);
    for file in &rust {
        if let Ok(source) = std::fs::read_to_string(file) {
            sources.extend(rust_string_literals(&source));
        }
    }
    let (mut checked, mut failures) = (0usize, Vec::new());
    for (index, text) in sources.into_iter().enumerate() {
        if text.contains("//") || text.contains("/*") || index % 2 != 0 {
            continue;
        }
        let parsed = memobits_syntax::parse(SourceId(0), &text);
        if !parsed.diagnostics.is_empty() || parsed.module.items.is_empty() {
            continue;
        }
        checked += 1;
        let variants = [
            sprinkle(&text, 5, " /* c */ ", false),
            sprinkle(&text, 7, " // line\n", false),
            sprinkle(&text, 6, "\n// own\n", true),
            sprinkle(&text, 4, "/*a*/ /*b*/", true),
            sprinkle(&text, 9, " /* multi\n   line */ ", false),
            sprinkle(&text, 3, " // x\n\n// y\n\n", false),
            sprinkle(&text, 2, " /* c */ ", true),
            sprinkle(&text, 2, " // l\n", false),
            sprinkle(&text, 3, "\n// own\n\n", true),
            sprinkle(&text, 1, " /*i*/ ", false),
            sprinkle(&random_layout(&text, 12), 4, " // r\n", false),
            sprinkle(&random_layout(&text, 13), 5, "\n// r own\n", true),
        ];
        for variant in variants {
            match format_source(SourceId(0), &variant) {
                Ok(once) => {
                    if !matches!(format_source(SourceId(0), &once), Ok(ref twice) if *twice == once)
                    {
                        failures.push(format!("not idempotent:\n{variant}"));
                    }
                }
                Err(error) => failures.push(format!("{error:?}:\n{variant}")),
            }
        }
    }
    eprintln!("{checked} programs with comments sprinkled twelve ways");
    assert!(checked >= 100, "only {checked} programs");
    assert!(
        failures.is_empty(),
        "{} failures, first:\n{}",
        failures.len(),
        failures.first().unwrap()
    );
}
