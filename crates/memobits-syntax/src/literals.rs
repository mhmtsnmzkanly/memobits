//! Numeric literal lexing.
//!
//! Integers may be written in decimal, hexadecimal (`0x`, `0X`), binary (`0b`)
//! or octal (`0o`); `_` separates digits in every integer and float literal.
//! The lexer hands the rest of the compiler one canonical spelling: radix
//! literals become decimal and separators are removed, so contextual typing,
//! range checks, constants and patterns see the same text as for a plain
//! decimal literal. Source spans still cover the original spelling.

use crate::{Diagnostic, SourceId, Span};

/// Lex a number that starts with an ASCII digit at `start`. Returns the end
/// offset and the canonical spelling. Malformed forms push SE001 and yield
/// `"0"` so later phases do not cascade.
pub(crate) fn lex_number(
    source: SourceId,
    text: &str,
    start: usize,
    diagnostics: &mut Vec<Diagnostic>,
) -> (usize, String) {
    let bytes = text.as_bytes();
    if bytes[start] == b'0' {
        let radix = match bytes.get(start + 1) {
            Some(b'x' | b'X') => Some((16, "hexadecimal", "0x")),
            Some(b'b') => Some((2, "binary", "0b")),
            Some(b'o') => Some((8, "octal", "0o")),
            _ => None,
        };
        if let Some((radix, name, prefix)) = radix {
            return lex_radix(source, text, start, radix, name, prefix, diagnostics);
        }
    }
    let mut i = start;
    let mut error = None;
    i = digit_run(bytes, i, &mut error);
    if bytes.get(i) == Some(&b'.') && bytes.get(i + 1).is_some_and(u8::is_ascii_digit) {
        i += 1;
        i = digit_run(bytes, i, &mut error);
    }
    if matches!(bytes.get(i), Some(b'e' | b'E')) {
        i += 1;
        if matches!(bytes.get(i), Some(b'+' | b'-')) {
            i += 1;
        }
        if bytes.get(i).is_some_and(u8::is_ascii_digit) {
            i = digit_run(bytes, i, &mut error);
        } else {
            error = Some("expected exponent digits");
            while bytes
                .get(i)
                .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
            {
                i += 1;
            }
        }
    }
    let span = Span {
        source,
        start,
        end: i,
    };
    if let Some(message) = error {
        diagnostics.push(crate::diagnostic(1, span, message));
        return (i, "0".into());
    }
    (i, text[start..i].replace('_', ""))
}

/// A run of digits and `_` starting at a digit; a trailing `_` is an error.
fn digit_run(bytes: &[u8], mut i: usize, error: &mut Option<&'static str>) -> usize {
    while bytes
        .get(i)
        .is_some_and(|byte| byte.is_ascii_digit() || *byte == b'_')
    {
        i += 1;
    }
    if bytes[i - 1] == b'_' {
        *error = Some("a digit separator must be followed by a digit");
    }
    i
}

fn lex_radix(
    source: SourceId,
    text: &str,
    start: usize,
    radix: u32,
    name: &str,
    prefix: &str,
    diagnostics: &mut Vec<Diagnostic>,
) -> (usize, String) {
    let digits_start = start + 2;
    let mut i = digits_start;
    while text[i..]
        .chars()
        .next()
        .is_some_and(|c| c == '_' || c.is_alphanumeric())
    {
        i += text[i..].chars().next().unwrap().len_utf8();
    }
    let span = Span {
        source,
        start,
        end: i,
    };
    let body = &text[digits_start..i];
    let message = if body.starts_with('_') {
        Some(format!(
            "a digit separator is not allowed directly after `{prefix}`"
        ))
    } else if body.is_empty() {
        Some(format!("expected {name} digits after `{prefix}`"))
    } else if body.ends_with('_') {
        Some("a digit separator must be followed by a digit".to_owned())
    } else if let Some(bad) = body.chars().find(|c| *c != '_' && !c.is_digit(radix)) {
        Some(format!("invalid digit '{bad}' in {name} literal"))
    } else {
        None
    };
    if let Some(message) = message {
        diagnostics.push(crate::diagnostic(1, span, message));
        return (i, "0".into());
    }
    let digits: String = body.chars().filter(|c| *c != '_').collect();
    match u128::from_str_radix(&digits, radix) {
        Ok(value) => (i, value.to_string()),
        Err(_) => {
            diagnostics.push(crate::diagnostic(
                1,
                span,
                format!("{name} literal is too large"),
            ));
            (i, "0".into())
        }
    }
}
