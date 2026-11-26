//! Shared diagnostics with stable codes and UTF-8 byte source locations.
//!
//! Internal compiler failures must be reported separately, not assigned a user
//! diagnostic code. Display columns count Unicode scalars, not terminal cells.

use std::{fmt, str::FromStr};

/// Stable diagnostic groups. Severity is independent of this classification.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Category {
    Syntax,
    Name,
    Type,
    Borrow,
    Module,
    StaticOperation,
    Project,
    Runtime,
    /// Non-failing migration warnings (`MW`); always rendered with warning severity.
    Migration,
}

impl Category {
    pub const fn prefix(self) -> &'static str {
        match self {
            Self::Syntax => "SE",
            Self::Name => "NE",
            Self::Type => "TE",
            Self::Borrow => "BE",
            Self::Module => "ME",
            Self::StaticOperation => "LE",
            Self::Project => "PE",
            Self::Runtime => "RE",
            Self::Migration => "MW",
        }
    }
}

/// A group plus a number in 1..=999, rendered as e.g. `SE001`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct DiagnosticCode {
    category: Category,
    number: u16,
}

impl DiagnosticCode {
    pub fn new(category: Category, number: u16) -> Result<Self, InvalidCode> {
        if (1..=999).contains(&number) {
            Ok(Self { category, number })
        } else {
            Err(InvalidCode)
        }
    }

    pub const fn category(self) -> Category {
        self.category
    }
    pub const fn number(self) -> u16 {
        self.number
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InvalidCode;

impl fmt::Display for InvalidCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("expected a diagnostic group followed by three digits (001..999)")
    }
}
impl std::error::Error for InvalidCode {}

impl fmt::Display for DiagnosticCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{:03}", self.category.prefix(), self.number)
    }
}

impl FromStr for DiagnosticCode {
    type Err = InvalidCode;
    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let bytes = value.as_bytes();
        if bytes.len() != 5 || !bytes[2..].iter().all(u8::is_ascii_digit) {
            return Err(InvalidCode);
        }
        let category = match &bytes[..2] {
            b"SE" => Category::Syntax,
            b"NE" => Category::Name,
            b"TE" => Category::Type,
            b"BE" => Category::Borrow,
            b"ME" => Category::Module,
            b"LE" => Category::StaticOperation,
            b"PE" => Category::Project,
            b"RE" => Category::Runtime,
            b"MW" => Category::Migration,
            _ => return Err(InvalidCode),
        };
        let number = bytes[2..]
            .iter()
            .fold(0u16, |n, b| n * 10 + u16::from(b - b'0'));
        Self::new(category, number)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Severity {
    Error,
    Warning,
    Note,
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Error => "error",
            Self::Warning => "warning",
            Self::Note => "note",
        })
    }
}

/// Identity assigned by the caller's source store.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SourceId(pub u32);

/// Half-open UTF-8 byte offsets. Empty spans indicate insertion points.
/// Validation against the corresponding text happens at rendering time.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Span {
    pub source: SourceId,
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagnostic {
    pub code: DiagnosticCode,
    pub severity: Severity,
    pub message: String,
    pub span: Option<Span>,
    /// Secondary locations that explain the primary one, rendered as notes in
    /// order after the primary snippet.
    pub labels: Vec<Label>,
    pub help: Option<String>,
}

/// A secondary source location with an explanation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

impl Diagnostic {
    pub fn new(code: DiagnosticCode, severity: Severity, message: impl Into<String>) -> Self {
        Self {
            code,
            severity,
            message: message.into(),
            span: None,
            labels: Vec::new(),
            help: None,
        }
    }

    /// Attach a secondary location, e.g. where a conflicting loan began.
    pub fn with_label(mut self, span: Span, message: impl Into<String>) -> Self {
        self.labels.push(Label {
            span,
            message: message.into(),
        });
        self
    }
}

/// Borrowed source data; ownership and source lookup stay with the caller.
#[derive(Clone, Copy, Debug)]
pub struct SourceFile<'a> {
    pub id: SourceId,
    pub name: &'a str,
    pub text: &'a str,
}

/// Render plain text with the first affected line and a caret range.
/// Missing sources and invalid spans retain the diagnostic and raw location.
/// Secondary labels are rendered only when they point into `source`; use
/// [`render_with`] when labels may live in other files.
pub fn render(diagnostic: &Diagnostic, source: Option<SourceFile<'_>>) -> String {
    render_with(diagnostic, &|id| source.filter(|s| s.id == id))
}

/// Like [`render`], looking each span's source up by id.
pub fn render_with<'a>(
    diagnostic: &Diagnostic,
    lookup: &dyn Fn(SourceId) -> Option<SourceFile<'a>>,
) -> String {
    use fmt::Write;
    let mut output = format!(
        "{}[{}]: {}\n",
        diagnostic.severity, diagnostic.code, diagnostic.message
    );
    if let Some(span) = diagnostic.span {
        write_snippet(&mut output, span, lookup(span.source));
    }
    for label in &diagnostic.labels {
        let _ = writeln!(output, " note: {}", label.message);
        write_snippet(&mut output, label.span, lookup(label.span.source));
    }
    if let Some(help) = &diagnostic.help {
        let _ = writeln!(output, " help: {help}");
    }
    output
}

/// Append the `-->` location line and the caret snippet for a position that is
/// already resolved (1-based `line` and `column`, `width` in characters). Used
/// by reports that carry their own line text, such as runtime traps.
pub fn write_location(
    output: &mut String,
    name: &str,
    line: usize,
    column: usize,
    width: usize,
    text: &str,
) {
    use fmt::Write;
    let _ = writeln!(output, " --> {name}:{line}:{column}");
    let _ = writeln!(output, " {line} | {text}");
    let _ = writeln!(
        output,
        "   | {}{}",
        " ".repeat(column.saturating_sub(1)),
        "^".repeat(width.max(1))
    );
}

fn write_snippet(output: &mut String, span: Span, source: Option<SourceFile<'_>>) {
    use fmt::Write;
    let valid = source.filter(|s| {
        s.id == span.source
            && span.start <= span.end
            && span.end <= s.text.len()
            && s.text.is_char_boundary(span.start)
            && s.text.is_char_boundary(span.end)
    });
    if let Some(source) = valid {
        let before = &source.text[..span.start];
        let line = before.bytes().filter(|&b| b == b'\n').count() + 1;
        let line_start = before.rfind('\n').map_or(0, |n| n + 1);
        let line_end = source.text[span.start..]
            .find('\n')
            .map_or(source.text.len(), |n| span.start + n);
        let text = source.text[line_start..line_end].trim_end_matches('\r');
        let column = source.text[line_start..span.start].chars().count();
        let width = source.text[span.start..span.end.min(line_end)]
            .chars()
            .count()
            .max(1);
        write_location(output, source.name, line, column + 1, width, text);
        if span.end > line_end {
            output.push_str("   = span continues on following lines\n");
        }
    } else {
        let _ = writeln!(
            output,
            " --> source {} bytes {}..{} (source unavailable or invalid span)",
            span.source.0, span.start, span.end
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn codes_round_trip_all_categories_and_boundaries() {
        for category in [
            Category::Syntax,
            Category::Name,
            Category::Type,
            Category::Borrow,
            Category::Module,
            Category::StaticOperation,
            Category::Project,
            Category::Runtime,
            Category::Migration,
        ] {
            for number in [1, 42, 999] {
                let code = DiagnosticCode::new(category, number).unwrap();
                assert_eq!(code.to_string().parse(), Ok(code));
                assert_eq!(code.category(), category);
                assert_eq!(code.number(), number);
            }
        }
        assert!(DiagnosticCode::new(Category::Syntax, 0).is_err());
        assert!(DiagnosticCode::new(Category::Syntax, 1000).is_err());
    }

    #[test]
    fn rejects_noncanonical_codes_without_panicking_on_unicode() {
        for value in [
            "", "SE000", "SE01", "SE1000", "se001", "XX001", "SE+01", "SE١", "é001", "SE01 ",
        ] {
            assert!(value.parse::<DiagnosticCode>().is_err(), "{value}");
        }
    }
}
