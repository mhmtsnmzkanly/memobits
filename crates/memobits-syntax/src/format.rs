//! Canonical source formatter behind `mb fmt`.
//!
//! The formatter works on the token stream plus the comments that the lexer
//! skips, and uses the parsed syntax tree only as a side channel (which `<`
//! tokens open generic argument lists, where each top-level item starts). It
//! never rewrites a token: literals, identifiers and parentheses are printed
//! exactly as written, so formatting cannot change meaning. Only the white
//! space between tokens is chosen by the formatter.
//!
//! Every result is verified before it is returned: the output must parse, its
//! syntax tree must equal the input's modulo positions, every comment must
//! survive in order, and formatting the output again must change nothing.
//! A failed check is reported as [`FormatError::Internal`] and callers leave
//! the file untouched.
use crate::{lex, parse, Module, Token, TokenKind};
use memobits_diagnostics::{Diagnostic, SourceId};

/// Maximum line width in characters.
pub const MAX_WIDTH: usize = 100;
/// Spaces per indentation level.
const INDENT: usize = 4;

#[derive(Debug)]
pub enum FormatError {
    /// The source does not parse; the diagnostics are the parser's.
    Syntax(Vec<Diagnostic>),
    /// A formatter self-check failed. The input is left unchanged.
    Internal(String),
}

/// Format one source text. Returns the canonical text.
pub fn format_source(source: SourceId, text: &str) -> Result<String, FormatError> {
    let normalized = text.replace("\r\n", "\n");
    let parsed = parse(source, &normalized);
    if !parsed.diagnostics.is_empty() {
        return Err(FormatError::Syntax(parsed.diagnostics));
    }
    let output = Formatter::new(source, &normalized, &parsed.module).format();
    verify(source, &normalized, &parsed.module, &output)?;
    Ok(output)
}

fn verify(source: SourceId, input: &str, module: &Module, output: &str) -> Result<(), FormatError> {
    let again = parse(source, output);
    if !again.diagnostics.is_empty() {
        return Err(FormatError::Internal(format!(
            "formatted output does not parse: {}",
            again.diagnostics[0].message
        )));
    }
    if syntax_fingerprint(module) != syntax_fingerprint(&again.module) {
        return Err(FormatError::Internal(
            "formatting changed the syntax tree".into(),
        ));
    }
    if comment_texts(source, input) != comment_texts(source, output) {
        return Err(FormatError::Internal("formatting changed a comment".into()));
    }
    let second = Formatter::new(source, output, &again.module).format();
    if second != output {
        return Err(FormatError::Internal("formatting is not idempotent".into()));
    }
    Ok(())
}

/// The `Debug` rendering of a module with every span removed. Two modules with
/// equal fingerprints have the same syntax tree modulo positions.
pub fn syntax_fingerprint(module: &Module) -> String {
    strip_spans(&format!("{module:?}"))
}

/// Whether two modules have the same syntax tree, ignoring spans.
pub fn same_syntax(a: &Module, b: &Module) -> bool {
    syntax_fingerprint(a) == syntax_fingerprint(b)
}

fn strip_spans(debug: &str) -> String {
    let bytes = debug.as_bytes();
    let mut out = String::with_capacity(debug.len());
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if c == b'"' || c == b'\'' {
            // Copy a quoted string or character literal verbatim.
            let quote = c;
            let start = i;
            i += 1;
            while i < bytes.len() && bytes[i] != quote {
                if bytes[i] == b'\\' {
                    i += 1;
                }
                i += 1;
            }
            i = (i + 1).min(bytes.len());
            out.push_str(&debug[start..i]);
        } else if debug[i..].starts_with("Span { ") {
            match debug[i..].find(" }") {
                Some(end) => {
                    out.push_str("Span");
                    i += end + 2;
                }
                None => {
                    out.push_str(&debug[i..]);
                    break;
                }
            }
        } else {
            let ch = debug[i..].chars().next().unwrap();
            out.push(ch);
            i += ch.len_utf8();
        }
    }
    out
}

/// Every comment of `text` in order, with trailing blanks removed per line.
pub fn comment_texts(source: SourceId, text: &str) -> Vec<String> {
    let lexed = lex(source, text);
    let mut out = Vec::new();
    let mut previous_end = 0;
    for token in &lexed.tokens {
        let (comments, _) = scan_gap(&text[previous_end..token.span.start]);
        out.extend(comments.into_iter().map(|c| c.text));
        previous_end = token.span.end;
    }
    out
}

// ---------------------------------------------------------------------------
// Document model and printer (a Wadler/prettier style layout engine).
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum Doc {
    Nil,
    Text(String),
    Concat(Vec<Doc>),
    Indent(Box<Doc>),
    /// Indents only when the enclosing group is printed in break mode.
    IndentBreak(Box<Doc>),
    Group {
        doc: Box<Doc>,
        /// Always printed in break mode (does not force enclosing groups).
        expanded: bool,
        /// Printed in break mode: expanded, or contains a forced break.
        broken: bool,
        /// A forced break inside propagates to enclosing groups.
        up: bool,
        /// Decided on its own width even inside a flat parent, and allowed to
        /// "hug" the end of its line in the parent's width check.
        hug: bool,
    },
    Line,
    SoftLine,
    HardLine,
    IfBreak(Box<Doc>, Box<Doc>),
    LineSuffix(String),
    BreakParent,
}

/// The document without its forced breaks.
fn without_break_parent(doc: Doc) -> Doc {
    match doc {
        Doc::BreakParent => Doc::Nil,
        Doc::Concat(items) => Doc::Concat(items.into_iter().map(without_break_parent).collect()),
        other => other,
    }
}

fn text(s: impl Into<String>) -> Doc {
    Doc::Text(s.into())
}

fn indent(doc: Doc) -> Doc {
    Doc::Indent(Box::new(doc))
}

fn propagates(doc: &Doc) -> bool {
    match doc {
        Doc::BreakParent => true,
        Doc::Group { up, .. } => *up,
        Doc::Concat(items) => items.iter().any(propagates),
        Doc::Indent(inner) | Doc::IndentBreak(inner) => propagates(inner),
        Doc::IfBreak(a, b) => propagates(a) || propagates(b),
        _ => false,
    }
}

fn group(doc: Doc, expanded: bool) -> Doc {
    let inner = propagates(&doc);
    Doc::Group {
        doc: Box::new(doc),
        expanded,
        broken: expanded || inner,
        up: !expanded && inner,
        hug: false,
    }
}

/// A group whose layout may be chosen by the source (`expanded`) and that is
/// laid out independently of a flat parent.
fn hug_group(doc: Doc, expanded: bool) -> Doc {
    match group(doc, expanded) {
        Doc::Group {
            doc,
            expanded,
            broken,
            up,
            ..
        } => Doc::Group {
            doc,
            expanded,
            broken,
            up,
            hug: true,
        },
        other => other,
    }
}

fn width_of(s: &str) -> usize {
    s.chars().count()
}

/// Width of the document printed on a single line, or `None` when it cannot
/// be (hard line breaks or expanded groups).
fn flat_width(doc: &Doc) -> Option<usize> {
    match doc {
        Doc::Nil | Doc::SoftLine | Doc::BreakParent => Some(0),
        Doc::LineSuffix(s) => Some(if s.trim_start().starts_with("/*") && !s.contains('\n') {
            width_of(s)
        } else {
            0
        }),
        Doc::Text(s) => (!s.contains('\n')).then(|| width_of(s)),
        Doc::Concat(items) => items
            .iter()
            .try_fold(0, |sum, d| Some(sum + flat_width(d)?)),
        Doc::Indent(inner) | Doc::IndentBreak(inner) => flat_width(inner),
        Doc::Group { doc, broken, .. } => {
            if *broken {
                None
            } else {
                flat_width(doc)
            }
        }
        Doc::Line => Some(1),
        Doc::HardLine => None,
        Doc::IfBreak(_, flat) => flat_width(flat),
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Flat,
    Break,
}

#[derive(Clone, Copy)]
struct Cmd<'a> {
    indent: usize,
    mode: Mode,
    doc: &'a Doc,
    /// Inside the flat measurement of a group that lets a hug child break.
    hugok: bool,
}

fn fits(next: Cmd, rest: &[Cmd], mut remaining: isize) -> bool {
    let mut stack = vec![next];
    let mut rest_index = rest.len();
    loop {
        if remaining < 0 {
            return false;
        }
        let cmd = match stack.pop() {
            Some(cmd) => cmd,
            None => {
                if rest_index == 0 {
                    return true;
                }
                rest_index -= 1;
                rest[rest_index]
            }
        };
        match cmd.doc {
            Doc::Nil | Doc::BreakParent => {}
            // A trailing block comment still occupies the line.
            Doc::LineSuffix(s) => {
                if s.trim_start().starts_with("/*") && !s.contains('\n') {
                    remaining -= width_of(s) as isize;
                }
            }
            Doc::Text(s) => match s.find('\n') {
                Some(at) => return remaining >= width_of(&s[..at]) as isize,
                None => remaining -= width_of(s) as isize,
            },
            Doc::Concat(items) => {
                for item in items.iter().rev() {
                    stack.push(Cmd { doc: item, ..cmd });
                }
            }
            Doc::Indent(inner) | Doc::IndentBreak(inner) => stack.push(Cmd { doc: inner, ..cmd }),
            Doc::Group {
                doc, broken, hug, ..
            } => {
                let mut mode = if *broken { Mode::Break } else { cmd.mode };
                // Outside a container body, a source-inline container that
                // cannot fit flat will break: the line ends at its first line.
                let mut hugok = cmd.hugok;
                if *hug && mode == Mode::Flat && hugok {
                    // A source-inline group that cannot fit flat will break.
                    if !flat_width(doc).is_some_and(|w| w as isize <= remaining) {
                        mode = Mode::Break;
                    }
                }
                if *hug {
                    hugok = false;
                }
                stack.push(Cmd {
                    doc,
                    mode,
                    hugok,
                    ..cmd
                });
            }
            Doc::IfBreak(broken, flat) => {
                let chosen = if cmd.mode == Mode::Break {
                    broken
                } else {
                    flat
                };
                stack.push(Cmd { doc: chosen, ..cmd });
            }
            Doc::Line => {
                if cmd.mode == Mode::Break {
                    return true;
                }
                remaining -= 1;
            }
            Doc::SoftLine => {
                if cmd.mode == Mode::Break {
                    return true;
                }
            }
            Doc::HardLine => return true,
        }
    }
}

fn print(doc: &Doc) -> String {
    let mut out = String::new();
    let mut position = 0usize;
    let mut suffixes: Vec<&str> = Vec::new();
    let mut remeasure = false;
    let mut stack = vec![Cmd {
        indent: 0,
        mode: Mode::Break,
        doc,
        hugok: false,
    }];
    let mut line_indent = 0usize;
    // Comments that followed a line comment on the same output line. They are
    // written as own-line comments in front of the next text, which is where a
    // second formatting pass would find them.
    let mut pending: Vec<String> = Vec::new();
    let flush = |out: &mut String, suffixes: &mut Vec<&str>, pending: &mut Vec<String>| {
        let mut ended = false;
        for suffix in suffixes.drain(..) {
            if ended {
                pending.push(suffix.trim_start().to_string());
            } else {
                out.push_str(suffix);
            }
            ended = ended || suffix.trim_start().starts_with("//");
        }
    };
    let newline = |out: &mut String,
                   position: &mut usize,
                   suffixes: &mut Vec<&str>,
                   pending: &mut Vec<String>,
                   line_indent: &mut usize,
                   indent: usize| {
        flush(out, suffixes, pending);
        while out.ends_with(' ') {
            out.pop();
        }
        out.push('\n');
        for _ in 0..indent {
            out.push(' ');
        }
        *position = indent;
        *line_indent = indent;
    };
    let write_pending =
        |out: &mut String, pending: &mut Vec<String>, first: char, indent: usize| {
            if pending.is_empty() {
                return;
            }
            // A closing bracket's comments belong inside the bracket.
            let pending_indent = if matches!(first, ')' | ']' | '}') {
                indent + INDENT
            } else {
                indent
            };
            while out.ends_with(' ') {
                out.pop();
            }
            for comment in pending.drain(..) {
                out.push_str(&" ".repeat(pending_indent));
                out.push_str(&comment);
                out.push('\n');
            }
            out.push_str(&" ".repeat(indent));
        };
    while let Some(cmd) = stack.pop() {
        match cmd.doc {
            Doc::Nil | Doc::BreakParent => {}
            Doc::Text(s) => {
                if !s.is_empty() {
                    write_pending(
                        &mut out,
                        &mut pending,
                        s.chars().next().unwrap(),
                        line_indent,
                    );
                }
                out.push_str(s);
                position = match s.rfind('\n') {
                    Some(at) => width_of(&s[at + 1..]),
                    None => position + width_of(s),
                };
            }
            Doc::Concat(items) => {
                for item in items.iter().rev() {
                    stack.push(Cmd { doc: item, ..cmd });
                }
            }
            Doc::Indent(inner) => stack.push(Cmd {
                indent: cmd.indent + INDENT,
                doc: inner,
                ..cmd
            }),
            Doc::IndentBreak(inner) => stack.push(Cmd {
                indent: if cmd.mode == Mode::Break {
                    cmd.indent + INDENT
                } else {
                    cmd.indent
                },
                doc: inner,
                ..cmd
            }),
            Doc::Group {
                doc, broken, hug, ..
            } => {
                if cmd.mode == Mode::Flat && !remeasure && !*hug {
                    stack.push(Cmd {
                        doc,
                        mode: if *broken { Mode::Break } else { Mode::Flat },
                        ..cmd
                    });
                } else {
                    remeasure = false;
                    let flat = Cmd {
                        doc,
                        mode: Mode::Flat,
                        hugok: !*hug,
                        ..cmd
                    };
                    let remaining = MAX_WIDTH as isize - position as isize;
                    if !*broken && fits(flat, &stack, remaining) {
                        stack.push(flat);
                    } else {
                        stack.push(Cmd {
                            doc,
                            mode: Mode::Break,
                            ..cmd
                        });
                    }
                }
            }
            Doc::IfBreak(broken, flat) => {
                let chosen = if cmd.mode == Mode::Break {
                    broken
                } else {
                    flat
                };
                stack.push(Cmd { doc: chosen, ..cmd });
            }
            Doc::Line => {
                if cmd.mode == Mode::Break {
                    newline(
                        &mut out,
                        &mut position,
                        &mut suffixes,
                        &mut pending,
                        &mut line_indent,
                        cmd.indent,
                    );
                } else {
                    out.push(' ');
                    position += 1;
                }
            }
            Doc::SoftLine => {
                if cmd.mode == Mode::Break {
                    newline(
                        &mut out,
                        &mut position,
                        &mut suffixes,
                        &mut pending,
                        &mut line_indent,
                        cmd.indent,
                    );
                }
            }
            Doc::HardLine => {
                if cmd.mode == Mode::Flat {
                    remeasure = true;
                }
                newline(
                    &mut out,
                    &mut position,
                    &mut suffixes,
                    &mut pending,
                    &mut line_indent,
                    cmd.indent,
                );
            }
            Doc::LineSuffix(s) => suffixes.push(s),
        }
    }
    flush(&mut out, &mut suffixes, &mut pending);
    for comment in pending.drain(..) {
        while out.ends_with(' ') {
            out.pop();
        }
        out.push('\n');
        out.push_str(&comment);
    }
    while out.ends_with([' ', '\n']) {
        out.pop();
    }
    out
}

// ---------------------------------------------------------------------------
// Comments and tokens.
// ---------------------------------------------------------------------------

struct RawComment {
    text: String,
    line: bool,
    /// Newlines in the white space before the comment (since the previous
    /// token or comment).
    newlines_before: usize,
}

fn trim_lines(comment: &str) -> String {
    comment
        .split('\n')
        .map(str::trim_end)
        .collect::<Vec<_>>()
        .join("\n")
}

/// Split the text between two tokens into comments and the newline count
/// that follows the last of them.
fn scan_gap(gap: &str) -> (Vec<RawComment>, usize) {
    let mut comments = Vec::new();
    let mut newlines = 0;
    let mut i = 0;
    while i < gap.len() {
        let c = gap[i..].chars().next().unwrap();
        if c == '\n' {
            newlines += 1;
            i += 1;
        } else if c.is_whitespace() {
            i += c.len_utf8();
        } else if gap[i..].starts_with("//") {
            let end = gap[i..].find('\n').map_or(gap.len(), |n| i + n);
            comments.push(RawComment {
                text: trim_lines(&gap[i..end]),
                line: true,
                newlines_before: newlines,
            });
            newlines = 0;
            i = end;
        } else if gap[i..].starts_with("/*") {
            let start = i;
            i += 2;
            let mut depth = 1;
            while i < gap.len() && depth > 0 {
                if gap[i..].starts_with("/*") {
                    depth += 1;
                    i += 2;
                } else if gap[i..].starts_with("*/") {
                    depth -= 1;
                    i += 2;
                } else {
                    i += gap[i..].chars().next().unwrap().len_utf8();
                }
            }
            comments.push(RawComment {
                text: trim_lines(&gap[start..i]),
                line: false,
                newlines_before: newlines,
            });
            newlines = 0;
        } else {
            i += c.len_utf8();
        }
    }
    (comments, newlines)
}

struct LeadingComment {
    text: String,
    line: bool,
    newlines_before: usize,
    /// Newlines between this comment and whatever follows it.
    newlines_after: usize,
}

#[derive(Default)]
struct Info {
    leading: Vec<LeadingComment>,
    /// Comments on the same line after the previous token: (text, is_line).
    trailing: Vec<(String, bool)>,
    /// Newlines between the last comment (or previous token) and this token.
    newlines_before: usize,
    /// Any white space or comment between the previous token and this one.
    gap_whitespace: bool,
}

fn build_info(text: &str, tokens: &[Token]) -> Vec<Info> {
    let mut infos: Vec<Info> = Vec::new();
    let mut previous_end = 0;
    for (i, token) in tokens.iter().enumerate() {
        let gap = &text[previous_end..token.span.start];
        let (comments, final_newlines) = scan_gap(gap);
        let mut info = Info {
            newlines_before: final_newlines,
            gap_whitespace: !gap.is_empty(),
            ..Info::default()
        };
        let mut in_trailing = i > 0;
        for (k, comment) in comments.iter().enumerate() {
            let newlines_after = comments
                .get(k + 1)
                .map_or(final_newlines, |next| next.newlines_before);
            let same_line = comment.newlines_before == 0 && (i > 0 || k > 0);
            // The whole run of comments sharing this line is trailing when the
            // line ends after it, and leading (inline) when code follows.
            let mut end = k;
            while end + 1 < comments.len() && comments[end + 1].newlines_before == 0 {
                end += 1;
            }
            let run_ends_line = comments[end].line
                || comments
                    .get(end + 1)
                    .map_or(final_newlines, |next| next.newlines_before)
                    > 0;
            let trailing = in_trailing && same_line && run_ends_line;
            if trailing {
                infos[i - 1]
                    .trailing
                    .push((comment.text.clone(), comment.line));
            } else {
                in_trailing = false;
                info.leading.push(LeadingComment {
                    text: comment.text.clone(),
                    line: comment.line,
                    newlines_before: comment.newlines_before,
                    newlines_after,
                });
            }
        }
        infos.push(info);
        previous_end = token.span.end;
    }
    infos
}

// ---------------------------------------------------------------------------
// The formatter proper.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum Head {
    None,
    Type,
    Interface,
    Extend,
}

#[derive(Clone, Copy)]
enum Prev {
    Start,
    Tok(usize),
    /// A bracket group; the index is its closing token.
    Group(usize),
}

struct RunState {
    head: Head,
    body_seen: bool,
    match_pending: u32,
    prev: Prev,
    unary_prev: bool,
}

impl RunState {
    fn new(head: Head) -> Self {
        RunState {
            head,
            body_seen: false,
            match_pending: 0,
            prev: Prev::Start,
            unary_prev: false,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Brace {
    Block,
    Match,
    Fields,
    Use,
    ItemBody,
}

struct Chunk {
    doc: Doc,
    blank_before: bool,
}

struct Formatter<'a> {
    text: &'a str,
    tokens: Vec<Token>,
    info: Vec<Info>,
    generic: Vec<bool>,
    in_type: Vec<bool>,
    close: Vec<usize>,
    item_starts: Vec<usize>,
    /// Token whose leading comments are ignored (item width measurement).
    ignore_leading: std::cell::Cell<usize>,
    /// Block nesting depth while documents are built (width estimates).
    depth: std::cell::Cell<usize>,
    /// Printing the comments of a dropped token: no newline after the last.
    dangle: std::cell::Cell<bool>,
    /// The blocks of the `if` chain being built are all printed expanded.
    force_expand: std::cell::Cell<bool>,
}

const NO_CLOSE: usize = usize::MAX;

fn collect_spans(debug: &str, marker: &str) -> Vec<(usize, usize)> {
    let mut spans = Vec::new();
    let mut from = 0;
    while let Some(found) = debug[from..].find(marker) {
        let at = from + found + marker.len();
        from = at;
        let rest = &debug[at..];
        let Some((_, rest)) = rest.split_once("), start: ") else {
            continue;
        };
        let Some((start, rest)) = rest.split_once(", end: ") else {
            continue;
        };
        let end: String = rest.chars().take_while(char::is_ascii_digit).collect();
        if let (Ok(start), Ok(end)) = (start.parse(), end.parse()) {
            spans.push((start, end));
        }
    }
    spans
}

fn is_keyword(word: &str) -> bool {
    matches!(
        word,
        "if" | "else"
            | "match"
            | "return"
            | "in"
            | "as"
            | "of"
            | "let"
            | "var"
            | "loop"
            | "try"
            | "const"
            | "use"
            | "type"
            | "pub"
            | "borrow"
            | "share"
            | "enum"
            | "break"
            | "continue"
            | "while"
            | "struct"
            | "import"
            | "export"
            | "fn"
    )
}

impl<'a> Formatter<'a> {
    fn new(source: SourceId, text: &'a str, module: &Module) -> Self {
        let tokens = lex(source, text).tokens;
        let info = build_info(text, &tokens);
        let count = tokens.len();
        let mut close = vec![NO_CLOSE; count];
        let mut stack: Vec<usize> = Vec::new();
        for (i, token) in tokens.iter().enumerate() {
            if let TokenKind::Symbol(s) = &token.kind {
                match s.as_str() {
                    "(" | "[" | "{" => stack.push(i),
                    ")" | "]" | "}" => {
                        if let Some(open) = stack.pop() {
                            close[open] = i;
                        }
                    }
                    _ => {}
                }
            }
        }
        let mut formatter = Formatter {
            text,
            tokens,
            info,
            generic: vec![false; count],
            in_type: vec![false; count],
            close,
            item_starts: Vec::new(),
            ignore_leading: std::cell::Cell::new(NO_CLOSE),
            depth: std::cell::Cell::new(0),
            dangle: std::cell::Cell::new(false),
            force_expand: std::cell::Cell::new(false),
        };
        formatter.mark_regions(module);
        formatter
    }

    fn token_at(&self, offset: usize) -> Option<usize> {
        self.tokens
            .binary_search_by(|token| token.span.start.cmp(&offset))
            .ok()
    }

    fn mark_regions(&mut self, module: &Module) {
        let debug = format!("{module:?}");
        let count = self.tokens.len();
        for (start, end) in collect_spans(&debug, "Type { span: Span { source: SourceId(") {
            if end <= start {
                continue;
            }
            let Some(first) = self.token_at(start) else {
                continue;
            };
            if self
                .word(first)
                .is_some_and(|w| matches!(w, "pub" | "type" | "extend"))
            {
                continue;
            }
            let mut i = first;
            while i < count && self.tokens[i].span.end <= end {
                self.in_type[i] = true;
                i += 1;
            }
        }
        let mut opens = vec![false; count];
        for (start, _) in collect_spans(&debug, "GenericParameter { span: Span { source: SourceId(")
        {
            if let Some(first) = self.token_at(start) {
                if first > 0 && self.sym(first - 1) == "<" {
                    opens[first - 1] = true;
                }
            }
        }
        // `Name<T> {` in expression position: a generic struct literal.
        for i in 1..count {
            if self.sym(i) == "<"
                && self
                    .word(i - 1)
                    .is_some_and(|w| w.starts_with(|c: char| c.is_ascii_uppercase()))
                && self.generic_literal_ahead(i)
            {
                opens[i] = true;
            }
        }
        let mut depth = 0usize;
        for i in 0..count {
            match self.sym(i) {
                "<" if self.in_type[i] || opens[i] || (depth > 0 && self.word(i - 1).is_some()) => {
                    self.generic[i] = true;
                    depth += 1;
                }
                ">" if depth > 0 => {
                    self.generic[i] = true;
                    depth -= 1;
                }
                _ => {}
            }
        }
        // Top-level item starts.
        let mut starts = Vec::new();
        for item in &module.items {
            if let Some(first) = self.token_at(item.span.start) {
                let trailing_extension = self.word(first) == Some("extend")
                    && self.sym(first + 1) == "{"
                    && !starts.is_empty();
                if !trailing_extension {
                    starts.push(first);
                }
            }
        }
        starts.sort_unstable();
        starts.dedup();
        self.item_starts = starts;
    }

    /// Mirrors the parser's check for `Name<...> {` struct literals.
    fn generic_literal_ahead(&self, open: usize) -> bool {
        let mut depth = 0usize;
        for i in open..self.tokens.len() {
            match self.sym(i) {
                ";" => return false,
                "<" => depth += 1,
                ">" => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        return self.sym(i + 1) == "{";
                    }
                }
                _ => {}
            }
            if matches!(self.tokens[i].kind, TokenKind::Eof) {
                return false;
            }
        }
        false
    }

    // -- token helpers ------------------------------------------------------

    fn raw(&self, i: usize) -> &'a str {
        let span = self.tokens[i].span;
        &self.text[span.start..span.end]
    }

    fn sym(&self, i: usize) -> &str {
        match self.tokens.get(i).map(|t| &t.kind) {
            Some(TokenKind::Symbol(s)) => s,
            _ => "",
        }
    }

    fn word(&self, i: usize) -> Option<&str> {
        match self.tokens.get(i).map(|t| &t.kind) {
            Some(TokenKind::Word(s)) => Some(s),
            _ => None,
        }
    }

    fn is_open(&self, i: usize) -> bool {
        matches!(self.sym(i), "(" | "[" | "{") && self.close[i] != NO_CLOSE
    }

    fn skip(&self, i: usize) -> usize {
        if self.is_open(i) {
            self.close[i] + 1
        } else {
            i + 1
        }
    }

    fn newline_between(&self, from: usize, to: usize) -> bool {
        self.text[self.tokens[from].span.start..self.tokens[to].span.start].contains('\n')
    }

    fn first_atom_blank(&self, i: usize) -> bool {
        if i == 0 {
            return false;
        }
        match self.info[i].leading.first() {
            Some(comment) => comment.newlines_before >= 2,
            None => self.info[i].newlines_before >= 2,
        }
    }

    // -- comments -----------------------------------------------------------

    /// The document for token `i`: leading comments, the token text (or
    /// `replacement`) and trailing comments.
    fn tok(&self, i: usize, chunk_start: bool, spaced: bool) -> Doc {
        self.tok_text(i, chunk_start, spaced, None, true)
    }

    fn tok_text(
        &self,
        i: usize,
        chunk_start: bool,
        spaced: bool,
        replacement: Option<&str>,
        leading: bool,
    ) -> Doc {
        let (mut lead, tail) = self.tok_split(i, chunk_start, spaced, replacement, leading);
        lead.push(tail);
        Doc::Concat(lead)
    }

    /// Like `tok_text`, split into the leading comments and the token itself
    /// (with its trailing comments), so a group can keep the former outside.
    fn tok_split(
        &self,
        i: usize,
        chunk_start: bool,
        spaced: bool,
        replacement: Option<&str>,
        leading: bool,
    ) -> (Vec<Doc>, Doc) {
        let (lead, mut tail, trailing) =
            self.tok_split_raw(i, chunk_start, spaced, replacement, leading);
        tail.push(trailing);
        (lead, Doc::Concat(tail))
    }

    /// Leading comments, the token text, and the trailing comments apart.
    fn tok_split_raw(
        &self,
        i: usize,
        chunk_start: bool,
        spaced: bool,
        replacement: Option<&str>,
        leading: bool,
    ) -> (Vec<Doc>, Vec<Doc>, Doc) {
        let info = &self.info[i];
        let mut parts: Vec<Doc> = Vec::new();
        let mut at_line_start = chunk_start;
        // Width measurement ignores own-line comments (they never share the
        // item's line) but not inline ones.
        let measuring = self.ignore_leading.get() == i;
        let comments: Vec<&LeadingComment> = if leading {
            info.leading
                .iter()
                .filter(|c| !measuring || (!c.line && c.newlines_after == 0))
                .collect()
        } else {
            Vec::new()
        };
        let dangle = self.dangle.get();
        for (k, comment) in comments.iter().enumerate() {
            let inline = !comment.line && comment.newlines_after == 0;
            if inline {
                if !at_line_start && !spaced && k == 0 {
                    parts.push(text(" "));
                }
                parts.push(text(comment.text.clone()));
                if k + 1 < comments.len() || spaced || at_line_start {
                    parts.push(text(" "));
                }
                continue;
            }
            if !at_line_start {
                if comment.newlines_before == 0 {
                    parts.push(text(" "));
                } else {
                    parts.push(Doc::HardLine);
                }
            }
            if k > 0 && comment.newlines_before >= 2 {
                parts.push(Doc::HardLine);
            }
            parts.push(text(comment.text.clone()));
            if !(dangle && k + 1 == comments.len()) {
                parts.push(Doc::HardLine);
            }
            parts.push(Doc::BreakParent);
            at_line_start = true;
        }
        if leading && !dangle {
            if let Some(last) = comments.last() {
                let own = last.line || last.newlines_after > 0;
                if own && info.newlines_before >= 2 {
                    parts.push(Doc::HardLine);
                }
            }
        }
        let tail = vec![text(replacement.unwrap_or_else(|| self.raw(i)))];
        let mut trailing = Vec::new();
        for (comment, line) in &info.trailing {
            trailing.push(Doc::LineSuffix(format!(" {comment}")));
            // After a separator or opener the comment annotates the line it
            // ends, so the enclosing list must keep that line break.
            if *line && matches!(self.sym(i), "," | "(" | "[" | "{") {
                trailing.push(Doc::BreakParent);
            }
        }
        (parts, tail, Doc::Concat(trailing))
    }

    /// A closing bracket: its text (with any leading comments) for use inside
    /// the group, and its trailing comments for use after the group.
    fn close_tok(&self, close: usize, leading: bool) -> (Doc, Doc) {
        let (mut lead, tail, trailing) = self.tok_split_raw(close, false, false, None, leading);
        lead.extend(tail);
        (Doc::Concat(lead), trailing)
    }

    /// Only the comments of token `i`, for a token that is not printed.
    fn comments_only(&self, i: usize, chunk_start: bool) -> Doc {
        // The caller's next separator ends the last comment's line.
        self.dangle.set(true);
        let doc = self.tok_text(i, chunk_start, false, Some(""), true);
        self.dangle.set(false);
        doc
    }

    /// Comments before a closing bracket, printed on their own lines.
    fn dangling(&self, close: usize) -> Option<Doc> {
        let comments = &self.info[close].leading;
        if comments.is_empty() {
            return None;
        }
        let mut parts = Vec::new();
        for (k, comment) in comments.iter().enumerate() {
            parts.push(Doc::Line);
            if k > 0 && comment.newlines_before >= 2 {
                parts.push(Doc::Line);
            }
            parts.push(text(comment.text.clone()));
            if comment.line {
                parts.push(Doc::BreakParent);
            }
        }
        Some(Doc::Concat(parts))
    }

    // -- spacing ------------------------------------------------------------

    fn operand_end(&self, prev: Prev) -> bool {
        match prev {
            Prev::Start => false,
            Prev::Group(_) => true,
            Prev::Tok(i) => match &self.tokens[i].kind {
                TokenKind::Word(w) => !is_keyword(w) || (i > 0 && self.sym(i - 1) == "."),
                TokenKind::Number(_) | TokenKind::StringLiteral(_) | TokenKind::CharLiteral(_) => {
                    true
                }
                TokenKind::Symbol(s) => s == "?" || (s == ">" && self.generic[i]),
                TokenKind::Eof => false,
            },
        }
    }

    fn prev_text(&self, prev: Prev) -> &str {
        match prev {
            Prev::Start => "",
            Prev::Tok(i) => match &self.tokens[i].kind {
                TokenKind::Symbol(s) => s,
                _ => "",
            },
            Prev::Group(close) => self.sym(close),
        }
    }

    fn prev_word(&self, prev: Prev) -> Option<&str> {
        match prev {
            Prev::Tok(i) => self.word(i),
            _ => None,
        }
    }

    fn is_unary_at(&self, i: usize, st: &RunState) -> bool {
        match self.sym(i) {
            "-" | "+" | "~" => !self.operand_end(st.prev),
            "!" => !self.in_type[i] && !self.operand_end(st.prev),
            _ => false,
        }
    }

    /// Whether a space separates `st.prev` from the token or group at `cur`.
    fn space_before(&self, cur: usize, is_group: bool, st: &RunState) -> bool {
        if matches!(st.prev, Prev::Start) || st.unary_prev {
            return false;
        }
        let c = self.sym(cur);
        let p = self.prev_text(st.prev);
        let prev_generic_close =
            matches!(st.prev, Prev::Tok(i) if self.generic[i] && self.sym(i) == ">");
        if !is_group && matches!(c, "," | ";") {
            return false;
        }
        if matches!(c, "." | "::" | ".." | "..=") && !is_group {
            return false;
        }
        if matches!(p, "." | "::" | ".." | "..=") && matches!(st.prev, Prev::Tok(_)) {
            return false;
        }
        if !is_group && c == "?" {
            return self.sym(cur + 1) == "!"
                && !self.info[cur + 1].gap_whitespace
                && self.info[cur].gap_whitespace;
        }
        if !is_group && c == "!" && self.in_type[cur] {
            return !(p == "?"
                && matches!(st.prev, Prev::Tok(_))
                && !self.info[cur].gap_whitespace);
        }
        if !is_group && self.generic[cur] && matches!(c, "<" | ">") {
            return false;
        }
        if let Prev::Tok(i) = st.prev {
            if self.generic[i] && self.sym(i) == "<" {
                return false;
            }
        }
        if prev_generic_close {
            if is_group && c == "[" {
                return st.head == Head::Type;
            }
            return !matches!(c, "(" | "[" | "::" | "," | ";" | ")" | "?" | ">" | ".");
        }
        if !is_group && c == ":" {
            return false;
        }
        if is_group && c == "(" {
            if self.prev_word(st.prev) == Some("fn") {
                return false;
            }
            return !self.operand_end(st.prev);
        }
        if is_group && c == "[" {
            if st.head == Head::Type && self.operand_end(st.prev) {
                return true;
            }
            return !self.operand_end(st.prev);
        }
        true
    }

    // -- runs ---------------------------------------------------------------

    fn brace_kind(&self, open: usize, st: &mut RunState) -> Brace {
        let prev_word = if open > 0 { self.word(open - 1) } else { None };
        if prev_word == Some("extend") {
            st.body_seen = true;
            return Brace::ItemBody;
        }
        if matches!(st.head, Head::Interface | Head::Extend) && !st.body_seen {
            st.body_seen = true;
            return Brace::ItemBody;
        }
        if st.match_pending > 0 {
            st.match_pending -= 1;
            return Brace::Match;
        }
        if open > 0 && self.sym(open - 1) == "::" {
            return Brace::Use;
        }
        if self.looks_like_fields(open) {
            return Brace::Fields;
        }
        let close = self.close[open];
        if self.sym(close + 1) == ":=" {
            return Brace::Fields;
        }
        Brace::Block
    }

    fn looks_like_fields(&self, open: usize) -> bool {
        let first = open + 1;
        if self.word(first) == Some("pub") && self.word(first + 1).is_some() {
            return self.sym(first + 2) == ":";
        }
        self.word(first).is_some() && self.sym(first + 1) == ":"
    }

    /// Lowest-precedence breakable operator class present at the top level.
    fn operator_tier(&self, lo: usize, hi: usize) -> u8 {
        let mut st = RunState::new(Head::None);
        let mut tier = 0u8;
        let mut i = lo;
        while i < hi {
            if self.is_open(i) {
                st.prev = Prev::Group(self.close[i]);
                i = self.close[i] + 1;
                continue;
            }
            let binary = !self.is_unary_at(i, &st);
            if self.word(i) == Some("where") {
                return if tier == 1 { 1 } else { 0 };
            }
            match self.sym(i) {
                "&&" | "||" => tier = 1,
                "+" | "-" if binary && tier == 0 => tier = 2,
                _ => {}
            }
            st.prev = Prev::Tok(i);
            i += 1;
        }
        tier
    }

    fn run(&self, lo: usize, hi: usize, head: Head) -> Doc {
        let mut st = RunState::new(head);
        let doc = self.run_with(lo, hi, &mut st);
        if head != Head::None || self.word(lo) != Some("if") || self.force_expand.get() {
            return doc;
        }
        // An `if` chain whose blocks are all written inline stays inline only
        // when the whole chain fits; otherwise every block is expanded.
        let mut i = lo;
        while i < hi {
            if self.sym(i) == "{" && self.is_open(i) && self.newline_between(i, self.close[i]) {
                return doc;
            }
            i = self.skip(i);
        }
        let too_wide =
            flat_width(&doc).is_some_and(|width| width + self.depth.get() * INDENT > MAX_WIDTH);
        if !too_wide {
            return doc;
        }
        self.force_expand.set(true);
        let mut st = RunState::new(head);
        let expanded = self.run_with(lo, hi, &mut st);
        self.force_expand.set(false);
        expanded
    }

    fn run_with(&self, lo: usize, hi: usize, st: &mut RunState) -> Doc {
        let tier = self.operator_tier(lo, hi);
        let mut lead_parts: Vec<Doc> = Vec::new();
        let mut parts: Vec<Doc> = Vec::new();
        let mut i = lo;
        while i < hi {
            let first = matches!(st.prev, Prev::Start);
            if self.is_open(i) {
                let close = self.close[i];
                let spaced = self.space_before(i, true, st);
                if spaced && !self.starts_own_line(i) {
                    parts.push(text(" "));
                }
                let (lead, doc) = self.group_doc(i, close, st, spaced, first);
                if first {
                    lead_parts.extend(lead);
                } else {
                    parts.extend(lead);
                }
                parts.push(doc);
                st.prev = Prev::Group(close);
                st.unary_prev = false;
                i = close + 1;
                continue;
            }
            let sym = self.sym(i);
            let unary = self.is_unary_at(i, st);
            let spaced = self.space_before(i, false, st);
            let breakable = !unary
                && ((tier == 1 && matches!(sym, "&&" | "||"))
                    || (tier == 2 && matches!(sym, "+" | "-")));
            let is_where = self.word(i) == Some("where");
            if (breakable || is_where) && !first {
                // The break, any comments and the token share one indent
                // level, so continuation lines stay aligned.
                let own_line = self.starts_own_line(i);
                let mut inner = Vec::new();
                if spaced && !own_line {
                    inner.push(Doc::Line);
                    if is_where
                        && (self.info[i].newlines_before > 0
                            || self.info[i].leading.iter().any(|c| c.newlines_after > 0))
                    {
                        inner.push(Doc::BreakParent);
                    }
                }
                let (lead, tail) = self.tok_split(i, false, spaced, None, true);
                inner.extend(lead);
                inner.push(tail);
                parts.push(indent(Doc::Concat(inner)));
                st.unary_prev = unary;
                st.prev = Prev::Tok(i);
                i += 1;
                continue;
            }
            if spaced && !self.starts_own_line(i) {
                parts.push(text(" "));
            }
            if self.word(i) == Some("match") && !(i > lo && self.sym(i - 1) == ".") {
                st.match_pending += 1;
            }
            // `<<` and `>>` are two adjacent single-character tokens.
            let shift = !self.generic[i]
                && i + 1 < hi
                && matches!(sym, "<" | ">")
                && self.sym(i + 1) == sym
                && !self.generic[i + 1];
            if shift {
                parts.push(self.tok_text(i, first, spaced, Some(sym), true));
                parts.push(self.tok_text(i + 1, false, false, Some(sym), true));
                st.prev = Prev::Tok(i + 1);
                st.unary_prev = false;
                i += 2;
                continue;
            }
            let (lead, tail) = self.tok_split(i, first, spaced, None, true);
            if first {
                lead_parts.extend(lead);
            } else {
                parts.extend(lead);
            }
            parts.push(tail);
            st.unary_prev = unary;
            st.prev = Prev::Tok(i);
            i += 1;
        }
        lead_parts.push(group(Doc::Concat(parts), false));
        Doc::Concat(lead_parts)
    }

    fn starts_own_line(&self, i: usize) -> bool {
        self.info[i]
            .leading
            .first()
            .is_some_and(|c| c.line || c.newlines_after > 0)
    }

    // -- groups -------------------------------------------------------------

    fn group_doc(
        &self,
        open: usize,
        close: usize,
        st: &mut RunState,
        spaced: bool,
        first: bool,
    ) -> (Vec<Doc>, Doc) {
        match self.sym(open) {
            "(" => {
                let tuple_like = self.is_tuple_like(open);
                self.list_doc(open, close, false, false, tuple_like, spaced, first)
            }
            "[" => {
                let index = self.operand_end(st.prev) && st.head != Head::Type;
                // An index holds exactly one expression: never a list.
                self.list_doc(open, close, false, !index, index, spaced, first)
            }
            _ => match self.brace_kind(open, st) {
                Brace::Fields => self.list_doc(open, close, true, true, false, spaced, first),
                Brace::Use => self.list_doc(open, close, false, true, false, spaced, first),
                Brace::Block => self.block_doc(open, close, spaced, first),
                Brace::Match => self.match_doc(open, close, spaced, first),
                Brace::ItemBody => self.item_body_doc(open, close, spaced, first),
            },
        }
    }

    fn is_tuple_like(&self, open: usize) -> bool {
        if open == 0 {
            return true;
        }
        let prev = open - 1;
        match &self.tokens[prev].kind {
            TokenKind::Word(w) => is_keyword(w) && w != "fn",
            TokenKind::Symbol(s) => {
                !(matches!(s.as_str(), ")" | "]" | "?") || (s == ">" && self.generic[prev]))
            }
            _ => false,
        }
    }

    /// Split `(lo, hi)` at top-level commas: item ranges, comma token indices
    /// and the trailing comma, if any.
    fn split_commas(
        &self,
        lo: usize,
        hi: usize,
    ) -> (Vec<(usize, usize)>, Vec<usize>, Option<usize>) {
        let mut items = Vec::new();
        let mut commas = Vec::new();
        let mut start = lo;
        let mut i = lo;
        let mut generic_depth = 0usize;
        while i < hi {
            if self.is_open(i) {
                i = self.close[i] + 1;
                continue;
            }
            if self.generic[i] {
                match self.sym(i) {
                    "<" => generic_depth += 1,
                    ">" => generic_depth = generic_depth.saturating_sub(1),
                    _ => {}
                }
            }
            if self.sym(i) == "," && generic_depth == 0 {
                items.push((start, i));
                commas.push(i);
                start = i + 1;
            }
            i += 1;
        }
        let mut trailing = None;
        if start < hi {
            items.push((start, hi));
        } else if let Some(last) = commas.pop() {
            trailing = Some(last);
        }
        (items, commas, trailing)
    }

    #[allow(clippy::too_many_arguments)]
    fn list_doc(
        &self,
        open: usize,
        close: usize,
        padded: bool,
        preserve: bool,
        tuple_like: bool,
        spaced: bool,
        first: bool,
    ) -> (Vec<Doc>, Doc) {
        let (lead, open_doc) = self.tok_split(open, first, spaced, None, true);
        let (items, commas, trailing) = self.split_commas(open + 1, close);
        let dangling = self.dangling(close);
        if items.is_empty() {
            let (close_doc, after) = self.close_tok(close, dangling.is_none());
            let body = match dangling {
                None => Doc::Concat(vec![without_break_parent(open_doc), close_doc]),
                Some(comments) => group(
                    Doc::Concat(vec![open_doc, indent(comments), Doc::Line, close_doc]),
                    true,
                ),
            };
            return (lead, Doc::Concat(vec![body, after]));
        }
        let expanded = preserve && self.newline_between(open, open + 1);
        let sep = if padded { Doc::Line } else { Doc::SoftLine };
        let single = items.len() == 1;
        let force_comma = single && tuple_like && trailing.is_some();
        // A parenthesized single item is a grouping, not a tuple: no comma.
        let repeat =
            (open + 1..close).any(|i| self.sym(i) == ";" && self.depth_is_top(open + 1, i));
        let never_comma = (single && tuple_like && trailing.is_none()) || repeat;
        let mut inner = vec![sep.clone()];
        for (k, &(lo, hi)) in items.iter().enumerate() {
            if k > 0 {
                inner.push(Doc::Line);
                if expanded && self.first_atom_blank(lo) {
                    inner.push(Doc::Line);
                }
            }
            inner.push(self.run(lo, hi, Head::None));
            if k + 1 < items.len() {
                inner.push(self.tok(commas[k], false, false));
            }
        }
        match trailing {
            Some(comma) if force_comma => inner.push(self.tok(comma, false, false)),
            Some(comma) => {
                inner.push(Doc::IfBreak(Box::new(text(",")), Box::new(Doc::Nil)));
                inner.push(self.comments_only(comma, false));
            }
            None if never_comma => {}
            None => inner.push(Doc::IfBreak(Box::new(text(",")), Box::new(Doc::Nil))),
        }
        if let Some(comments) = &dangling {
            inner.push(comments.clone());
        }
        let (close_doc, after) = self.close_tok(close, dangling.is_none());
        let body = Doc::Concat(vec![
            open_doc,
            Doc::IndentBreak(Box::new(Doc::Concat(inner))),
            sep,
            close_doc,
        ]);
        let body = if preserve && expanded {
            // A list the source spread over several lines keeps its layout and
            // forces the enclosing groups to break around it.
            match group(body, true) {
                Doc::Group {
                    doc,
                    expanded,
                    broken,
                    ..
                } => Doc::Group {
                    doc,
                    expanded,
                    broken,
                    up: true,
                    hug: false,
                },
                other => other,
            }
        } else {
            group(body, false)
        };
        (lead, Doc::Concat(vec![body, after]))
    }

    /// Whether token `at` is outside every bracket group of `lo..at`.
    fn depth_is_top(&self, lo: usize, at: usize) -> bool {
        let mut i = lo;
        while i < at {
            if self.is_open(i) {
                if self.close[i] >= at {
                    return false;
                }
                i = self.close[i] + 1;
            } else {
                i += 1;
            }
        }
        true
    }

    fn container_doc(
        &self,
        open: usize,
        close: usize,
        chunks: Vec<Chunk>,
        expanded: bool,
        spaced: bool,
        first: bool,
    ) -> (Vec<Doc>, Doc) {
        // A body holding something that cannot be printed on one line (an
        // expanded block, an own-line comment) is itself expanded.
        let expanded = expanded || chunks.iter().any(|chunk| flat_width(&chunk.doc).is_none());
        let (lead, open_doc) = self.tok_split(open, first, spaced, None, true);
        let dangling = self.dangling(close);
        if chunks.is_empty() && dangling.is_none() {
            let (close_doc, after) = self.close_tok(close, true);
            return (
                lead,
                Doc::Concat(vec![without_break_parent(open_doc), close_doc, after]),
            );
        }
        let mut inner = vec![Doc::Line];
        for (k, chunk) in chunks.into_iter().enumerate() {
            if k > 0 {
                inner.push(Doc::Line);
                if expanded && chunk.blank_before {
                    inner.push(Doc::Line);
                }
            }
            inner.push(chunk.doc);
        }
        let had_dangling = dangling.is_some();
        if let Some(comments) = dangling {
            inner.push(comments);
        }
        let (close_doc, after) = self.close_tok(close, !had_dangling);
        let body = hug_group(
            Doc::Concat(vec![
                open_doc,
                indent(Doc::Concat(inner)),
                Doc::Line,
                close_doc,
            ]),
            expanded || had_dangling,
        );
        (lead, Doc::Concat(vec![body, after]))
    }

    fn block_doc(&self, open: usize, close: usize, spaced: bool, first: bool) -> (Vec<Doc>, Doc) {
        let force = self.force_expand.replace(false);
        self.depth.set(self.depth.get() + 1);
        let chunks = self
            .segment_statements(open + 1, close)
            .into_iter()
            .map(|(lo, hi)| Chunk {
                doc: self.run(lo, hi, Head::None),
                blank_before: self.first_atom_blank(lo),
            })
            .collect();
        self.depth.set(self.depth.get() - 1);
        self.force_expand.set(force);
        let expanded = force || self.newline_between(open, close);
        self.container_doc(open, close, chunks, expanded, spaced, first)
    }

    fn match_doc(&self, open: usize, close: usize, spaced: bool, first: bool) -> (Vec<Doc>, Doc) {
        let force = self.force_expand.replace(false);
        self.depth.set(self.depth.get() + 1);
        let arms = self.segment_arms(open + 1, close);
        let count = arms.len();
        let chunks = arms
            .into_iter()
            .enumerate()
            .map(|(k, (lo, hi, comma))| {
                let last = k + 1 == count;
                let block_like = {
                    let body = self.arm_body_start(lo, hi);
                    body.is_some_and(|b| self.is_block_like(b))
                };
                let mut parts = vec![self.run(lo, hi, Head::None)];
                let comma_doc = |present: Option<usize>| match present {
                    Some(c) => self.comments_only(c, false),
                    None => Doc::Nil,
                };
                if block_like {
                    if !last {
                        parts.push(Doc::IfBreak(Box::new(Doc::Nil), Box::new(text(","))));
                    }
                } else if last {
                    parts.push(Doc::IfBreak(Box::new(text(",")), Box::new(Doc::Nil)));
                } else {
                    parts.push(text(","));
                }
                parts.push(comma_doc(comma));
                Chunk {
                    doc: Doc::Concat(parts),
                    blank_before: self.first_atom_blank(lo),
                }
            })
            .collect();
        self.depth.set(self.depth.get() - 1);
        self.force_expand.set(force);
        let expanded = self.newline_between(open, close);
        self.container_doc(open, close, chunks, expanded, spaced, first)
    }

    fn item_body_doc(
        &self,
        open: usize,
        close: usize,
        spaced: bool,
        first: bool,
    ) -> (Vec<Doc>, Doc) {
        let force = self.force_expand.replace(false);
        self.depth.set(self.depth.get() + 1);
        let chunks = self
            .segment_members(open + 1, close)
            .into_iter()
            .map(|(lo, hi)| Chunk {
                doc: self.run(lo, hi, Head::None),
                blank_before: self.first_atom_blank(lo),
            })
            .collect();
        self.depth.set(self.depth.get() - 1);
        self.force_expand.set(force);
        let expanded = self.newline_between(open, close);
        self.container_doc(open, close, chunks, expanded, spaced, first)
    }

    // -- segmentation -------------------------------------------------------

    fn is_block_like(&self, i: usize) -> bool {
        self.sym(i) == "{" || matches!(self.word(i), Some("if" | "match"))
    }

    /// End (exclusive) of a statement that starts with a block-like construct,
    /// without a trailing semicolon.
    fn block_construct_end(&self, start: usize, hi: usize) -> usize {
        let mut i = start;
        if self.sym(i) == "{" {
            return self.close[i] + 1;
        }
        if self.word(i) == Some("if") {
            loop {
                i += 1;
                while i < hi && !(self.sym(i) == "{" && self.is_open(i)) {
                    i = self.skip(i);
                }
                if i >= hi {
                    return hi;
                }
                i = self.close[i] + 1;
                if i < hi && self.word(i) == Some("else") {
                    i += 1;
                    if i < hi && self.word(i) == Some("if") {
                        continue;
                    }
                    if i < hi && self.sym(i) == "{" && self.is_open(i) {
                        return self.close[i] + 1;
                    }
                }
                return i;
            }
        }
        // `match` and `loop`: a header, then one brace group.
        i += 1;
        while i < hi && !(self.sym(i) == "{" && self.is_open(i)) {
            i = self.skip(i);
        }
        if i >= hi {
            hi
        } else {
            self.close[i] + 1
        }
    }

    fn statement_end(&self, start: usize, hi: usize) -> usize {
        let word = self.word(start);
        let mut end = match word {
            Some("if" | "match" | "loop") => self.block_construct_end(start, hi),
            _ if self.sym(start) == "{" && self.is_open(start) => self.close[start] + 1,
            Some("try") => {
                let mut i = start + 1;
                loop {
                    if i >= hi {
                        break hi;
                    }
                    if self.sym(i) == ";" {
                        break i + 1;
                    }
                    if self.word(i) == Some("else") {
                        i += 1;
                        if i < hi && self.word(i).is_some() {
                            i += 1;
                        }
                        break if i < hi && self.sym(i) == "{" && self.is_open(i) {
                            self.close[i] + 1
                        } else {
                            hi
                        };
                    }
                    i = self.skip(i);
                }
            }
            _ => {
                let mut i = start;
                loop {
                    if i >= hi {
                        break hi;
                    }
                    if self.sym(i) == ";" && !self.is_open(i) {
                        break i + 1;
                    }
                    i = self.skip(i);
                }
            }
        };
        if matches!(word, Some("if" | "match" | "loop" | "try")) || self.sym(start) == "{" {
            if end < hi && self.sym(end) == ";" {
                end += 1;
            }
        }
        end.min(hi).max(start + 1)
    }

    fn segment_statements(&self, lo: usize, hi: usize) -> Vec<(usize, usize)> {
        let mut out = Vec::new();
        let mut i = lo;
        while i < hi {
            let end = self.statement_end(i, hi);
            out.push((i, end));
            i = end;
        }
        out
    }

    fn arm_body_start(&self, lo: usize, hi: usize) -> Option<usize> {
        let mut i = lo;
        while i < hi {
            if self.sym(i) == "=>" && !self.is_open(i) {
                return (i + 1 < hi).then_some(i + 1);
            }
            i = self.skip(i);
        }
        None
    }

    /// Arms as (first token, end exclusive of the arm without its comma, comma).
    fn segment_arms(&self, lo: usize, hi: usize) -> Vec<(usize, usize, Option<usize>)> {
        let mut arms = Vec::new();
        let mut i = lo;
        while i < hi {
            let start = i;
            let Some(body) = self.arm_body_start(start, hi) else {
                arms.push((start, hi, None));
                break;
            };
            let end;
            if self.is_block_like(body) {
                end = self.block_construct_end(body, hi);
            } else {
                let mut j = body;
                let mut generic_depth = 0usize;
                while j < hi && !(self.sym(j) == "," && generic_depth == 0) {
                    if self.generic[j] {
                        match self.sym(j) {
                            "<" => generic_depth += 1,
                            ">" => generic_depth = generic_depth.saturating_sub(1),
                            _ => {}
                        }
                    }
                    j = self.skip(j);
                }
                end = j.min(hi);
            }
            if end < hi && self.sym(end) == "," {
                arms.push((start, end, Some(end)));
                i = end + 1;
            } else {
                arms.push((start, end, None));
                i = end;
            }
        }
        arms
    }

    fn segment_members(&self, lo: usize, hi: usize) -> Vec<(usize, usize)> {
        let mut out = Vec::new();
        let mut i = lo;
        while i < hi {
            let start = i;
            let mut arrow = false;
            let mut j = i;
            let end = loop {
                if j >= hi {
                    break hi;
                }
                if self.sym(j) == ";" {
                    break j + 1;
                }
                if self.sym(j) == "=>" {
                    arrow = true;
                } else if j > start && arrow && self.starts_member(j) {
                    break j;
                }
                if self.sym(j) == "{" && self.is_open(j) {
                    if arrow || self.looks_like_fields(j) {
                        j = self.close[j] + 1;
                        continue;
                    }
                    break self.close[j] + 1;
                }
                j = self.skip(j);
            };
            out.push((start, end));
            i = end;
        }
        out
    }

    fn starts_member(&self, i: usize) -> bool {
        match self.word(i) {
            Some("pub" | "type") => true,
            Some("fn") => self.word(i + 1).is_some(),
            _ => false,
        }
    }

    // -- file ---------------------------------------------------------------

    fn head_of(&self, lo: usize, hi: usize) -> Head {
        let mut i = lo;
        while i < hi && matches!(self.word(i), Some("pub" | "test" | "extern")) {
            i += 1;
        }
        match self.word(i) {
            Some("type") => Head::Type,
            Some("interface") => Head::Interface,
            Some("extend") => Head::Extend,
            _ => Head::None,
        }
    }

    fn format(&self) -> String {
        let eof = self.tokens.len() - 1;
        let mut docs: Vec<(Doc, bool, usize)> = Vec::new();
        for (k, &start) in self.item_starts.iter().enumerate() {
            let end = self.item_starts.get(k + 1).copied().unwrap_or(eof);
            let head = self.head_of(start, end);
            let doc = self.run(start, end, head);
            self.ignore_leading.set(start);
            let body = self.run(start, end, head);
            self.ignore_leading.set(NO_CLOSE);
            let single = flat_width(&body).is_some_and(|w| w <= MAX_WIDTH);
            docs.push((doc, single, start));
        }
        let mut parts: Vec<Doc> = Vec::new();
        let mut previous_single = false;
        for (k, (doc, single, start)) in docs.into_iter().enumerate() {
            if k > 0 {
                parts.push(Doc::HardLine);
                if !(previous_single && single) || self.first_atom_blank(start) {
                    parts.push(Doc::HardLine);
                }
            }
            parts.push(doc);
            previous_single = single;
        }
        // Comments after the last item.
        for (k, comment) in self.info[eof].leading.iter().enumerate() {
            if k > 0 || !parts.is_empty() {
                parts.push(Doc::HardLine);
                if comment.newlines_before >= 2 {
                    parts.push(Doc::HardLine);
                }
            }
            parts.push(text(comment.text.clone()));
        }
        let mut output = print(&Doc::Concat(parts));
        if !output.is_empty() {
            output.push('\n');
        }
        output
    }
}
