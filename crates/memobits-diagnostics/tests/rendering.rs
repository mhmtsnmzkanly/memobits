use memobits_diagnostics::{render, Diagnostic, Severity, SourceFile, SourceId, Span};

fn diagnostic(start: usize, end: usize) -> Diagnostic {
    let mut diagnostic = Diagnostic::new(
        "SE001".parse().unwrap(),
        Severity::Warning,
        "unexpected token",
    );
    diagnostic.span = Some(Span {
        source: SourceId(7),
        start,
        end,
    });
    diagnostic.help = Some("remove the token".into());
    diagnostic
}

#[test]
fn renders_unicode_byte_offsets_as_readable_columns() {
    let source = SourceFile {
        id: SourceId(7),
        name: "example.memo",
        text: "first\nα β\n",
    };
    assert_eq!(render(&diagnostic(9, 11), Some(source)),
        "warning[SE001]: unexpected token\n --> example.memo:2:3\n 2 | α β\n   |   ^\n help: remove the token\n");
}

#[test]
fn invalid_and_unavailable_locations_preserve_message_and_help() {
    let source = SourceFile {
        id: SourceId(7),
        name: "example.memo",
        text: "α\n",
    };
    for (start, end) in [(2, 1), (0, 99), (1, 2), (usize::MAX, usize::MAX)] {
        let result = render(&diagnostic(start, end), Some(source));
        assert!(result.contains("invalid span"));
        assert!(result.contains("unexpected token"));
        assert!(result.contains("remove the token"));
    }
    assert!(render(&diagnostic(0, 0), None).contains("source unavailable"));
    let wrong_source = SourceFile {
        id: SourceId(8),
        ..source
    };
    assert!(render(&diagnostic(0, 0), Some(wrong_source)).contains("source unavailable"));
}

#[test]
fn handles_empty_eof_crlf_and_multiline_spans() {
    for text in ["", "a\n", "a\r\n", "α"] {
        let source = SourceFile {
            id: SourceId(7),
            name: "input",
            text,
        };
        assert!(render(&diagnostic(text.len(), text.len()), Some(source)).contains('^'));
    }
    let source = SourceFile {
        id: SourceId(7),
        name: "input",
        text: "first\nsecond",
    };
    assert!(render(&diagnostic(1, 9), Some(source)).contains("span continues"));
}

#[test]
fn project_diagnostics_need_no_source() {
    let diagnostic = Diagnostic::new(
        "PE001".parse().unwrap(),
        Severity::Error,
        "manifest missing",
    );
    assert_eq!(
        render(&diagnostic, None),
        "error[PE001]: manifest missing\n"
    );
}

#[test]
fn renders_secondary_labels_as_notes_with_snippets() {
    let source = SourceFile {
        id: SourceId(7),
        name: "a.mb",
        text: "var r := x.share();\nx = 1;\n",
    };
    let span = |start, end| Span {
        source: SourceId(7),
        start,
        end,
    };
    let mut d = Diagnostic::new("BE005".parse().unwrap(), Severity::Error, "cannot write")
        .with_label(span(9, 18), "`x` was shared here");
    d.span = Some(span(20, 21));
    assert_eq!(
        render(&d, Some(source)),
        "error[BE005]: cannot write\n --> a.mb:2:1\n 2 | x = 1;\n   | ^\n note: `x` was shared here\n --> a.mb:1:10\n 1 | var r := x.share();\n   |          ^^^^^^^^^\n"
    );
}

#[test]
fn labels_in_other_sources_fall_back_to_raw_locations() {
    let mut d = Diagnostic::new("BE005".parse().unwrap(), Severity::Error, "m").with_label(
        Span {
            source: SourceId(9),
            start: 1,
            end: 2,
        },
        "elsewhere",
    );
    d.span = None;
    let out = render(&d, None);
    assert!(out.contains("note: elsewhere"));
    assert!(out.contains("source 9 bytes 1..2"));
}
