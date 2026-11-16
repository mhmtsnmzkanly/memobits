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
