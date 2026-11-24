use memobits_diagnostics::SourceId;
use memobits_syntax::{
    lex, parse, Access, ExprKind, GenericParameterKind, ItemKind, StatementKind, TypeArgument,
};

#[test]
fn parses_real_project_sources() {
    for source in [
        include_str!("../../../examples/topics/numeric/src/main.mb"),
        include_str!("../../../examples/topics/numeric/src/math.mb"),
        include_str!("../../../examples/topics/enums/src/main.mb"),
    ] {
        let result = parse(SourceId(0), source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert!(!result.module.items.is_empty());
    }
}

#[test]
fn postfix_optional_type_preserves_grouped_reference_precedence() {
    let parsed = parse(
        SourceId(0),
        "fn f(value: borrow i32?, wrapped: (borrow i32)?) {}",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function { parameters, .. } = &parsed.module.items[0].kind else {
        panic!("expected a function");
    };
    assert_eq!(parameters[0].access, Access::Borrow);
    assert_eq!(parameters[0].ty.path, ["?"]);
    let [TypeArgument::Type(borrowed_option)] = parameters[0].ty.arguments.as_slice() else {
        panic!("expected an owned Option payload");
    };
    assert_eq!(borrowed_option.path, ["i32"]);
    assert_eq!(parameters[1].access, Access::Owned);
    assert_eq!(parameters[1].ty.path, ["?"]);
    let [TypeArgument::Reference {
        access: Access::Borrow,
        referent,
        ..
    }] = parameters[1].ty.arguments.as_slice()
    else {
        panic!("expected an Option containing a borrow");
    };
    assert_eq!(referent.path, ["i32"]);
}

#[test]
fn parses_bodyless_nominal_types_separately_from_empty_structs() {
    let parsed = parse(SourceId(0), "type Token; type Empty {}");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Type {
        definition: memobits_syntax::TypeDefinition::Bodyless,
        ..
    } = &parsed.module.items[0].kind
    else {
        panic!("expected a bodyless nominal declaration");
    };
    let ItemKind::Type {
        definition: memobits_syntax::TypeDefinition::Struct(fields),
        ..
    } = &parsed.module.items[1].kind
    else {
        panic!("expected an empty struct declaration");
    };
    assert!(fields.is_empty());
}

#[test]
fn parses_inherent_extensions_without_an_interface_constraint() {
    let parsed = parse(
        SourceId(0),
        "type Point; extend Point { fn zero(borrow self) -> i32 { 0 } }",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::InherentExtension {
        target, methods, ..
    } = &parsed.module.items[1].kind
    else {
        panic!("expected an inherent extension");
    };
    assert_eq!(target.path, ["Point"]);
    assert_eq!(methods[0].name, "zero");
    assert_eq!(methods[0].receiver, Access::Borrow);
}

#[test]
fn parses_trailing_inherent_extension_as_a_type_associated_item() {
    let parsed = parse(
        SourceId(0),
        "type Point { x: i32 } extend { fn zero(borrow self) -> i32 { 0 } }",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert!(matches!(
        parsed.module.items[0].kind,
        ItemKind::Type {
            definition: memobits_syntax::TypeDefinition::Struct(_),
            ..
        }
    ));
    let ItemKind::InherentExtension {
        target, methods, ..
    } = &parsed.module.items[1].kind
    else {
        panic!("expected the trailing inherent extension");
    };
    assert_eq!(target.path, ["Point"]);
    assert_eq!(methods[0].name, "zero");
}

#[test]
fn generic_trailing_inherent_extensions_parse_and_alias_extensions_remain_gated() {
    for source in [
        "type Box<T> { value: T } extend { fn value(borrow self) -> T { self.value } }",
        "type Packet<const N: u32> { value: array<u32, N> } extend { fn value(borrow self) -> u32 { self.value[0] } }",
    ] {
        let parsed = parse(SourceId(41), source);
        assert!(parsed.diagnostics.is_empty(), "{source}: {:?}", parsed.diagnostics);
        assert_eq!(parsed.module.items.len(), 2, "{source}");
        let ItemKind::InherentExtension { target, generic_parameters, methods, .. } =
            &parsed.module.items[1].kind
        else {
            panic!("expected trailing inherent extension: {source}");
        };
        assert_eq!(target.arguments.len(), 1, "{source}");
        assert_eq!(generic_parameters.len(), 1, "{source}");
        assert_eq!(methods.len(), 1, "{source}");
    }

    syntax_error(
        "type Alias<T> = array<T, 1>; extend { fn value(borrow self) -> i32 { 0 } }",
        "inherent extensions require a nominal type declaration",
    );
}

#[test]
fn parses_interface_and_borrowing_extension_methods() {
    let result = parse(
        SourceId(0),
        "pub interface Draw { fn draw(borrow self) -> i32; }\ntype Point { x: i32 }\nextend Point of Draw { fn draw(borrow self) -> i32 { 42 } }",
    );
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(matches!(
        &result.module.items[0].kind,
        ItemKind::Interface { public: true, name, methods, .. }
            if name == "Draw" && methods.len() == 1 && methods[0].receiver == Access::Borrow
    ));
    assert!(matches!(
        &result.module.items[2].kind,
        ItemKind::Extension { methods, .. }
            if methods.len() == 1 && methods[0].body.is_some()
    ));
}

#[test]
fn interface_extension_words_remain_valid_identifiers_outside_declaration_positions() {
    let result = parse(
        SourceId(0),
        "fn extend(of: i32) -> i32 { let interface := of; interface }",
    );
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
}

#[test]
fn generic_function_type_and_const_parameter_syntax_parses() {
    let parsed = parse(
        SourceId(0),
        "interface Draw { fn draw(borrow self) -> i32; } type Buffer<T, const N: u32> { data: array<T, N> } fn project<T, const N: u32>(value: T) -> array<T, N> where T: Draw { value }",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Type {
        generic_parameters, ..
    } = &parsed.module.items[1].kind
    else {
        panic!()
    };
    assert_eq!(generic_parameters.len(), 2);
    assert!(matches!(
        generic_parameters[1].kind,
        GenericParameterKind::Const(_)
    ));
    let ItemKind::Function {
        generic_parameters,
        bounds,
        result,
        ..
    } = &parsed.module.items[2].kind
    else {
        panic!()
    };
    assert_eq!(generic_parameters.len(), 2);
    assert_eq!(bounds.len(), 1);
    assert_eq!(bounds[0].parameter, "T");
    assert_eq!(result.as_ref().unwrap().arguments.len(), 2);
    assert!(matches!(
        result.as_ref().unwrap().arguments[1],
        TypeArgument::Const(_)
    ));
}

#[test]
fn generic_struct_constructor_keeps_explicit_type_arguments() {
    let parsed = parse(
        SourceId(0),
        "fn make() { let value := Box<i32> { item: 42 }; }",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
        panic!()
    };
    let StatementKind::Binding { value, .. } = &body.statements[0].kind else {
        panic!()
    };
    let ExprKind::Struct {
        type_arguments,
        fields,
        ..
    } = &value.kind
    else {
        panic!()
    };
    assert_eq!(type_arguments.len(), 1);
    assert_eq!(fields[0].name, "item");
}

#[test]
fn parses_explicit_interface_selection_on_a_call() {
    let result = parse(
        SourceId(0),
        "fn f(point: Point) { (point.draw() of graphics::Draw).inspect(); }",
    );
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    let ItemKind::Function { body, .. } = &result.module.items[0].kind else {
        panic!()
    };
    let StatementKind::Expression(expression) = &body.statements[0].kind else {
        panic!()
    };
    let ExprKind::Call { callee, .. } = &expression.kind else {
        panic!()
    };
    let ExprKind::Field { base, name } = &callee.kind else {
        panic!()
    };
    assert_eq!(name, "inspect");
    let ExprKind::Call { interface, .. } = &base.kind else {
        panic!()
    };
    assert_eq!(interface.as_ref().unwrap().path, ["graphics", "Draw"]);
}

#[test]
fn grouped_symbol_imports_expand_to_individual_bindings() {
    let result = parse(
        SourceId(0),
        "use graphics::{Color as Hue, Draw}; fn main() {}",
    );
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    let uses = result
        .module
        .items
        .iter()
        .filter_map(|item| match &item.kind {
            ItemKind::Use { path, alias, .. } => Some((path, alias)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(uses.len(), 2);
    assert_eq!(
        uses[0],
        (
            &vec!["graphics".to_owned(), "Color".to_owned()],
            &Some("Hue".to_owned())
        )
    );
    assert_eq!(uses[1].0, &["graphics", "Draw"]);
}

#[test]
fn string_literals_preserve_utf8_and_quoted_byte_spans() {
    let source = "fn f() { let empty := \"\"; \"café 😀 // /* }}\" }";
    let result = parse(SourceId(0), source);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    let ItemKind::Function { body, .. } = &result.module.items[0].kind else {
        panic!()
    };
    let StatementKind::Binding { value, .. } = &body.statements[0].kind else {
        panic!()
    };
    // `}}` is an escaped brace, so the text holds a single `}`.
    for (expr, expected, written) in [
        (value, "", ""),
        (
            body.tail.as_deref().unwrap(),
            "café 😀 // /* }",
            "café 😀 // /* }}",
        ),
    ] {
        assert_eq!(expr.kind, ExprKind::StringLiteral(expected.into()));
        assert_eq!(
            &source[expr.span.start..expr.span.end],
            format!("\"{written}\"")
        );
    }
}

#[test]
fn character_literals_decode_one_unicode_scalar_and_escapes() {
    let source = r#"fn f() { 'a'; 'é'; '😀'; '\n'; '\'' }"#;
    let result = parse(SourceId(0), source);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    let ItemKind::Function { body, .. } = &result.module.items[0].kind else {
        panic!()
    };
    let values = body
        .statements
        .iter()
        .map(|statement| match &statement.kind {
            StatementKind::Expression(expr) => match expr.kind {
                ExprKind::CharLiteral(ch) => ch,
                _ => panic!("{expr:?}"),
            },
            _ => panic!("{statement:?}"),
        })
        .collect::<Vec<_>>();
    let tail = body.tail.as_deref().unwrap();
    assert_eq!(tail.kind, ExprKind::CharLiteral('\''));
    assert_eq!(values, ['a', 'é', '😀', '\n']);
}

#[test]
fn tuples_parse_as_ordered_types_and_expressions_without_changing_grouping() {
    let source = "fn pair(v: (i32, bool)) -> (i32, bool) { (1, true) } fn grouped() -> i32 { (1) } fn first(v: (i32, bool)) -> i32 { v.0 }";
    let result = parse(SourceId(0), source);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    let ItemKind::Function {
        parameters,
        result: Some(result_ty),
        body,
        ..
    } = &result.module.items[0].kind
    else {
        panic!()
    };
    assert_eq!(parameters[0].ty.path, ["\0tuple"]);
    assert_eq!(result_ty.path, ["\0tuple"]);
    assert!(matches!(
        body.tail.as_deref().unwrap().kind,
        ExprKind::Tuple(_)
    ));
    let ItemKind::Function { body, .. } = &result.module.items[1].kind else {
        panic!()
    };
    assert_eq!(
        body.tail.as_deref().unwrap().kind,
        ExprKind::Number("1".into())
    );
    let ItemKind::Function { body, .. } = &result.module.items[2].kind else {
        panic!()
    };
    assert!(
        matches!(&body.tail.as_deref().unwrap().kind, ExprKind::Field { name, .. } if name == "0")
    );
}

#[test]
fn labeled_tuple_shapes_and_initializers_preserve_labels_and_order() {
    let source =
        "fn f(v: (left: i32, right: bool)) -> i32 { let pair := (right: true, left: 1); v.left }";
    let result = parse(SourceId(0), source);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    let ItemKind::Function {
        parameters, body, ..
    } = &result.module.items[0].kind
    else {
        panic!()
    };
    let TypeArgument::TupleField {
        label: Some(left), ..
    } = &parameters[0].ty.arguments[0]
    else {
        panic!()
    };
    assert_eq!(left, "left");
    let StatementKind::Binding { value, .. } = &body.statements[0].kind else {
        panic!()
    };
    let ExprKind::Tuple(elements) = &value.kind else {
        panic!()
    };
    assert_eq!(
        elements
            .iter()
            .map(|element| element.label.as_deref())
            .collect::<Vec<_>>(),
        [Some("right"), Some("left")]
    );
}

#[test]
fn malformed_character_literals_report_scalar_errors_and_recover() {
    for source in ["fn f() { ''; }", "fn f() { 'ab'; }", "fn f() { 'a\n'; }"] {
        let result = parse(SourceId(0), source);
        assert!(
            result
                .diagnostics
                .iter()
                .any(|d| d.message.contains("exactly one Unicode scalar")),
            "{source}: {:?}",
            result.diagnostics
        );
    }
    let result = parse(SourceId(0), r#"fn f() { '\q'; }"#);
    assert!(result
        .diagnostics
        .iter()
        .any(|d| d.message.contains("unsupported escape")));
    let surrogate = parse(SourceId(0), r#"fn f() { '\u{D800}'; }"#);
    assert!(surrogate
        .diagnostics
        .iter()
        .any(|d| d.message.contains("unsupported escape")));
}

#[test]
fn malformed_string_literals_report_lexical_errors_and_recover() {
    for (source, message) in [
        (
            r#"fn f() { "é\"ok"; } fn next() {}"#,
            "escapes in string literals",
        ),
        (
            "fn f() { \"é\n; } fn next() {}",
            "newline in string literal",
        ),
        (
            "fn f() { \"é\r\n; } fn next() {}",
            "newline in string literal",
        ),
        ("fn f() { \"é", "unterminated string literal"),
    ] {
        let lexed = lex(SourceId(0), source);
        assert_eq!(lexed.diagnostics.len(), 1, "{source:?}");
        let error = &lexed.diagnostics[0];
        assert_eq!(error.code.to_string(), "SE001");
        assert!(error.message.contains(message), "{error:?}");
        let span = error.span.unwrap();
        assert!(source.get(span.start..span.end).is_some(), "{span:?}");
        if source.contains("fn next") {
            let parsed = parse(SourceId(0), source);
            assert_eq!(parsed.diagnostics.len(), 1, "{:?}", parsed.diagnostics);
            assert!(
                matches!(&parsed.module.items[1].kind, ItemKind::Function { name, .. } if name == "next")
            );
        }
    }
}

#[test]
fn precedence_and_access_modes_are_preserved() {
    let result = parse(
        SourceId(1),
        "fn f(a: borrow Player, b: share Player, var c: Player) -> i32 { let n := 1 + 2 * 3; n }",
    );
    assert!(result.diagnostics.is_empty());
    let ItemKind::Function {
        parameters, body, ..
    } = &result.module.items[0].kind
    else {
        panic!()
    };
    assert_eq!(parameters[0].access, Access::Borrow);
    assert_eq!(parameters[1].access, Access::Share);
    assert!(parameters[2].mutable);
    let StatementKind::Binding { value, .. } = &body.statements[0].kind else {
        panic!()
    };
    let ExprKind::Binary {
        operator, right, ..
    } = &value.kind
    else {
        panic!()
    };
    assert_eq!(operator, "+");
    assert!(matches!(&right.kind, ExprKind::Binary { operator, .. } if operator == "*"));
    assert!(body.tail.is_some());
}

#[test]
fn parses_documented_access_conversion_suffixes() {
    let result = parse(
        SourceId(5),
        "fn use_value(value: i32) { consume(value.borrow()); consume(value.share()); consume(value.copy()); }",
    );
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    let ItemKind::Function { body, .. } = &result.module.items[0].kind else {
        panic!()
    };

    for (index, expected) in ["borrow", "share", "copy"].into_iter().enumerate() {
        let StatementKind::Expression(expression) = &body.statements[index].kind else {
            panic!("expected outer call expression")
        };
        let ExprKind::Call { arguments, .. } = &expression.kind else {
            panic!("expected outer call")
        };
        let ExprKind::Call {
            callee,
            arguments: suffix_args,
            ..
        } = &arguments[0].kind
        else {
            panic!("expected conversion call")
        };
        assert!(suffix_args.is_empty());
        assert!(matches!(&callee.kind, ExprKind::Field { name, .. } if name == expected));
    }
}

#[test]
fn borrow_and_share_remain_reserved_as_function_and_binding_names() {
    for source in ["fn borrow() {}", "fn f() { let share := 1; }"] {
        let result = parse(SourceId(6), source);
        assert!(!result.diagnostics.is_empty(), "{source}");
    }
}

#[test]
fn accepted_type_forms_and_loop_parse() {
    let source = "pub type Player { pub score: i32 } type State [ Idle, Active(i32) ] type Id = u64; fn f() { var n: i32 = 0; loop { if n > 3 { break; } n += 1; continue; } return; }";
    let result = parse(SourceId(2), source);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert_eq!(result.module.items.len(), 4);
}

#[test]
fn rejects_legacy_and_incomplete_syntax_without_hanging() {
    for source in [
        "fn f() { let x = 1; }",
        "fn f() { while true {} }",
        "struct X {}",
        "fn f(",
        "fn f() { let x := ; return; }",
        "type X [ Broken(",
    ] {
        let result = parse(SourceId(3), source);
        assert!(!result.diagnostics.is_empty(), "{source}");
        for d in result.diagnostics {
            let span = d.span.unwrap();
            assert!(source.is_char_boundary(span.start));
            assert!(source.is_char_boundary(span.end));
        }
    }
}

#[test]
fn utf8_errors_and_nested_comments_have_valid_spans() {
    let text = "/* outer /* nested */ done */ 🙂 fn valid() {}";
    let result = lex(SourceId(4), text);
    assert_eq!(result.diagnostics.len(), 1);
    let span = result.diagnostics[0].span.unwrap();
    assert_eq!(&text[span.start..span.end], "🙂");
    let parsed = parse(SourceId(4), text);
    assert_eq!(parsed.module.items.len(), 1);
    assert!(!lex(SourceId(0), "/* unfinished").diagnostics.is_empty());
}

#[test]
fn parses_reference_type_arguments_with_access_and_spans() {
    use memobits_syntax::{Access, TypeArgument};

    let source = "fn f(a: borrow (borrow math::Value)?, b: (share array<i32, 2>)?) {}";
    let parsed = parse(SourceId(0), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function { parameters, .. } = &parsed.module.items[0].kind else {
        panic!()
    };
    assert_eq!(parameters[0].access, Access::Borrow);
    assert_eq!(parameters[1].access, Access::Owned);
    for (parameter, expected_access, expected_text, expected_path) in [
        (
            &parameters[0],
            Access::Borrow,
            "borrow math::Value",
            &["math", "Value"][..],
        ),
        (
            &parameters[1],
            Access::Share,
            "share array<i32, 2>",
            &["array"][..],
        ),
    ] {
        let TypeArgument::Reference {
            span,
            access,
            referent,
        } = &parameter.ty.arguments[0]
        else {
            panic!()
        };
        assert_eq!(*access, expected_access);
        assert_eq!(&source[span.start..span.end], expected_text);
        assert_eq!(referent.path, expected_path);
    }
    assert!(!parse(SourceId(0), "type Bad = array<i32, borrow i32>;")
        .diagnostics
        .is_empty());
}

#[test]
fn arrays_preserve_nested_types_literals_and_spans() {
    use memobits_syntax::TypeArgument;
    let source = "fn f(a: array<array<i32, 0>, 1_000>) { [1, 2,]; []; [f(); 03]; }";
    let parsed = parse(SourceId(0), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function {
        parameters, body, ..
    } = &parsed.module.items[0].kind
    else {
        panic!()
    };
    let ty = &parameters[0].ty;
    assert_eq!(
        &source[ty.span.start..ty.span.end],
        "array<array<i32, 0>, 1_000>"
    );
    let TypeArgument::Type(inner) = &ty.arguments[0] else {
        panic!()
    };
    assert_eq!(inner.path, ["array"]);
    let TypeArgument::Integer(count) = &ty.arguments[1] else {
        panic!()
    };
    assert_eq!(count.raw, "1_000");
    let StatementKind::Expression(expr) = &body.statements[2].kind else {
        panic!()
    };
    let ExprKind::RepeatArray { value, count } = &expr.kind else {
        panic!()
    };
    assert!(matches!(value.kind, ExprKind::Call { .. }));
    assert_eq!(count.raw, "03");
    assert_eq!(&source[count.span.start..count.span.end], "03");
    assert_eq!(&source[expr.span.start..expr.span.end], "[f(); 03]");
}

#[test]
fn nested_generic_closers_remain_separate_from_right_shift_tokens() {
    let source = "use alloc::List; fn f(value: List<List<u32>>) -> u32 { value >> 1 }";
    let parsed = parse(SourceId(0), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
}

#[test]
fn indexing_chains_with_calls_fields_and_unary_precedence() {
    let parsed = parse(SourceId(0), "fn f() { -a[1 + 2].b()[0] * 3 }");
    assert!(parsed.diagnostics.is_empty());
    let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
        panic!()
    };
    let ExprKind::Binary { left, .. } = &body.tail.as_ref().unwrap().kind else {
        panic!()
    };
    let ExprKind::Unary { operand, .. } = &left.kind else {
        panic!()
    };
    let ExprKind::Index { base, .. } = &operand.kind else {
        panic!()
    };
    assert!(matches!(base.kind, ExprKind::Call { .. }));
}

#[test]
fn malformed_arrays_recover_to_following_statements_and_items() {
    for malformed in [
        "[1,,2]",
        "[1; -1]",
        "[1; 1.5]",
        "a[]",
        "[1; n]",
        "[1; 2 + 3]",
    ] {
        let parsed = parse(
            SourceId(0),
            &format!("fn f() {{ {malformed}; let good := 3; }} fn g() {{}}"),
        );
        assert!(!parsed.diagnostics.is_empty(), "{malformed}");
        assert_eq!(parsed.module.items.len(), 2, "{malformed}");
        let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
            panic!()
        };
        assert_eq!(body.statements.len(), 1, "{malformed}");
    }
    for ty in [
        "array<i32>",
        "array<i32, -1>",
        "array<i32, 1.0>",
        "array<i32, n>",
        "array<i32, 1 + 2>",
        "array<i32, 1, 2>",
        "i32<u8, 2>",
        "array",
    ] {
        let parsed = parse(SourceId(0), &format!("fn bad(a: {ty}) {{}} fn good() {{}}"));
        assert!(!parsed.diagnostics.is_empty(), "{ty}");
        assert!(
            parsed
                .module
                .items
                .iter()
                .any(|i| matches!(&i.kind, ItemKind::Function { name, .. } if name == "good")),
            "{ty}"
        );
    }
}

fn function_body(source: &str) -> memobits_syntax::Block {
    let parsed = parse(SourceId(7), source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
        panic!()
    };
    body.clone()
}

#[test]
fn block_like_statements_end_at_their_closing_brace() {
    let body = function_body("fn f(c: bool) -> array<i32, 2> { if c { return [5, 6]; } [7, 8] }");
    assert_eq!(body.statements.len(), 1);
    assert!(
        matches!(body.statements[0].kind, StatementKind::Expression(ref e) if matches!(e.kind, ExprKind::If { .. }))
    );
    assert!(
        matches!(body.tail.as_deref().map(|e| &e.kind), Some(ExprKind::Array(v)) if v.len() == 2)
    );

    let body = function_body("fn main() -> i32 { var x := 1; if x == 1 { x = 2; } (x + 1) }");
    assert_eq!(body.statements.len(), 2);
    assert!(
        matches!(body.statements[1].kind, StatementKind::Expression(ref e) if matches!(e.kind, ExprKind::If { .. }))
    );
    assert!(
        matches!(body.tail.as_deref().map(|e| &e.kind), Some(ExprKind::Binary { operator, .. }) if operator == "+")
    );

    let body = function_body("fn f() -> i32 { loop { break; } [1, 2] }");
    assert_eq!(body.statements.len(), 1);
    assert!(matches!(body.statements[0].kind, StatementKind::Loop(_)));
    assert!(matches!(
        body.tail.as_deref().map(|e| &e.kind),
        Some(ExprKind::Array(_))
    ));

    let body = function_body("fn f(x: i32) -> i32 { { x = 1; } (x) }");
    assert_eq!(body.statements.len(), 1);
    assert!(
        matches!(body.statements[0].kind, StatementKind::Expression(ref e) if matches!(e.kind, ExprKind::Block(_)))
    );
    assert!(matches!(
        body.tail.as_deref().map(|e| &e.kind),
        Some(ExprKind::Path(_))
    ));

    let body = function_body("fn f(c: bool) -> i32 { if c { 1 } else { 2 } [1] }");
    assert_eq!(body.statements.len(), 1);
    assert!(matches!(
        body.tail.as_deref().map(|e| &e.kind),
        Some(ExprKind::Array(_))
    ));

    let body = function_body("fn f(c: bool) -> i32 { if c {} else if c {} else {} [1] }");
    assert_eq!(body.statements.len(), 1);
    assert!(matches!(
        body.tail.as_deref().map(|e| &e.kind),
        Some(ExprKind::Array(_))
    ));

    let body = function_body("fn f() -> i32 { loop { break; } -x }");
    assert_eq!(body.statements.len(), 1);
    assert!(matches!(body.statements[0].kind, StatementKind::Loop(_)));
    assert!(
        matches!(body.tail.as_deref().map(|e| &e.kind), Some(ExprKind::Unary { operator, .. }) if operator == "-")
    );
}

#[test]
fn block_like_expressions_outside_statement_position_are_unchanged() {
    let body = function_body("fn f(c: bool) { let a := if c { 1 } else { 2 } + 3; }");
    let StatementKind::Binding { value, .. } = &body.statements[0].kind else {
        panic!()
    };
    // The else operand keeps full-expression parsing, so `+ 3` joins it.
    let ExprKind::If { else_branch, .. } = &value.kind else {
        panic!()
    };
    assert!(
        matches!(else_branch.as_deref().map(|e| &e.kind), Some(ExprKind::Binary { operator, .. }) if operator == "+")
    );

    let body = function_body("fn f(c: bool) { foo(if c { 1 } else { 2 }); }");
    let StatementKind::Expression(e) = &body.statements[0].kind else {
        panic!()
    };
    let ExprKind::Call { arguments, .. } = &e.kind else {
        panic!()
    };
    assert!(matches!(arguments[0].kind, ExprKind::If { .. }));

    let body = function_body("fn f(c: bool) { (if c { a } else { b })[0]; }");
    let StatementKind::Expression(e) = &body.statements[0].kind else {
        panic!()
    };
    let ExprKind::Index { base, .. } = &e.kind else {
        panic!()
    };
    assert!(matches!(base.kind, ExprKind::If { .. }));

    let body = function_body("fn f(c: bool) { var x := 0; x = if c { 1 } else { 2 }; }");
    let StatementKind::Assign { value, .. } = &body.statements[1].kind else {
        panic!()
    };
    assert!(matches!(value.kind, ExprKind::If { .. }));

    let body = function_body("fn f(c: bool) -> i32 { return if c { 1 } else { 2 }; }");
    let StatementKind::Return(Some(value)) = &body.statements[0].kind else {
        panic!()
    };
    assert!(matches!(value.kind, ExprKind::If { .. }));
}

// ---- struct literals ----

fn first_binding_value(source: &str) -> memobits_syntax::Expr {
    let body = function_body(source);
    let StatementKind::Binding { value, .. } = &body.statements[0].kind else {
        panic!("expected a binding")
    };
    value.clone()
}

#[test]
fn struct_literals_keep_field_order_and_allow_trailing_commas() {
    let value = first_binding_value("fn f() { let p := Version { minor: 1, major: 0, }; }");
    let ExprKind::Struct { path, fields, .. } = &value.kind else {
        panic!("{value:?}")
    };
    assert_eq!(path, &["Version"]);
    let names: Vec<_> = fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(names, ["minor", "major"]);
    assert!(matches!(fields[0].value.kind, ExprKind::Number(_)));

    let value = first_binding_value("fn f() { let p := a::P { x: 1 + 2, y: g(3) }; }");
    let ExprKind::Struct { path, fields, .. } = &value.kind else {
        panic!()
    };
    assert_eq!(path, &["a", "P"]);
    assert!(matches!(fields[0].value.kind, ExprKind::Binary { .. }));
    assert!(matches!(fields[1].value.kind, ExprKind::Call { .. }));

    let value = first_binding_value("fn f() { let p := Empty {}; }");
    assert!(matches!(&value.kind, ExprKind::Struct { fields, .. } if fields.is_empty()));
}

#[test]
fn struct_literals_postfix_and_nest() {
    let value = first_binding_value("fn f() { let n := P { x: 1, y: 2 }.x; }");
    let ExprKind::Field { base, name } = &value.kind else {
        panic!("{value:?}")
    };
    assert_eq!(name, "x");
    assert!(matches!(base.kind, ExprKind::Struct { .. }));
}

#[test]
fn struct_literal_is_not_allowed_directly_in_an_if_condition() {
    // The `{` after the condition starts the branch block, as in Rust.
    let result = parse(SourceId(2), "fn f() { if x == P { a: 1 } { 1; } }");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|d| d.message.contains("wrap it in parentheses")),
        "{:?}",
        result.diagnostics
    );
    // An ordinary condition followed by its block is unaffected.
    let result = parse(
        SourceId(2),
        "fn f(x: i32) { if x == 1 { 1; } else if x == 2 { 2; } }",
    );
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
}

#[test]
fn parenthesised_and_delimited_struct_literals_are_fine_in_conditions() {
    for source in [
        "fn f() { if (P { a: 1 }).a == 1 { 1; } }",
        "fn f() { if g(P { a: 1 }) { 1; } }",
        "fn f() { if xs[Q { i: 0 }.i] == 1 { 1; } }",
        "fn f() { if true { let p := P { a: 1 }; } }",
        "fn f() { if true { P { a: 1 }.a; } else { Q { b: 2 }.b; } }",
    ] {
        let result = parse(SourceId(3), source);
        assert!(
            result.diagnostics.is_empty(),
            "{source}: {:?}",
            result.diagnostics
        );
    }
    let body = function_body("fn f() { if (P { a: 1 }).a == 1 { 1; } }");
    let e = body.tail.as_ref().expect("if is the block tail");
    let ExprKind::If { condition, .. } = &e.kind else {
        panic!()
    };
    let ExprKind::Binary { left, .. } = &condition.kind else {
        panic!()
    };
    let ExprKind::Field { base, .. } = &left.kind else {
        panic!()
    };
    assert!(matches!(base.kind, ExprKind::Struct { .. }));
}

#[test]
fn malformed_struct_literals_and_destructuring_have_clear_diagnostics() {
    for (source, expected) in [
        ("fn f() { let p := P { x }; }", "shorthand is not supported"),
        ("fn f() { let p := P { x: 1 y: 2 }; }", "expected '}'"),
        (
            "fn f() { let P { x: Q { y } } := p; }",
            "nested destructuring",
        ),
        ("fn f() { let P { x, .. } := p; }", "`..`"),
        ("fn f() { let P { x: 1 } := p; }", "expected identifier"),
        ("fn f() { let P { x } = p; }", "expected ':='"),
    ] {
        let result = parse(SourceId(4), source);
        assert!(
            result
                .diagnostics
                .iter()
                .any(|d| d.message.contains(expected)),
            "{source}: {:?}",
            result.diagnostics
        );
    }
}

#[test]
fn parses_positional_nested_and_wildcard_tuple_destructuring() {
    let parsed = parse(
        SourceId(42),
        "fn f() { let (first, second,) := pair; var () := empty; }",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
        panic!()
    };
    let StatementKind::TupleDestructure { elements, .. } = &body.statements[0].kind else {
        panic!("expected tuple destructuring")
    };
    assert_eq!(
        elements
            .iter()
            .map(|element| element.binding.as_str())
            .collect::<Vec<_>>(),
        ["first", "second"]
    );
    let StatementKind::TupleDestructure { elements, .. } = &body.statements[1].kind else {
        panic!("expected empty tuple destructuring")
    };
    assert!(elements.is_empty());

    let parsed = parse(SourceId(43), "fn f() { let (_, (inner, _)) := pair; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
        panic!()
    };
    let StatementKind::TupleDestructure { elements, .. } = &body.statements[0].kind else {
        panic!("expected nested tuple pattern")
    };
    assert_eq!(elements[0].binding, "_");
    let nested = elements[1].nested.as_ref().expect("nested tuple pattern");
    assert_eq!(nested[0].binding, "inner");
    assert_eq!(nested[1].binding, "_");

    for (source, expected) in [
        ("fn f() { let (one) := pair; }", "one-element tuple"),
        ("fn f() { let (one: alias, two) := pair; }", "aliases"),
    ] {
        let parsed = parse(SourceId(43), source);
        assert!(
            parsed
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains(expected)),
            "{source}: {:?}",
            parsed.diagnostics
        );
    }
}

fn first_body(source: &str) -> memobits_syntax::Block {
    let result = parse(SourceId(40), source);
    assert!(
        result.diagnostics.is_empty(),
        "{source}: {:?}",
        result.diagnostics
    );
    let ItemKind::Function { body, .. } = &result.module.items[0].kind else {
        panic!()
    };
    body.clone()
}

fn syntax_error(source: &str, text: &str) {
    let result = parse(SourceId(41), source);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|d| d.code.to_string() == "SE002" && d.message.contains(text)),
        "{source}: expected SE002 containing {text:?}, found {:?}",
        result.diagnostics
    );
}

#[test]
fn match_arms_patterns_and_optional_commas_parse() {
    use memobits_syntax::PatternKind;
    let body = first_body(
        "fn f(s: Shape) -> i32 { match s { Shape::Empty => 0, Shape::Circle(r) => { 1 } \
         Shape::Rect(w, _) => 2, _ => 3, } }",
    );
    let tail = body.tail.expect("match is the tail expression");
    let ExprKind::Match { scrutinee, arms } = &tail.kind else {
        panic!("{tail:?}")
    };
    assert!(matches!(&scrutinee.kind, ExprKind::Path(path) if path == &["s"]));
    assert_eq!(arms.len(), 4);
    let PatternKind::Variant { path, slots } = &arms[0].pattern.kind else {
        panic!()
    };
    assert_eq!(path, &["Shape", "Empty"]);
    assert!(slots.is_empty());
    let PatternKind::Variant { slots, .. } = &arms[2].pattern.kind else {
        panic!()
    };
    assert!(matches!(&slots[0].kind, PatternKind::Binding(name) if name == "w"));
    assert!(matches!(slots[1].kind, PatternKind::Wildcard));
    assert!(matches!(arms[3].pattern.kind, PatternKind::Wildcard));
    assert!(matches!(arms[1].body.kind, ExprKind::Block(_)));
}

#[test]
fn match_in_statement_position_ends_at_its_brace() {
    let body = first_body("fn f(s: Shape) { match s { _ => {} } [1, 2]; match s { _ => 1 } + 2; }");
    // Each match is a complete statement; `[1, 2]` and `+ 2` start new ones.
    assert_eq!(body.statements.len(), 4);
    assert!(matches!(
        &body.statements[0].kind,
        StatementKind::Expression(e) if matches!(e.kind, ExprKind::Match { .. })
    ));
    assert!(matches!(
        &body.statements[1].kind,
        StatementKind::Expression(e) if matches!(e.kind, ExprKind::Array(_))
    ));
}

#[test]
fn match_is_an_expression_and_nests() {
    let body = first_body(
        "fn f(a: A, b: B) -> i32 { let n := match a { A::X(v) => match b { B::Y => v, _ => 0 }, _ => 1 } + 1; n }",
    );
    let StatementKind::Binding { value, .. } = &body.statements[0].kind else {
        panic!()
    };
    assert!(
        matches!(&value.kind, ExprKind::Binary { left, .. } if matches!(left.kind, ExprKind::Match { .. }))
    );
}

#[test]
fn match_scrutinee_rejects_struct_literals_but_allows_parentheses() {
    syntax_error(
        "fn f() { match P { x: 1 } { _ => {} } }",
        "match` scrutinee",
    );
    let body = first_body("fn f() { match (P { x: 1 }).x { _ => {} } }");
    assert_eq!(body.statements.len() + usize::from(body.tail.is_some()), 1);
    // A struct literal is fine inside an arm body.
    first_body("fn f(s: S) -> P { match s { _ => P { x: 1 } } }");
}

#[test]
fn unsupported_patterns_are_gated_with_messages() {
    syntax_error("fn f(s: S) { match s { 1 => {} } }", "literal patterns");
    syntax_error("fn f(s: S) { match s { true => {} } }", "literal patterns");
    syntax_error(
        "fn f(s: S) { match s { A::B(1) => {} } }",
        "literal patterns",
    );
    syntax_error(
        "fn f(s: S) { match s { A::B(C::D(1)) => {} } }",
        "literal patterns",
    );
    syntax_error(
        "fn f(s: S) { match s { A::B(x) if x > 1 => {} _ => {} } }",
        "guards",
    );
    syntax_error(
        "fn f(s: S) { match s { A { x } => {} } }",
        "struct patterns",
    );
    syntax_error("fn f(s: S) { match s { A::B => 1 C::D => 2 } }", "','");
}

#[test]
fn divergent_statements_can_be_arm_bodies_directly() {
    let body = first_body(
        "fn f(s: S) -> i32 { loop { let n := match s { A::X => return 1, A::Y(v) => break, _ => continue }; } 0 }",
    );
    let StatementKind::Loop(inner) = &body.statements[0].kind else {
        panic!()
    };
    let StatementKind::Binding { value, .. } = &inner.statements[0].kind else {
        panic!()
    };
    let ExprKind::Match { arms, .. } = &value.kind else {
        panic!()
    };
    let kinds: Vec<_> = arms
        .iter()
        .map(|arm| match &arm.body.kind {
            ExprKind::Block(block) => match &block.statements[0].kind {
                StatementKind::Return(Some(_)) => "return",
                StatementKind::Break => "break",
                StatementKind::Continue => "continue",
                _ => "other",
            },
            _ => "expr",
        })
        .collect();
    assert_eq!(kinds, ["return", "break", "continue"]);
}

#[test]
fn associated_type_declarations_and_bindings_parse_in_interface_extensions() {
    let parsed = parse(
        SourceId(0),
        "interface Add { type Rhs; type Output; fn add(self, rhs: Rhs) -> Output; } extend Left of Add { type Rhs = Right; type Output = Result; fn add(self, rhs: Right) -> Result { Result {} } }",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let module = parsed.module;
    let ItemKind::Interface {
        associated_types, ..
    } = &module.items[0].kind
    else {
        panic!("expected interface")
    };
    assert_eq!(associated_types, &["Rhs", "Output"]);
    let ItemKind::Extension {
        associated_types, ..
    } = &module.items[1].kind
    else {
        panic!("expected interface extension")
    };
    assert_eq!(associated_types.len(), 2);
    assert_eq!(associated_types[0].name, "Rhs");
    assert_eq!(associated_types[0].ty.as_ref().unwrap().path, ["Right"]);
}

#[test]
fn parses_bitand_compound_assignment_statement() {
    let parsed = parse(SourceId(0), "fn main() { var bits: u32 = 15; bits &= 6; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
        panic!("expected function body");
    };
    let StatementKind::Assign { operator, .. } = &body.statements[1].kind else {
        panic!("expected assignment statement");
    };
    assert_eq!(operator, "&=");
}

#[test]
fn parses_bitor_compound_assignment_statement() {
    let parsed = parse(SourceId(0), "fn main() { var bits: u32 = 8; bits |= 3; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
        panic!("expected function body");
    };
    let StatementKind::Assign { operator, .. } = &body.statements[1].kind else {
        panic!("expected assignment statement");
    };
    assert_eq!(operator, "|=");
}
#[test]
fn parses_shift_left_compound_assignment_statement() {
    let parsed = parse(SourceId(0), "fn main() { var bits: u32 = 10; bits <<= 2; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
        panic!("expected function body");
    };
    let StatementKind::Assign { operator, .. } = &body.statements[1].kind else {
        panic!("expected assignment statement");
    };
    assert_eq!(operator, "<<=");
}

#[test]
fn parses_bitxor_compound_assignment_statement() {
    let parsed = parse(SourceId(0), "fn main() { var bits: u32 = 10; bits ^= 3; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
        panic!("expected function body");
    };
    let StatementKind::Assign { operator, .. } = &body.statements[1].kind else {
        panic!("expected assignment statement");
    };
    assert_eq!(operator, "^=");
}

#[test]
fn parses_shift_right_compound_assignment_statement() {
    let parsed = parse(SourceId(0), "fn main() { var bits: u32 = 10; bits >>= 2; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
        panic!("expected function body");
    };
    let StatementKind::Assign { operator, .. } = &body.statements[1].kind else {
        panic!("expected assignment statement");
    };
    assert_eq!(operator, ">>=");
}

#[test]
fn parses_shift_right_assignment_after_nested_generic_closer() {
    let parsed = parse(
        SourceId(0),
        "fn main() { var x: Box<Box<u32>> = value; x >>= 1; }",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ItemKind::Function { body, .. } = &parsed.module.items[0].kind else {
        panic!("expected function");
    };
    let StatementKind::Assign { operator, .. } = &body.statements[1].kind else {
        panic!("expected assignment");
    };
    assert_eq!(operator, ">>=");
}

#[test]
fn nested_variant_tuple_wildcard_and_binding_patterns_parse_at_any_depth() {
    use memobits_syntax::PatternKind;
    let body = first_body(
        "fn f(r: R) -> i32 { match r { Ok(Some(v)) => 1, Ok(None) => 2, Err(_) => 3, \
         A::B(C::D((x, _)), (y,), z) => 4, (Some(a), (b, c)) => 5, ((d)) => 6 } }",
    );
    let tail = body.tail.expect("match is the tail expression");
    let ExprKind::Match { arms, .. } = &tail.kind else {
        panic!("{tail:?}")
    };
    assert_eq!(arms.len(), 6);
    let PatternKind::Variant { path, slots } = &arms[0].pattern.kind else {
        panic!()
    };
    assert_eq!(path, &["Ok"]);
    let PatternKind::Variant { path, slots } = &slots[0].kind else {
        panic!()
    };
    assert_eq!(path, &["Some"]);
    assert!(matches!(&slots[0].kind, PatternKind::Binding(name) if name == "v"));
    // A bare `None` has no parentheses, so the parser reports a lone identifier.
    let PatternKind::Variant { slots, .. } = &arms[1].pattern.kind else {
        panic!()
    };
    assert!(matches!(&slots[0].kind, PatternKind::Binding(name) if name == "None"));
    let PatternKind::Variant { slots, .. } = &arms[3].pattern.kind else {
        panic!()
    };
    assert_eq!(slots.len(), 3);
    let PatternKind::Variant { slots: inner, .. } = &slots[0].kind else {
        panic!()
    };
    let PatternKind::Tuple(pair) = &inner[0].kind else {
        panic!()
    };
    assert_eq!(pair.len(), 2);
    assert!(matches!(&slots[1].kind, PatternKind::Tuple(single) if single.len() == 1));
    assert!(matches!(&slots[2].kind, PatternKind::Binding(name) if name == "z"));
    assert!(matches!(&arms[4].pattern.kind, PatternKind::Tuple(items) if items.len() == 2));
    // Redundant parentheses group a single pattern.
    assert!(matches!(&arms[5].pattern.kind, PatternKind::Binding(name) if name == "d"));
}

#[test]
fn malformed_nested_patterns_are_syntax_errors() {
    syntax_error("fn f(s: S) { match s { A::B(C::D(1)) => {} } }", "literal");
    syntax_error("fn f(s: S) { match s { A::B(()) => {} } }", "empty tuple");
    syntax_error(
        "fn f(s: S) { match s { A::B(C { x }) => {} } }",
        "struct patterns",
    );
}
