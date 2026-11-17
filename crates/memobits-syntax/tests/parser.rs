use memobits_diagnostics::SourceId;
use memobits_syntax::{lex, parse, Access, ExprKind, ItemKind, StatementKind};

#[test]
fn parses_real_project_sources() {
    for source in [
        include_str!("../../../examples/projects/numeric/src/main.mb"),
        include_str!("../../../examples/projects/numeric/src/math.mb"),
        include_str!("../../../examples/projects/enums/src/main.mb"),
    ] {
        let result = parse(SourceId(0), source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert!(!result.module.items.is_empty());
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
fn arrays_preserve_nested_types_literals_and_spans() {
    use memobits_syntax::TypeArgument;
    let source = "fn f(a: Array<Array<i32, 0>, 1_000>) { [1, 2,]; []; [f(); 03]; }";
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
        "Array<Array<i32, 0>, 1_000>"
    );
    let TypeArgument::Type(inner) = &ty.arguments[0] else {
        panic!()
    };
    assert_eq!(inner.path, ["Array"]);
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
        "Array<i32>",
        "Array<i32, -1>",
        "Array<i32, 1.0>",
        "Array<i32, n>",
        "Array<i32, 1 + 2>",
        "Array<i32, 1, 2>",
        "i32<u8, 2>",
        "Array",
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
    let body = function_body("fn f(c: Bool) -> Array<i32, 2> { if c { return [5, 6]; } [7, 8] }");
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

    let body = function_body("fn f(c: Bool) -> i32 { if c { 1 } else { 2 } [1] }");
    assert_eq!(body.statements.len(), 1);
    assert!(matches!(
        body.tail.as_deref().map(|e| &e.kind),
        Some(ExprKind::Array(_))
    ));

    let body = function_body("fn f(c: Bool) -> i32 { if c {} else if c {} else {} [1] }");
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
    let body = function_body("fn f(c: Bool) { let a := if c { 1 } else { 2 } + 3; }");
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

    let body = function_body("fn f(c: Bool) { foo(if c { 1 } else { 2 }); }");
    let StatementKind::Expression(e) = &body.statements[0].kind else {
        panic!()
    };
    let ExprKind::Call { arguments, .. } = &e.kind else {
        panic!()
    };
    assert!(matches!(arguments[0].kind, ExprKind::If { .. }));

    let body = function_body("fn f(c: Bool) { (if c { a } else { b })[0]; }");
    let StatementKind::Expression(e) = &body.statements[0].kind else {
        panic!()
    };
    let ExprKind::Index { base, .. } = &e.kind else {
        panic!()
    };
    assert!(matches!(base.kind, ExprKind::If { .. }));

    let body = function_body("fn f(c: Bool) { var x := 0; x = if c { 1 } else { 2 }; }");
    let StatementKind::Assign { value, .. } = &body.statements[1].kind else {
        panic!()
    };
    assert!(matches!(value.kind, ExprKind::If { .. }));

    let body = function_body("fn f(c: Bool) -> i32 { return if c { 1 } else { 2 }; }");
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
    let ExprKind::Struct { path, fields } = &value.kind else {
        panic!("{value:?}")
    };
    assert_eq!(path, &["Version"]);
    let names: Vec<_> = fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(names, ["minor", "major"]);
    assert!(matches!(fields[0].value.kind, ExprKind::Number(_)));

    let value = first_binding_value("fn f() { let p := a::P { x: 1 + 2, y: g(3) }; }");
    let ExprKind::Struct { path, fields } = &value.kind else {
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
    assert_eq!(slots[0].name.as_deref(), Some("w"));
    assert_eq!(slots[1].name, None);
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
        "fn f(s: S) { match s { A::B(C::D(x)) => {} } }",
        "nested patterns",
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
