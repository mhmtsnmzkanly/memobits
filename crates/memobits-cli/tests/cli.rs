use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

#[test]
fn concat_accepts_aliased_inputs_and_keeps_outer_owners_across_nested_calls() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='concat-aliases'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn byte_is(s: borrow string, offset: u32, expected: u8) -> bool {
            match s.byte_at(offset) { Some(byte) => byte == expected, None => false }
        }
        fn doubled(input: borrow string, descend: bool) -> bool {
            let joined := input.concat(input);
            if descend && !doubled(joined.borrow(), false) { return false; }
            // The callee's released region can be reused while joined is live.
            let joined_again := joined.concat("");
            joined.len() == input.len() * 2
                && byte_is(joined.borrow(), input.len(), 195)
                && byte_is(joined_again.borrow(), joined_again.len() - 1, 169)
        }
        fn main() -> bool ! Error {
            let text := "".concat("é");
            let pair := text.concat("😀");
            Ok(doubled(text.borrow(), true)
                && byte_is(text.borrow(), 1, 169)
                && pair.len() == 6
                && byte_is(pair.borrow(), 1, 169)
                && byte_is(pair.borrow(), 2, 240)
                && byte_is(pair.borrow(), 5, 128))
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "concat.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "concat.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn heap_strings_reject_unbound_results_and_conflicting_loans() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='concat'\nentry='main::main'\n",
    );
    for (body, message) in [
        (
            r#""a".concat("b").borrow();"#,
            "explicit borrow String argument to a direct internal call",
        ),
        (
            r#"var joined := "a".concat("b"); let view := joined.borrow(); joined = "c"; view.len();"#,
            "while it is borrowed",
        ),
        (
            r#"var joined := "a"; let view := joined.share(); joined = "b".concat("c"); view.len();"#,
            "while it is shared",
        ),
        (
            r#"let joined := "a".concat("b"); returns(joined).borrow();"#,
            "borrow/share conversion requires a named local",
        ),
        (
            r#"let joined := "a".concat("b"); earlier(joined, joined.len());"#,
            "BE001",
        ),
        (
            r#"let joined := "a".concat("b"); alias(joined.borrow(), joined);"#,
            "while it is borrowed",
        ),
        (
            r#"let joined := "a".concat("b"); alias(joined.borrow(), returns(joined));"#,
            "while it is borrowed",
        ),
        (
            r#"let joined := "a".concat("b"); let view := joined.borrow(); let moved := joined; view.len();"#,
            "while it is borrowed",
        ),
        (
            r#"var left := "a"; let joined := left.concat({ left = "x"; "b" });"#,
            "while it is borrowed",
        ),
    ] {
        f.write(
            "src/main.mb",
            &format!(
                "fn returns(s: string) -> string {{ s }}
                 fn earlier(s: string, size: u32) {{}}
                 fn alias(view: borrow string, s: string) {{ view.len(); }}
                 fn main() {{ {body} }}"
            ),
        );
        let result = f.run(&["run"]);
        assert!(!result.status.success(), "{body}");
        let stderr = String::from_utf8(result.stderr).unwrap();
        assert!(stderr.contains(message), "{body}: {stderr}");
    }
}

#[test]
fn string_push_str_runs_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='push-str'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn append(text: share string, suffix: borrow string) {
            text.push_str(suffix)
        }
        fn early(text: share string, stop: bool) {
            text.push_str({ if stop { return; } "wrong" });
        }
        fn main() -> bool ! Error {
            let suffix := "😀".concat("!");
            let view := suffix.borrow();
            var text := "";
            text.push_str("é");
            text.push_str("");
            append(text.share(), view);
            early(text.share(), true);
            let scalar := match text.scalar_at(2) {
                Some(value) => value == 128_512, None => false
            };
            Ok(text.len() == 7 && scalar && view.len() == 5)
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "append.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "append.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn string_push_str_rejects_aliases_and_read_only_receivers() {
    let f = Fixture::new();
    for (body, code, message) in [
        (
            r#"let text := "a"; text.push_str("b");"#,
            "TE017",
            "requires a mutable whole String",
        ),
        (
            r#"var text := "a"; let view := text.borrow(); view.push_str("b");"#,
            "TE017",
            "requires a mutable whole String",
        ),
        (
            r#"var text := "a"; text.push_str(text.borrow());"#,
            "BE005",
            "shared",
        ),
        (
            r#"var text := "a"; let view := text.borrow(); text.push_str("b"); view.len();"#,
            "BE005",
            "borrowed",
        ),
        (
            r#"var text := "a"; let view := text.share(); view.push_str("b");"#,
            "TE017",
            "direct share String parameter",
        ),
    ] {
        f.write("text.mb", &format!("fn main() {{ {body} }}"));
        let diagnostic = err(f.run(&["ownership", "text.mb"]), code);
        assert!(diagnostic.contains(message), "{body}: {diagnostic}");
    }
}

#[test]
fn share_string_replacement_preserves_caller_owned_storage() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='share-text'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn extend(text: share string, early: bool) {
            text = text.concat({ if early { return; } "😀" });
        }
        fn read_exclusive(text: share string) -> u32 { text.len() }
        fn clear(text: share string) { text = "ok"; }
        fn into_len(text: string) -> u32 { text.len() }
        fn main() -> bool ! Error {
            var text := "é";
            extend(text.share(), false);
            extend(text.share(), true);
            if read_exclusive(text.share()) != 6 { return Ok(false); }
            let last := match text.scalar_at(2) {
                Some(value) => value == 128_512, None => false
            };
            var other := "".concat("!");
            clear(other.share());
            Ok(last && other.len() == 2 && into_len(text) == 6)
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "share.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "share.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn share_string_replacement_rejects_aliases_and_conflicting_loans() {
    let f = Fixture::new();
    for (body, message) in [
        (
            "let view := text.borrow(); replace(text.share()); view.len();",
            "while it is borrowed",
        ),
        ("two(text.share(), text.share());", "already shares it"),
        (
            "let view := text.share(); replace(view);",
            "requires a direct share of a whole mutable caller local",
        ),
        (
            "forward(text.share());",
            "requires a direct share of a whole mutable caller local",
        ),
    ] {
        let forwarding = if body.starts_with("forward(") {
            "fn forward(text: share string) { replace(text.share()); }"
        } else {
            ""
        };
        f.write(
            "text.mb",
            &format!(
                r#"
            fn replace(text: share string) {{ text = text.concat("!"); }}
            {forwarding}
            fn two(left: share string, right: share string) {{ left.len(); right.len(); }}
            fn main() {{ var text := "a"; {body} }}
        "#
            ),
        );
        let result = f.run(&["ownership", "text.mb"]);
        assert!(!result.status.success(), "{body}");
        let diagnostic = String::from_utf8(result.stderr).unwrap();
        assert!(diagnostic.contains(message), "{body}: {diagnostic}");
    }
}

#[test]
fn heap_string_replacement_preserves_rhs_reads_and_handles_mixed_moves() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='concat-replacement'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn use_owner(value: string) -> u32 { value.len() }
        fn add(value: borrow string) -> string {
            let result := value.concat("😀");
            result
        }
        fn check(move_first: bool) -> bool {
            var text := "é";
            text = text.concat("!");
            text = text.concat("x");
            text = text;
            var new_text := add(text.borrow());
            if move_first { use_owner(text); }
            text = new_text;
            new_text = "ok";
            if text.len() != 8 || new_text.len() != 2 { return false; }
            text = add(text.borrow());
            let suffix_ok := match text.scalar_at(8) {
                Some(value) => value == 128_512, None => false
            };
            text = "done";
            suffix_ok && text.len() == 4
        }
        fn early() -> u32 {
            var text := "é".concat("!");
            text = text.concat({ return use_owner_before_exit(text.borrow()); "unreachable" });
            text.len()
        }
        fn use_owner_before_exit(value: borrow string) -> u32 { value.len() }
        fn main() -> bool ! Error { Ok(check(true) && check(false) && early() == 3) }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "replacement.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "replacement.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn multiple_heap_arguments_keep_order_and_can_return_an_owner() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='concat-args'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn select(first: string, order: i32, second: string, last: i32) -> string {
            if first.len() == 3 && order == 1 && last == 2 { return second; }
            first
        }
        fn main() -> u32 ! Error {
            let first := "é".concat("!");
            let second := "a".concat("😀");
            var order := 0;
            let selected := select(first, { order = 1; order }, second, {
                let scratch := "x".concat("y");
                if scratch.len() == 2 { order += 1; }
                order
            });
            Ok(selected.len())
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(u32(5))\n");
    let build = f.run(&["build", "--output", "arguments.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "arguments.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn heap_returns_chain_through_immutable_locals_and_preserve_static_paths() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='concat-returns'\nentry='main::main'\n",
    );
    f.write(
        "src/text.mb",
        r#"
        pub fn choose(early: bool) -> string {
            let joined := "é".concat("😀");
            if early { return joined; }
            "ok"
        }
        fn identity(owned: string) -> string { owned }
        pub fn forward(early: bool) -> string {
            let owned := choose(early);
            let forwarded := identity(owned);
            forwarded
        }
    "#,
    );
    f.write(
        "src/main.mb",
        r#"
        use self::text::forward;
        fn byte_is(s: borrow string, index: u32, expected: u8) -> bool {
            match s.byte_at(index) { Some(byte) => byte == expected, None => false }
        }
        fn main() -> bool ! Error {
            let first := forward(true);
            let literal := forward(false);
            let another := "a".concat("b");
            Ok(first.len() == 6 && byte_is(first.borrow(), 5, 128)
                && literal.len() == 2 && byte_is(literal.borrow(), 0, 111)
                && byte_is(another.borrow(), 0, 97))
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "returns.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "returns.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn discarded_heap_results_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='concat-discard'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn make(text: string, early: bool) -> string {
            if early { return text; }
            let result := text.concat("!");
            result
        }
        fn early_concat() -> bool {
            let first := "é".concat("!");
            first.concat({ return first.len() == 3; "unreachable" });
            false
        }
        fn main() -> bool ! Error {
            let first := "é".concat("!");
            make(first, true);
            "x".concat("😀");
            let second := "a".concat("b");
            make(second, { return Ok(early_concat()); false });
            Ok(false)
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "discard.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "discard.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn discarded_heap_call_preserves_trap_diagnostics() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='concat-discard-trap'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn make(text: string, divisor: i32) -> string {
            let quotient := 1 / divisor;
            if quotient == 0 { return "zero"; }
            text
        }
        fn main() {
            let text := "é".concat("!");
            make(text, 0);
        }
        "#,
    );
    let source = err(f.run(&["run"]), "RE007");
    assert!(source.contains("division by zero"), "{source}");
    let build = f.run(&["build", "--output", "discard-trap.wasm"]);
    assert!(build.status.success(), "{build:?}");
    assert_eq!(err(f.run(&["run", "discard-trap.wasm"]), "RE007"), source);
}

#[test]
fn immediate_heap_string_reads_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='concat-read'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn make() -> string {
            let text := "é".concat("😀");
            text
        }
        fn byte_is(value: u8?, expected: u8) -> bool {
            match value { Some(byte) => byte == expected, None => false }
        }
        fn scalar_is(value: u32?, expected: u32) -> bool {
            match value { Some(scalar) => scalar == expected, None => false }
        }
        fn early() -> bool {
            make().byte_at({ return true; 0 });
            false
        }
        fn order() -> bool {
            var step := 0;
            let result := "é".concat({ step = 1; "😀" }).scalar_at({
                if step != 1 { return false; }
                step = 2;
                2
            });
            scalar_is(result, 128_512) && step == 2
        }
        fn main() -> bool ! Error {
            Ok("é".concat("😀").len() == 6 && make().len() == 6
                && byte_is("é".concat("😀").byte_at(1), 169)
                && byte_is(make().byte_at(5), 128)
                && "é".concat("😀").is_char_boundary(2) && !make().is_char_boundary(1)
                && scalar_is("é".concat("😀").scalar_at(0), 233)
                && scalar_is(make().scalar_at(2), 128_512)
                && early() && order())
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "read.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "read.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn temporary_string_borrows_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='concat-borrow'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn make() -> string {
            let result := "a".concat("😀");
            result
        }
        fn inspect(first: borrow string, second: borrow string, order: i32) -> bool {
            first.len() == 3 && second.len() == 5 && order == 2
        }
        fn early() -> bool {
            let unused := "unused";
            inspect(make().borrow(), { return true; unused.borrow() }, 0)
        }
        fn main() -> bool ! Error {
            var order := 0;
            let read := inspect("é".concat({ order = 1; "!" }).borrow(),
                make().borrow(), {
                    if order != 1 { return Ok(false); }
                    order = 2;
                    order
                });
            Ok(read && early())
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "borrow.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "borrow.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn temporary_string_borrows_require_an_explicit_direct_argument() {
    let f = Fixture::new();
    for (body, message) in [
        (
            "let view := make().borrow(); view.len();",
            "requires a named local",
        ),
        ("inspect(make());", "explicit .borrow()"),
        ("inspect({ make().borrow() });", "requires a named local"),
        (
            "let indirect := inspect; indirect(make().borrow());",
            "requires a named local",
        ),
        ("mutate(make().share());", "requires a named local"),
    ] {
        f.write(
            "text.mb",
            &format!(
                r#"fn make() -> string {{ let result := "é".concat("!"); result }}
                   fn inspect(value: borrow string) {{ value.len(); }}
                   fn mutate(value: share string) {{ value.len(); }}
                   fn main() {{ {body} }}"#,
            ),
        );
        let diagnostic = err(f.run(&["ownership", "text.mb"]), "TE017");
        assert!(diagnostic.contains(message), "{body}: {diagnostic}");
    }
}

#[test]
fn temporary_owned_string_arguments_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='concat-owned-argument'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn make(ordered: bool) -> string {
            let text := "a".concat("😀");
            if ordered { return text; }
            "wrong order"
        }
        fn select(first: string, view: borrow string, second: string, last: i32) -> string {
            if first.len() == 3 && view.len() == 2 && last == 2 { return second; }
            first
        }
        fn early() -> bool {
            select(make(true), "v".concat("w").borrow(), "a".concat("b"), {
                return true;
                0
            });
            false
        }
        fn main() -> bool ! Error {
            var order := 0;
            let result := select("é".concat({ order = 1; "!" }),
                "v".concat("w").borrow(), make(order == 1), {
                    order += 1;
                    order
                });
            Ok(result.len() == 5 && order == 2 && early())
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "owned-argument.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "owned-argument.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn heap_returns_reject_nested_temporaries() {
    let f = Fixture::new();
    for body in [
        "take({ make() });",
        "let indirect := take; indirect(make());",
    ] {
        f.write(
            "text.mb",
            &format!(
                r#"fn make() -> string {{ let result := "é".concat("!"); result }}
               fn take(value: string) {{ value.len(); }}
               fn main() {{ {body} }}"#,
            ),
        );
        let diagnostic = err(f.run(&["ownership", "text.mb"]), "TE018");
        assert!(
            diagnostic.contains("must be assigned directly to a whole String local"),
            "{body}: {diagnostic}"
        );
    }
}

#[test]
fn owned_heap_arguments_forward_and_leave_literal_only_calls_available() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='concat-calls'\nentry='main::main'\n",
    );
    f.write(
        "src/text.mb",
        r#"
        pub fn consume(early: bool, value: string) -> u32 {
            if early { return value.len(); }
            let moved := value;
            moved.len()
        }
        pub fn forward(early: bool, value: string) -> u32 {
            consume(early, value)
        }
    "#,
    );
    f.write(
        "src/main.mb",
        r#"
        use self::text::forward;
        fn literal_echo(value: string, extra: u32) -> string { value }
        fn main() -> u32 ! Error {
            let first := "é".concat("!");
            let second := "a".concat("😀");
            let echoed := literal_echo("ok", 0);
            Ok(forward(true, first) + forward(false, second) + forward(false, echoed))
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(u32(10))\n");
    let build = f.run(&["build", "--output", "calls.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "calls.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn concat_moves_across_nested_scopes_release_once_on_either_branch() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='concat-moves'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn first_is(value: borrow string, expected: u8) -> bool {
            match value.byte_at(0) { Some(byte) => byte == expected, None => false }
        }
        fn check(move_inward: bool) -> bool {
            let joined := "a".concat("b");
            let size := if move_inward {
                let inner := joined;
                { let moved := inner; moved.len() }
            } else {
                joined.len()
            };
            let first := "x".concat("y");
            let second := "m".concat("n");
            size == 2 && first_is(first.borrow(), 120) && first_is(second.borrow(), 109)
        }
        fn main() -> bool ! Error {
            Ok(check(true) && check(false) && check(true))
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "moves.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "moves.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn concat_move_on_one_branch_invalidates_the_original_at_the_join() {
    let f = Fixture::new();
    f.write(
        "text.mb",
        r#"fn main(flag: bool) -> u32 {
        let joined := "é".concat("😀");
        if flag { let moved := joined; moved.len(); }
        joined.len()
    }"#,
    );
    let diagnostic = err(f.run(&["ownership", "text.mb"]), "BE001");
    assert!(diagnostic.contains("on some paths"), "{diagnostic}");
}

#[test]
fn string_scope_exits_preserve_values_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='text'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn choose(outer: string, early: bool) -> string {
            var step := 0;
            loop {
                let outer := "é";
                if early { return outer; }
                step += 1;
                if step == 1 { continue; }
                break;
            }
            { let moved := outer; moved }
        }
        fn main() -> u32 ! Error {
            Ok(choose("outer", true).len() + choose("outer", false).len())
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(u32(7))\n");
    let build = f.run(&["build", "--output", "scope.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "scope.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn list_replacement_runs_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='replace-list'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn rebuild(old: borrow List<u32>) -> List<u32> {
            var result: List<u32> = [];
            result.push(0);
            let previous := match old.get(0) { Some(value) => value, None => 0 };
            result.push(previous + old.len());
            result
        }
        fn consume(items: List<u32>) -> u32 { items.len() }
        fn pass(items: List<u32>) -> List<u32> { items }
        fn check(move_old: bool) -> bool {
            var items: List<u32> = [];
            items.push(40);
            items = rebuild(items.borrow());
            items = items;
            items = pass(items);
            let old_ok := match items.get(1) { Some(value) => value == 41, None => false };
            var next: List<u32> = [];
            next.push(99);
            if move_old { consume(items); }
            items = next;
            let moved_ok := match items.get(0) { Some(value) => value == 99, None => false };
            items = [];
            old_ok && moved_ok && items.len() == 0
        }
        fn early() -> bool {
            var items: List<u8> = [];
            items.push(255);
            items = { return items.len() == 1; [] };
            false
        }
        fn main() -> bool ! Error { Ok(check(false) && check(true) && early()) }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "replace.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "replace.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn list_replacement_rejects_live_loans_and_unavailable_sources() {
    let f = Fixture::new();
    for (body, code) in [
        (
            "let held := items.borrow(); items = []; held.len();",
            "BE005",
        ),
        (
            "let held := items.share(); items = []; held.len();",
            "BE005",
        ),
        (
            "let held := items.borrow(); items = items; held.len();",
            "BE005",
        ),
        ("let moved := items; items = items;", "BE001"),
        ("let fixed: List<u8> = []; fixed = [];", "TE004"),
    ] {
        f.write(
            "list.mb",
            &format!("use alloc::List; fn main() {{ var items: List<u8> = []; {body} }}"),
        );
        err(f.run(&["ownership", "list.mb"]), code);
    }
}

#[test]
fn owned_list_returns_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='list-return'\nentry='main::main'\n",
    );
    f.write("src/main.mb", r#"
        use alloc::List; fn bytes(empty: bool) -> List<u8> {
            var result: List<u8> = [];
            if empty { return result; }
            result.push(255);
            result
        }
        fn grown() -> List<u32> {
            var result: List<u32> = [];
            loop {
                result.push(result.len() + 100);
                if result.len() == 128 { break; }
            }
            result
        }
        fn forward(items: List<u32>, marker: u32) -> List<u32> { items }
        fn main() -> bool ! Error {
            let empty := bytes(true);
            let byte_list := bytes(false);
            let original := grown();
            var words := forward(original, 7);
            words.push(4_294_967_295);
            let first := match byte_list.get(0) { Some(value) => value == 255, None => false };
            let grown := match words.get(127) { Some(value) => value == 227, None => false };
            let last := match words.get(128) { Some(value) => value == 4_294_967_295, None => false };
            Ok(empty.len() == 0 && first && grown && last && words.len() == 129)
        }
    "#);
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "return-list.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "return-list.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn discarded_list_returns_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='list-discard'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn make_bytes(log: share List<u8>, empty: bool) -> List<u8> {
            log.push(7);
            var result: List<u8> = [];
            if empty { return result; }
            result.push(255);
            result
        }
        fn make_words() -> List<u32> {
            var result: List<u32> = [];
            result.push(4_294_967_295);
            result
        }
        fn forward(items: List<u32>, log: share List<u8>) -> List<u32> {
            log.push(9);
            items
        }
        fn check_early_exit() -> bool {
            let staged := make_words();
            var log: List<u8> = [];
            forward(staged, { return log.len() == 0; log.share() });
            false
        }
        fn main() -> bool ! Error {
            var log: List<u8> = [];
            make_bytes(log.share(), true);
            make_bytes(log.share(), false);
            let words := make_words();
            forward(words, log.share());
            make_words();
            let last := match log.get(2) { Some(value) => value == 9, None => false };
            Ok(log.len() == 3 && last && check_early_exit())
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "discard-list.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "discard-list.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn collection_contains_runs_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='contains'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; type Rows { flags: array<bool, 2> }
        fn make(log: share List<u8>) -> List<u32> {
            log.push(1);
            var words: List<u32> = [];
            words.push(4_294_967_295);
            words
        }
        fn reads(bytes: borrow array<u8, 2>, words: share List<u32>) -> bool {
            bytes.contains(bytes[1]) && words.contains(4_294_967_295)
        }
        fn main() -> bool ! Error {
            var log: List<u8> = [];
            let empty := !log.contains({ log.len(); 0 });
            let found := make(log.share()).contains({
                if log.len() != 1 { return Ok(false); }
                log.push(2);
                4_294_967_295
            });
            var early := false;
            loop {
                make(log.share()).contains({ early = true; break; });
            }
            let mutating_after_read := log.contains(2) && !log.contains(3);
            log.clear();
            let cleared := !log.contains(2);
            let bytes: array<u8, 2> = [0, 255];
            var words := make(log.share());
            let borrowed := reads(bytes.borrow(), words.share());
            words.clear();
            let rows := Rows { flags: [false, true] };
            let nested: array<array<i8, 2>, 1> = [[-2, 3]];
            let no_values: array<i32, 0> = [];
            let wide: array<u64, 1> = [4_294_967_296];
            let floats: array<f32, 2> = [0.0, 1.0];
            let zero: f32 = 0.0;
            let nan := zero / zero;
            let doubles: array<f64, 1> = [0.0];
            Ok(empty && found && early && mutating_after_read && cleared && borrowed
                && rows.flags.contains(true) && nested[0].contains(-2)
                && !no_values.contains(0) && wide.contains(4_294_967_296)
                && !wide.contains(0) && floats.contains(-0.0) && !floats.contains(nan)
                && doubles.contains(-0.0) && [1, 2].contains(2))
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "contains.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "contains.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn collection_index_of_runs_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='index-of'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; type Flags { values: array<bool, 2> }

        fn at(result: u32?, expected: u32) -> bool {
            match result { Some(index) => index == expected, None => false }
        }
        fn missing(result: u32?) -> bool {
            match result { Some(_) => false, None => true }
        }
        fn make(log: share List<u8>) -> List<u32> {
            log.push(1);
            var words: List<u32> = [];
            words.push(7);
            words.push(4_294_967_295);
            words.push(4_294_967_295);
            words
        }
        fn reads(bytes: borrow array<u8, 3>, words: share List<u32>) -> bool {
            at(bytes.index_of(bytes[2]), 0) && at(words.index_of(4_294_967_295), 1)
        }
        fn main() -> bool ! Error {
            var log: List<u8> = [];
            var evaluations: u32 = 0;
            let empty := missing(log.index_of({ evaluations = evaluations + 1; 1 }))
                && evaluations == 1;
            let found := make(log.share()).index_of({
                if log.len() != 1 { return Ok(false); }
                log.push(2);
                4_294_967_295
            });
            loop {
                make(log.share()).index_of({ break; });
            }
            let order := log.len() == 3 && at(log.index_of(2), 1);
            log.clear();
            let cleared := missing(log.index_of(2));
            let bytes: array<u8, 3> = [255, 0, 255];
            var words := make(log.share());
            let borrowed := reads(bytes.borrow(), words.share());
            let flags := Flags { values: [false, true] };
            let rows: array<array<i8, 2>, 1> = [[-2, 3]];
            let empty_array: array<i32, 0> = [];
            let wide: array<u64, 2> = [0, 4_294_967_296];
            let floats: array<f32, 2> = [1.0, 0.0];
            let zero: f32 = 0.0;
            let nan := zero / zero;
            let doubles: array<f64, 1> = [0.0];
            Ok(empty && at(found, 1) && order && cleared && borrowed
                && at(flags.values.index_of(true), 1) && at(rows[0].index_of(-2), 0)
                && missing(empty_array.index_of(0)) && at(wide.index_of(4_294_967_296), 1)
                && at(floats.index_of(-0.0), 1) && missing(floats.index_of(nan))
                && at(doubles.index_of(-0.0), 0) && at([1, 2].index_of(2), 1))
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "index-of.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "index-of.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn collection_search_checks_types_and_preserves_the_receiver_loan() {
    let f = Fixture::new();
    for (body, code) in [
        ("let a: array<u8, 1> = [1]; a.contains(true);", "TE002"),
        ("let a: array<u8, 1> = [1]; a.contains();", "TE010"),
        ("let a: array<u8, 1> = [1]; a.contains(1, 2);", "TE010"),
        ("let a := [[1]]; a.contains([1]);", "TE017"),
        ("let a := \"text\"; a.contains(1);", "TE017"),
        ("let a: List<u32> = []; a.contains(true);", "TE002"),
        (
            "var a: List<u8> = []; a.contains({ a.push(1); 1 });",
            "BE005",
        ),
        (
            "let a: List<u8> = []; a.contains({ let moved := a; 1 });",
            "BE005",
        ),
        ("var a := [1]; a.contains({ a[0] = 2; 1 });", "BE005"),
        ("let a := [1]; a.contains({ let moved := a; 1 });", "BE005"),
    ] {
        for method in ["contains", "index_of"] {
            let body = body.replace(".contains(", &format!(".{method}("));
            f.write("search.mb", &format!("fn main() {{ {body} }}"));
            err(f.run(&["ownership", "search.mb"]), code);
        }
    }
}

#[test]
fn temporary_list_reads_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='list-temporary-read'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn bytes(log: share List<u8>) -> List<u8> {
            log.push(1);
            var items: List<u8> = [];
            items.push(255);
            items
        }
        fn words() -> List<u32> {
            var items: List<u32> = [];
            items.push(4_294_967_295);
            items
        }
        fn main() -> bool ! Error {
            var log: List<u8> = [];
            let length := bytes(log.share()).len();
            let byte := bytes(log.share()).get({
                if log.len() != 2 { return Ok(false); }
                log.push(2);
                0
            });
            let present := match byte { Some(value) => value == 255, None => false };
            let word := match words().get(0) {
                Some(value) => value == 4_294_967_295,
                None => false
            };
            let missing := match bytes(log.share()).get(4_294_967_295) {
                Some(_) => false,
                None => true
            };
            let final_entry := match log.get(2) { Some(value) => value == 2, None => false };
            Ok(length == 1 && words().len() == 1 && present && word && missing && final_entry && log.len() == 4)
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "list-read.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "list-read.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn temporary_list_borrows_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='list-temporary-borrow'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn bytes(log: share List<u8>) -> List<u8> {
            log.push(1);
            var items: List<u8> = [];
            items.push(255);
            items
        }
        fn words(log: share List<u8>) -> List<u32> {
            log.push(2);
            var items: List<u32> = [];
            items.push(log.len() + 1000);
            items
        }
        fn inspect(first: borrow List<u8>, second: borrow List<u32>, order: u32) -> bool {
            let byte_ok := match first.get(0) { Some(value) => value == 255, None => false };
            let word_ok := match second.get(0) { Some(value) => value == 1002, None => false };
            byte_ok && word_ok && order == 3
        }
        fn early() -> bool {
            var log: List<u8> = [];
            inspect(bytes(log.share()).borrow(), words(log.share()).borrow(), {
                return log.len() == 2;
            })
        }
        fn main() -> bool ! Error {
            var log: List<u8> = [];
            let inspected := inspect(bytes(log.share()).borrow(), words(log.share()).borrow(), {
                log.push(3);
                log.len()
            });
            Ok(inspected && early())
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "list-borrow.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "list-borrow.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn temporary_list_borrows_require_an_explicit_direct_argument() {
    let f = Fixture::new();
    for (body, code, message) in [
        (
            "let view := make().borrow(); view.len();",
            "TE017",
            "named local owner",
        ),
        ("inspect(make());", "TE017", "explicit .borrow()"),
        (
            "inspect({ make().borrow() });",
            "TE017",
            "named local owner",
        ),
        (
            "inspect(({ make() }).borrow());",
            "TE017",
            "named local owner",
        ),
        (
            "let indirect := inspect; indirect(make().borrow());",
            "TE017",
            "named local owner",
        ),
        (
            "let indirect := make; inspect(indirect().borrow());",
            "TE017",
            "named local owner",
        ),
        ("mutate(make().share());", "TE017", "named local owner"),
        ("inspect(make().share());", "TE017", "named local owner"),
        (
            "inspect_words(make().borrow());",
            "TE002",
            "expected borrow List<u32>",
        ),
    ] {
        f.write(
            "list.mb",
            &format!(
                r#"use alloc::List; fn make() -> List<u8> {{ let items: List<u8> = []; items }}
                   fn inspect(items: borrow List<u8>) {{ items.len(); }}
                   fn inspect_words(items: borrow List<u32>) {{ items.len(); }}
                   fn mutate(items: share List<u8>) {{ items.clear(); }}
                   fn main() {{ {body} }}"#,
            ),
        );
        let diagnostic = err(f.run(&["ownership", "list.mb"]), code);
        assert!(diagnostic.contains(message), "{body}: {diagnostic}");
    }
}

#[test]
fn list_returns_keep_temporary_and_abi_gates() {
    let f = Fixture::new();
    for (body, code, message) in [
        (
            "{ make() };",
            "TE018",
            "assigned directly to a whole List local",
        ),
        ("({ make() }).len();", "TE017", "direct internal List call"),
        ("({ make() }).get(0);", "TE017", "direct internal List call"),
        (
            "let indirect := make; indirect().get(0);",
            "TE017",
            "direct internal List call",
        ),
        ("make().borrow();", "TE017", "named local owner"),
        (
            "let indirect := make; let result := indirect();",
            "TE018",
            "direct internal call",
        ),
        (
            "let indirect := make; indirect();",
            "TE018",
            "direct internal call",
        ),
    ] {
        f.write(
            "list.mb",
            &format!(
                "use alloc::List; fn make() -> List<u8> {{ let items: List<u8> = []; items }} fn main() {{ {body} }}"
            ),
        );
        let diagnostic = err(f.run(&["ownership", "list.mb"]), code);
        assert!(diagnostic.contains(message), "{body}: {diagnostic}");
    }
    f.write("list.mb", "use alloc::List; fn make() -> List<u8> { let items: List<u8> = []; items } fn forward() -> List<u8> { make() }");
    err(f.run(&["ownership", "list.mb"]), "TE018");

    f.write(
        "project.toml",
        "[package]\nname='list-return-abi'\nentry='main::main'\n[export]\nmake='main::make'\n",
    );
    f.write(
        "src/main.mb",
        "use alloc::List; pub fn make() -> List<u8> { let items: List<u8> = []; items } fn main() {}",
    );
    let diagnostic = err(f.run(&["build", "--lib"]), "LE900");
    assert!(
        diagnostic.contains("external List ABI is not defined"),
        "{diagnostic}"
    );
}

#[test]
fn owned_list_arguments_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='owned-list'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn finish(words: List<u32>) -> bool {
            match words.get(1) { Some(word) => word == 100, None => false }
        }
        fn take(bytes: List<u8>, proceed: bool, var words: List<u32>) -> bool {
            if !proceed { return false; }
            words.push(100);
            let valid := match bytes.get(0) { Some(byte) => byte == 255, None => false };
            valid && finish(words)
        }
        fn make_bytes(log: share List<u8>) -> List<u8> {
            log.push(1);
            var bytes: List<u8> = [];
            bytes.push(255);
            bytes
        }
        fn make_words(log: borrow List<u8>) -> List<u32> {
            var words: List<u32> = [];
            if log.len() != 2 { return words; }
            words.push(99);
            words
        }
        fn run_temporary(skip: bool) -> bool {
            var log: List<u8> = [];
            let check := take(make_bytes(log.share()), {
                if skip { return log.len() == 1; }
                if log.len() != 1 { return false; }
                log.push(2);
                true
            }, make_words(log.borrow()));
            check && log.len() == 2
        }
        fn run(skip: bool) -> bool {
            var bytes: List<u8> = [];
            bytes.push(255);
            var words: List<u32> = [];
            words.push(99);
            var evaluations := 0;
            let check := take(bytes, {
                if skip { return words.len() == 1; }
                evaluations += 1;
                true
            }, words);
            check && evaluations == 1
        }
        fn main() -> bool ! Error { Ok(run(false) && run(true) && run_temporary(false) && run_temporary(true)) }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "owned.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "owned.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn owned_list_arguments_keep_move_loan_and_abi_gates() {
    let f = Fixture::new();
    for (body, code) in [
        (
            "let view := items.borrow(); take(items, 0); view.len();",
            "BE005",
        ),
        ("take(items, items.len());", "BE001"),
        ("let indirect := take; indirect(items, 0);", "TE017"),
        ("take([], 0);", "TE017"),
        ("take({ items }, 0);", "TE017"),
        ("take({ make() }, 0);", "TE017"),
        ("let indirect := take; indirect(make(), 0);", "TE017"),
        ("let indirect := make; take(indirect(), 0);", "TE017"),
        ("take(make_words(), 0);", "TE002"),
    ] {
        f.write(
            "list.mb",
            &format!("use alloc::List; fn make() -> List<u8> {{ let items: List<u8> = []; items }} fn make_words() -> List<u32> {{ let items: List<u32> = []; items }} fn take(items: List<u8>, later: u32) {{}} fn main() {{ let items: List<u8> = []; {body} }}"),
        );
        err(f.run(&["ownership", "list.mb"]), code);
    }
    f.write(
        "project.toml",
        "[package]\nname='owned-list-abi'\nentry='main::main'\n[export]\ntake='main::take'\n",
    );
    f.write(
        "src/main.mb",
        "use alloc::List; pub fn take(items: List<u8>) { items.len(); } fn main() {}",
    );
    let diagnostic = err(f.run(&["build", "--lib"]), "LE900");
    assert!(
        diagnostic.contains("external List ABI is not defined"),
        "{diagnostic}"
    );
}

#[test]
fn shared_list_push_updates_caller_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='list-share'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn add(bytes: share List<u8>, words: share List<u32>) {
            bytes.push(255);
            let held := words.borrow();
            let value := held.len() + 1000;
            words.push(value);
        }
        fn last(words: share List<u32>) -> u32? {
            words.get(words.len() - 1)
        }
        fn main() -> bool ! Error {
            var bytes: List<u8> = [];
            var words: List<u32> = [];
            var index: u32 = 0;
            loop {
                add(bytes.share(), words.share());
                index += 1;
                if index == 150 { break; }
            }
            let word := match last(words.share()) { Some(value) => value == 1149, None => false };
            let moved := words;
            let first := match moved.get(0) { Some(value) => value == 1000, None => false };
            let byte := match bytes.get(149) { Some(value) => value == 255, None => false };
            Ok(word && first && byte && bytes.len() == 150 && moved.len() == 150)
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "shared.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "shared.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn shared_list_replacement_runs_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='share-list-replacement'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn fresh(previous: borrow List<u32>) -> List<u32> {
            var result: List<u32> = [];
            result.push(0);
            let old := match previous.get(0) { Some(value) => value, None => 0 };
            result.push(old + 1);
            result
        }
        fn rebuild(items: share List<u32>, early: bool) {
            items = { if early { return; } fresh(items.borrow()) };
        }
        fn install(items: share List<u8>, replacement: List<u8>) { items = replacement; }
        fn clear(items: share List<u8>) { items = []; }
        fn main() -> bool ! Error {
            var words: List<u32> = [];
            words.push(40);
            rebuild(words.share(), true);
            let untouched := words.len() == 1;
            rebuild(words.share(), false);
            let moved := words;
            let last := match moved.get(1) { Some(value) => value == 41, None => false };
            var bytes: List<u8> = [];
            bytes.push(7);
            var next: List<u8> = [];
            next.push(255);
            install(bytes.share(), next);
            let byte := match bytes.get(0) { Some(value) => value == 255, None => false };
            clear(bytes.share());
            Ok(untouched && last && byte && bytes.len() == 0)
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "replace-share.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "replace-share.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn list_clear_runs_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='list-clear'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn reset(words: share List<u32>) { words.clear() }
        fn main() -> bool ! Error {
            var bytes: List<u8> = [];
            bytes.clear();
            bytes.push(255);
            bytes.push(42);
            var handle := bytes.share();
            let preview := handle.borrow();
            let before := preview.len();
            handle.clear();
            let empty := match bytes.get(0) { None => true, Some(_) => false };
            bytes.push(7);
            let new_byte := match bytes.pop() { Some(value) => value == 7, None => false };
            var words: List<u32> = [];
            words.push(4_294_967_295);
            reset(words.share());
            let word_empty := words.len() == 0;
            words.push(17);
            words.clear();
            Ok(before == 2 && empty && new_byte && word_empty && words.len() == 0)
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "clear.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "clear.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn list_clear_rejects_read_only_and_conflicting_receivers() {
    let f = Fixture::new();
    for (body, code) in [
        ("let frozen: List<u8> = []; frozen.clear();", "TE017"),
        ("let handle := items.share(); handle.clear();", "TE017"),
        ("var handle := items.borrow(); handle.clear();", "TE017"),
        ("items.clear(1);", "TE010"),
        ("let moved := items; items.clear();", "BE001"),
        (
            "let held := items.borrow(); items.clear(); held.len();",
            "BE005",
        ),
        (
            "var handle := items.share(); let held := handle.borrow(); handle.clear(); held.len();",
            "BE005",
        ),
        (
            "var handle := items.share(); let moved := items; handle.clear();",
            "BE005",
        ),
    ] {
        f.write(
            "list.mb",
            &format!("use alloc::List; fn main() {{ var items: List<u8> = []; {body} }}"),
        );
        err(f.run(&["ownership", "list.mb"]), code);
    }
}

#[test]
fn list_pop_runs_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='list-pop'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn take(items: share List<u32>) -> u32? { items.pop() }
        fn main() -> bool ! Error {
            var bytes: List<u8> = [];
            let empty := match bytes.pop() { None => true, Some(_) => false };
            bytes.push(255);
            bytes.push(42);
            var handle := bytes.share();
            let last := match handle.pop() { Some(v) => v == 42, None => false };
            let first := match bytes.pop() { Some(v) => v == 255, None => false };
            var words: List<u32> = [];
            words.push(9);
            words.push(4_294_967_295);
            let high := match take(words.share()) { Some(v) => v == 4_294_967_295, None => false };
            let remaining := match words.get(0) { Some(v) => v == 9, None => false };
            let removed := match words.get(1) { None => true, Some(_) => false };
            Ok(empty && last && first && bytes.len() == 0 && high && remaining && removed)
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "pop.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "pop.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn list_pop_rejects_read_only_and_borrowed_receivers() {
    let f = Fixture::new();
    for (body, code) in [
        ("let frozen: List<u8> = []; frozen.pop();", "TE017"),
        ("let handle := items.share(); handle.pop();", "TE017"),
        ("var handle := items.borrow(); handle.pop();", "TE017"),
        (
            "let held := items.borrow(); items.pop(); held.len();",
            "BE005",
        ),
        (
            "var handle := items.share(); let held := handle.borrow(); handle.pop(); held.len();",
            "BE005",
        ),
        ("let moved := items; items.pop();", "BE001"),
        (
            "var handle := items.share(); let moved := items; handle.pop();",
            "BE005",
        ),
        (
            "var handle := items.share(); let moved := items; handle.push(1);",
            "BE005",
        ),
    ] {
        f.write(
            "list.mb",
            &format!("use alloc::List; fn main() {{ var items: List<u8> = []; {body} }}"),
        );
        err(f.run(&["ownership", "list.mb"]), code);
    }
}

#[test]
fn stored_list_share_updates_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='list-share-local'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn rebuild(previous: borrow List<u32>) -> List<u32> {
            var next: List<u32> = [];
            next.push(0);
            let old := match previous.get(0) { Some(value) => value, None => 0 };
            next.push(old + 1);
            next
        }
        fn check(early: bool) -> bool {
            var items: List<u32> = [];
            items.push(40);
            var handle := items.share();
            handle = { if early { return handle.len() == 1; } rebuild(handle.borrow()) };
            let preview := handle.borrow();
            let next := preview.len() + 40;
            handle.push(next);
            let moved := items;
            let old_ok := match moved.get(1) { Some(value) => value == 41, None => false };
            let pushed := match moved.get(2) { Some(value) => value == 42, None => false };
            old_ok && pushed
        }
        fn main() -> bool ! Error {
            var bytes: List<u8> = [];
            bytes.push(7);
            var next: List<u8> = [];
            next.push(255);
            var handle := bytes.share();
            handle = next;
            handle.push(128);
            let appended := match handle.get(1) { Some(value) => value == 128, None => false };
            let found := match handle.get(0) { Some(value) => value == 255, None => false };
            handle = [];
            Ok(found && appended && bytes.len() == 0 && check(false) && check(true))
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "stored-share.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "stored-share.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn list_shares_reject_conflicts_and_immutable_handle_replacement() {
    let f = Fixture::new();
    for (source, code) in [
        (
            r#"use alloc::List; fn add(view: share List<u8>) { view.push(1); }
             fn main() { var items: List<u8> = []; let view := items.borrow();
                         add(items.share()); view.len(); }"#,
            "BE005",
        ),
        (
            r#"use alloc::List; fn both(left: share List<u8>, right: share List<u8>) {
                  left.push(1); right.push(2);
             }
             fn main() { var items: List<u8> = []; both(items.share(), items.share()); }"#,
            "BE005",
        ),
        (
            r#"use alloc::List; fn add(view: share List<u8>) {
                  let held := view.borrow(); view.push(1); held.len();
             }
             fn main() {}"#,
            "BE005",
        ),
        (
            r#"use alloc::List; fn reset(view: share List<u8>) {
                  let held := view.borrow(); view = []; held.len();
               } fn main() {}"#,
            "BE005",
        ),
        (
            r#"use alloc::List; fn main() { var items: List<u8> = []; var handle := items.share();
                         let held := handle.borrow(); handle = []; held.len(); }"#,
            "BE005",
        ),
        (
            r#"use alloc::List; fn reset(view: share List<u8>) { let alias := view; alias = []; } fn main() {}"#,
            "TE004",
        ),
        (
            r#"use alloc::List; fn main() { var items: List<u8> = []; var alias := items.share();
                         let held := alias.borrow(); alias.push(1); held.len(); }"#,
            "BE005",
        ),
        (
            r#"use alloc::List; fn main() { var items: List<u8> = []; var alias := items.borrow(); alias.push(1); }"#,
            "TE017",
        ),
        (
            r#"use alloc::List; fn main() { var items: List<u8> = []; let alias := items.share(); alias.push(1); }"#,
            "TE017",
        ),
    ] {
        f.write("list.mb", source);
        err(f.run(&["ownership", "list.mb"]), code);
    }

    f.write(
        "project.toml",
        "[package]\nname='list-share-abi'\nentry='main::main'\n[export]\nadd='main::add'\n",
    );
    f.write(
        "src/main.mb",
        "use alloc::List; pub fn add(items: share List<u8>) { items.push(1); } fn main() {}",
    );
    let diagnostic = err(f.run(&["build", "--lib"]), "LE900");
    assert!(
        diagnostic.contains("external List ABI is not defined"),
        "{diagnostic}"
    );
}

#[test]
fn borrowed_list_reads_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='list-borrows'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn word_at(items: borrow List<u32>, index: u32) -> u32? {
            if index < items.len() { return items.get(index); }
            None
        }
        fn byte_at(items: borrow List<u8>, index: u32) -> u8? {
            if index < items.len() { return items.get(index); }
            None
        }
        fn word_is(value: u32?, expected: u32) -> bool {
            match value { Some(word) => word == expected, None => false }
        }
        fn main() -> bool ! Error {
            var words: List<u32> = [];
            var index: u32 = 0;
            loop {
                words.push(index + 10);
                index += 1;
                if index == 100 { break; }
            }
            let held := words.borrow();
            let before := held.len() == 100 && word_is(word_at(held, 99), 109);
            words.push(4_294_967_295);
            let moved := words;
            var bytes: List<u8> = [];
            bytes.push(255);
            let byte_ok := match byte_at(bytes.borrow(), 0) {
                Some(byte) => byte == 255, None => false
            };
            let view := moved.borrow();
            let absent := match view.get(4_294_967_295) {
                Some(_) => false, None => true
            };
            Ok(before && byte_ok && absent && word_is(word_at(moved.borrow(), 100), 4_294_967_295))
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "borrow.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "borrow.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn list_borrow_conflicts_and_call_boundaries_are_checked() {
    let f = Fixture::new();
    for (body, code, message) in [
        (
            "let held := items.borrow(); items.push(1); held.len();",
            "BE005",
            "while it is borrowed",
        ),
        (
            "let held := items.borrow(); held.get({ items.push(1); 0 });",
            "BE005",
            "while it is borrowed",
        ),
        (
            "let held := items.borrow(); let moved := items; held.get(0);",
            "BE005",
            "while it is borrowed",
        ),
        ("inspect(items);", "TE017", "explicit .borrow()"),
        (
            "let indirect := inspect; indirect(items.borrow());",
            "TE017",
            "direct internal call",
        ),
        (
            "let fixed: List<u8> = []; fixed.share();",
            "TE017",
            "requires a mutable local owner",
        ),
        (
            "let view: (borrow List<u8>)? = Some(items.borrow());",
            "TE017",
            "cannot be stored in Option",
        ),
        (
            "let dangling := { var inner: List<u8> = []; inner.push(5); inner.borrow() }; dangling.len();",
            "TE017",
            "reference-valued block results",
        ),
    ] {
        f.write("list.mb", &format!(
            "use alloc::List; fn inspect(view: borrow List<u8>) {{ view.len(); }} fn main() {{ var items: List<u8> = []; {body} }}"
        ));
        let diagnostic = err(f.run(&["ownership", "list.mb"]), code);
        assert!(diagnostic.contains(message), "{body}: {diagnostic}");
    }

    f.write(
        "project.toml",
        "[package]\nname='list-borrow-abi'\nentry='main::main'\n[export]\ninspect='main::inspect'\n",
    );
    f.write(
        "src/main.mb",
        "use alloc::List; pub fn inspect(view: borrow List<u8>) -> u32 { view.len() } fn main() {}",
    );
    let diagnostic = err(f.run(&["build", "--lib"]), "LE900");
    assert!(
        diagnostic.contains("external List ABI is not defined"),
        "{diagnostic}"
    );
}

#[test]
fn list_get_reads_copied_values_after_growth_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='list-get'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn byte_is(value: u8?, expected: u8) -> bool {
            match value { Some(byte) => byte == expected, None => false }
        }
        fn word_is(value: u32?, expected: u32) -> bool {
            match value { Some(word) => word == expected, None => false }
        }
        fn no_word(value: u32?) -> bool {
            match value { Some(_) => false, None => true }
        }
        fn no_byte(value: u8?) -> bool {
            match value { Some(_) => false, None => true }
        }
        fn main() -> bool ! Error {
            var bytes: List<u8> = [];
            var words: List<u32> = [];
            let empty := no_word(words.get(0)) && no_byte(bytes.get(4_294_967_295));
            var index: u32 = 0;
            loop {
                bytes.push(if index % 2 == 0 { 255 } else { 17 });
                words.push(305_419_896 + index);
                index += 1;
                if index == 200 { break; }
            }
            var calls := 0;
            let appended := words.get({
                calls += 1;
                words.push(4_294_967_295);
                words.len() - 1
            });
            let last := words.len();
            let frozen_words := words;
            let frozen_bytes := bytes;
            Ok(empty && calls == 1 && last == 201 && word_is(appended, 4_294_967_295)
                && word_is(frozen_words.get(0), 305_419_896)
                && word_is(frozen_words.get(199), 305_420_095)
                && word_is(frozen_words.get(200), 4_294_967_295)
                && byte_is(frozen_bytes.get(0), 255) && byte_is(frozen_bytes.get(199), 17)
                && no_byte(frozen_bytes.get(200)) && no_byte(frozen_bytes.get(4_294_967_295))
                && no_word(frozen_words.get(last)) && no_word(frozen_words.get(4_294_967_295)))
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "get.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "get.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn list_get_rejects_invalid_indices_and_moves_during_evaluation() {
    let f = Fixture::new();
    for (body, code) in [
        ("let index: i32 = 0; items.get(index);", "TE002"),
        ("items.get({ let moved := items; 0 });", "BE001"),
    ] {
        f.write(
            "list.mb",
            &format!("use alloc::List; fn main() {{ let items: List<u32> = []; {body} }}"),
        );
        err(f.run(&["ownership", "list.mb"]), code);
    }
}

#[test]
fn list_push_runs_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='list-push'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn check(move_it: bool) -> bool {
            var bytes: List<u8> = [];
            var words: List<u32> = [];
            var calls := 0;
            loop {
                bytes.push({ calls += 1; 195 });
                words.push(words.len() + 1);
                if calls == 20 { break; }
            }
            if move_it {
                var moved := words;
                moved.push(99);
                return moved.len() == 21 && bytes.len() == 20 && calls == 20;
            }
            words.len() == 20 && bytes.len() == 20
        }
        fn main() -> bool ! Error { Ok(check(false) && check(true)) }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "lists.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "lists.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn list_push_rejects_invalid_destinations_and_elements() {
    let f = Fixture::new();
    for (body, code) in [
        ("let items: List<u8> = []; items.push(1);", "TE017"),
        ("var items: List<u8> = []; items.push(true);", "TE002"),
        (
            "var items: List<u32> = []; items.push({ let moved := items; 1 });",
            "BE001",
        ),
    ] {
        f.write("list.mb", &format!("fn main() {{ {body} }}"));
        err(f.run(&["ownership", "list.mb"]), code);
    }
}

#[test]
fn empty_lists_and_local_moves_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='empty-lists'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; type Counter { count: u32 }
        type Words = List<u32>;
        fn main() -> bool ! Error {
            let existing: Counter = Counter { count: 7 };
            let bytes: List<u8> = [];
            var words: Words = [];
            let before := bytes.len() + words.len();
            let moved_bytes := bytes;
            var moved_words := words;
            Ok(existing.count == 7 && before == 0 && moved_bytes.len() == 0 && moved_words.len() == 0)
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "lists.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "lists.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);

    let bytes = fs::read(f.0.join("lists.wasm")).unwrap();
    let memory = wasmparser::Parser::new(0)
        .parse_all(&bytes)
        .find_map(|item| match item.unwrap() {
            wasmparser::Payload::MemorySection(section) => section.into_iter().next(),
            _ => None,
        })
        .unwrap()
        .unwrap();
    assert_eq!(memory.maximum, Some(memory.initial));
}

#[test]
fn empty_list_diagnostics_keep_moves_and_boundaries_checked() {
    let f = Fixture::new();
    for (source, code) in [
        (
            "use alloc::List; fn main() { let items: List<u8> = []; let moved := items; items.len(); }",
            "BE001",
        ),
        (
            "use alloc::List; fn main() { let items: List<List<u8>> = []; }",
            "TE017",
        ),
        ("use alloc::List; fn main() { let items: List<u8> = [true]; }", "TE002"),
        (
            "use alloc::List; fn main() { let items: List<u8> = []; let array := [items]; }",
            "TE017",
        ),
        (
            "use alloc::List; fn main() { let items: List<u8> = []; items.share(); }",
            "TE017",
        ),
        ("use alloc::List; fn main() -> List<u32> { [] }", "TE018"),
    ] {
        f.write("lists.mb", source);
        err(f.run(&["ownership", "lists.mb"]), code);
    }
}

#[test]
fn strings_execute_from_source_and_artifact_with_private_utf8_data() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='strings'\nentry='main::main'\n",
    );
    f.write(
        "src/text.mb",
        r#"pub type Text = string;
           pub fn make() -> Text { "é😀" }
           pub fn inspect(s: borrow Text) -> i32 {
               let byte_ok := match s.byte_at(1) { Some(byte) => byte == 169, None => false };
               let scalar_ok := match s.scalar_at(2) { Some(scalar) => scalar == 128_512, None => false };
               if s.len() == 6 && s.is_char_boundary(2) && !s.is_char_boundary(1)
                   && byte_ok && scalar_ok { 42 } else { 0 }
           }
           fn unused() -> Text { "unreachable literal" }"#,
    );
    f.write(
        "src/main.mb",
        r#"use self::text::Text;
           use self::text::make;
           use self::text::inspect;
           fn consume(s: Text) {}
           fn main() -> i32 ! Error {
               let s := make();
               let view := s.borrow();
               let checked := inspect(view);
               consume(s);
               consume("");
               Ok(checked)
           }"#,
    );
    let expected = b"Result: Ok(i32(42))\n";
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, expected);
    let build = f.run(&["build", "--output", "strings.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let bytes = fs::read(f.0.join("strings.wasm")).unwrap();
    wasmparser::Validator::new().validate_all(&bytes).unwrap();
    let sections = wasmparser::Parser::new(0)
        .parse_all(&bytes)
        .map(Result::unwrap)
        .find_map(|payload| match payload {
            wasmparser::Payload::DataSection(data) => Some(data),
            _ => None,
        })
        .expect("literal data section");
    assert_eq!(sections.count(), 1);
    let segment = sections.into_iter().next().unwrap().unwrap();
    let wasmparser::DataKind::Active {
        memory_index: 0,
        offset_expr,
    } = segment.kind
    else {
        panic!("expected literal data in memory zero");
    };
    let wasmparser::Operator::I32Const { value: start } =
        offset_expr.get_operators_reader().read().unwrap()
    else {
        panic!("expected a static literal data address");
    };
    let mut data = segment.data;
    let mut address = start as u32;
    // The main function's empty literal precedes the reachable make function.
    for expected in ["", "é😀"] {
        let pointer = u32::from_le_bytes(data[..4].try_into().unwrap());
        let length = u32::from_le_bytes(data[4..8].try_into().unwrap());
        assert_eq!(pointer, address + 12);
        assert_eq!(length as usize, expected.len());
        assert_eq!(&data[8..12], &0u32.to_le_bytes());
        assert_eq!(&data[12..12 + expected.len()], expected.as_bytes());
        data = &data[12 + expected.len()..];
        address = pointer + length;
    }
    assert!(data.is_empty(), "unused literals should stay out of Wasm");

    let standalone = Fixture::new();
    fs::write(standalone.0.join("strings.wasm"), bytes).unwrap();
    let artifact = standalone.run(&["run", "strings.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, expected);
}

#[test]
fn internal_static_string_results_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='string-result'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        type TextError: Error { offset: i32 }
        fn literal() -> string { "😀" }
        fn make(use_literal: bool, fail: bool) -> string ! TextError {
            if fail { return Err(TextError { code: 7, offset: 2 }); }
            if use_literal { return Ok("é"); }
            let text := literal();
            Ok(text)
        }
        fn inspect(result: string ! TextError) -> u32 {
            match result {
                Ok(text) => match text.scalar_at(0) { Some(value) => value, None => 0 },
                Err(error) => {
                    let TextError { code, offset } := error;
                    if offset == 2 { code } else { 0 }
                }
            }
        }
        fn main() -> bool ! Error {
            let first := make(true, false);
            Ok(inspect(first) == 233 && inspect(make(false, false)) == 128_512
                && inspect(make(false, true)) == 7)
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "result.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "result.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn immediately_matched_heap_string_results_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='heap-string-result'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn into_len(value: string) -> u32 { value.len() }
        fn check(early: bool) -> bool {
            let text := "é".concat("😀");
            let result: string ! Error = Ok(text);
            match result {
                Ok(value) => {
                    if early { return value.len() == 6; }
                    let scalar := match value.scalar_at(2) {
                        Some(code) => code == 128_512, None => false
                    };
                    scalar && into_len(value) == 6
                },
                Err(_) => false
            }
        }
        fn main() -> bool ! Error { Ok(check(false) && check(true)) }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "owned-result.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "owned-result.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn returned_heap_string_results_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='heap-string-return'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn make(mode: i32, text: string) -> string ! Error {
            if mode == 1 { return Ok("é"); }
            if mode == 2 { return Err(Error { code: 7 }); }
            Ok(text)
        }
        fn length(mode: i32) -> u32 {
            let result := make(mode, "a".concat("😀"));
            match result {
                Ok(value) => {
                    if value.len() == 5 { return value.len(); }
                    value.len()
                },
                Err(error) => error.code
            }
        }
        fn main() -> bool ! Error {
            let empty := match make(0, "".concat("")) {
                Ok(value) => value.len() == 0,
                Err(_) => false
            };
            Ok(empty && length(0) == 5 && length(1) == 2 && length(2) == 7)
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "returned-result.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "returned-result.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn returned_heap_results_require_an_immediate_consuming_match() {
    let f = Fixture::new();
    for body in [
        "make();",
        "let result := make();",
        "let result := make(); match result { Ok(_) => {}, Err(_) => {} };",
        "let result := make(); match result { Err(_) => {}, _ => {} };",
        "let result := make(); match result.borrow() { Ok(_) => {}, Err(_) => {} };",
        "let result := make(); 1 + 1; match result { Ok(value) => { value.len(); }, Err(_) => {} };",
        "take(make());",
        "forward();",
    ] {
        let forward = if body == "forward();" {
            "fn forward() -> string ! Error { make() }"
        } else {
            ""
        };
        f.write(
            "text.mb",
            &format!(
                r#"
            fn make() -> string ! Error {{
                let text := "é".concat("!");
                return Ok(text);
            }}
            fn take(result: string ! Error) {{}}
            {forward}
            fn main() {{ {body} }}
        "#
            ),
        );
        let diagnostic = err(f.run(&["ownership", "text.mb"]), "TE018");
        assert!(
            diagnostic.contains("requires an immediate consuming match"),
            "{body}: {diagnostic}"
        );
    }
}

#[test]
fn heap_string_results_reject_escape_and_ignore_paths() {
    let f = Fixture::new();
    for body in [
        r#"let text := "é".concat("!"); let result: string ! Error = Ok(text); match result { Ok(_) => {}, Err(_) => {} };"#,
        r#"let text := "é".concat("!"); let result: string ! Error = Ok(text); match result { Err(_) => {}, _ => {} };"#,
        r#"let text := "é".concat("!"); let result: string ! Error = Ok(text); 1 + 1; match result { Ok(text) => { text.len(); }, Err(_) => {} };"#,
        r#"let text := "é".concat("!"); let result: string ! Error = Ok(text);"#,
        r#"let result := wrap("é".concat("!"));"#,
        r#"let result: string ! Error = Ok(heap());"#,
        r#"var text := "é"; append(text.share()); let result: string ! Error = Ok(text);"#,
    ] {
        f.write(
            "text.mb",
            &format!(
                r#"
            fn wrap(text: string) -> string ! Error {{ Ok(text) }}
            fn heap() -> string {{ let text := "é".concat("!"); text }}
            fn append(text: share string) {{ text.push_str("!"); }}
            fn main() {{ {body} }}
        "#
            ),
        );
        let diagnostic = err(f.run(&["ownership", "text.mb"]), "TE018");
        assert!(
            diagnostic.contains("heap String") || diagnostic.contains("heap `string ! E`"),
            "{body}: {diagnostic}"
        );
    }
}

#[test]
fn internal_string_results_require_consuming_payload_matches() {
    let f = Fixture::new();
    f.write(
        "text.mb",
        r#"
        fn main() -> u32 {
            let result: string ! Error = Ok("é");
            match result.borrow() { Ok(text) => text.len(), Err(_) => 0 }
        }
    "#,
    );
    let diagnostic = err(f.run(&["ownership", "text.mb"]), "TE018");
    assert!(
        diagnostic.contains("String enum payloads require a consuming match"),
        "{diagnostic}"
    );
}

#[test]
fn wasm_gates_string_exports_and_nested_storage() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='strings'\nentry='main::main'\n[export]\ncheck='main::main'\n",
    );
    for (source, args, message) in [
        (
            r#"pub fn main() -> string { "é" }"#,
            &["build"][..],
            "exported signatures cannot use String",
        ),
        (
            "pub fn main(s: borrow string) {}",
            &["build", "--lib"][..],
            "exported signatures cannot use String",
        ),
        (
            r#"pub fn main() -> string ! Error { Ok("é") }"#,
            &["build"][..],
            "primitive success payload",
        ),
        (
            r#"pub fn main() -> string ! Error { Ok("é") }"#,
            &["build", "--lib"][..],
            "exported signatures cannot return enums",
        ),
        (
            r#"pub fn main() -> string ! Error { let text := "é".concat("!"); Ok(text) }"#,
            &["build"][..],
            "primitive success payload",
        ),
        (
            r#"pub fn main() -> string ! Error { let text := "é".concat("!"); Ok(text) }"#,
            &["build", "--lib"][..],
            "exported signatures cannot return enums",
        ),
        (
            r#"pub fn main() -> string ! Utf8Error { let input: array<u8, 1> = [65]; input.to_utf8_string(1) }"#,
            &["build"][..],
            "primitive success payload",
        ),
    ] {
        f.write("src/main.mb", source);
        let diagnostic = err(f.run(args), "LE900");
        assert!(diagnostic.contains(message), "{diagnostic}");
        assert!(!f.0.join("target/memobits/app.wasm").exists());
    }
}

#[test]
fn wasm_gates_unsupported_string_struct_uses() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='labels'\nentry='main::main'\n",
    );
    for (source, code, message) in [
        (
            r#"fn main() { let text := "a".concat("b"); let label := if true { Label { text: text } } else { Label { text: "c" } }; }"#,
            "LE900",
            "requires a direct new local binding",
        ),
        (
            r#"fn make() -> string { let text := "a".concat("b"); text }
                fn main() { let label := Label { text: { make() } }; }"#,
            "TE018",
            "heap String call result must be assigned directly",
        ),
        (
            r#"fn main() { let label := if true { Label { text: "a".concat("b") } } else { Label { text: "c" } }; }"#,
            "LE900",
            "requires a direct new local binding",
        ),
        (
            r#"fn make() -> string { "a" }
                fn main() { let label := if true { Label { text: make() } } else { Label { text: "c" } }; }"#,
            "LE900",
            "requires a direct new local binding",
        ),
        (
            r#"fn make() -> string { "a" }
                fn main() { let named := make(); let label := Label { text: named }; }"#,
            "LE900",
            "requires a direct String literal",
        ),
        (
            r#"fn main() { let text := "a"; let label := Label { text: text }; }"#,
            "LE900",
            "requires a direct String literal",
        ),
        (
            r#"fn main() {
                let text := "a".concat("b");
                var label := Label { text: text };
                label = Label { text: "c" };
            }"#,
            "TE018",
            "requires a new local binding",
        ),
        (
            r#"fn main() {
                let text := "a".concat("b");
                let label := Label { text: text };
                let Label { text: field } := label;
            }"#,
            "TE018",
            "can only move directly into a new local",
        ),
        (
            r#"fn replace(var label: Label) { label.text = label.text.concat("!"); } fn main() {}"#,
            "TE017",
            "concat requires",
        ),
        (
            r#"fn make() -> Label { let text := "a".concat("b"); Label { text: text } } fn main() {}"#,
            "LE900",
            "requires a direct new local binding",
        ),
        (
            r#"fn main() { let label := Label { text: "a" }; let view := label.borrow(); }"#,
            "LE900",
            "cannot be stored in local bindings",
        ),
        (
            r#"fn inspect(label: borrow Label) {}
                fn forward(label: borrow Label) { inspect(label); }
                fn main() {}"#,
            "LE900",
            "requires a named owner",
        ),
    ] {
        f.write(
            "src/main.mb",
            &format!("type Label {{ text: string }} {source}"),
        );
        let output = f.run(&["build"]);
        assert_eq!(output.status.code(), Some(1), "{source}: {output:?}");
        let diagnostic = String::from_utf8(output.stderr).unwrap();
        assert!(diagnostic.contains(code), "{source}: {diagnostic}");
        assert!(diagnostic.contains(message), "{source}: {diagnostic}");
    }
}

#[test]
fn string_struct_call_borrow_blocks_moves_and_field_replacement() {
    let f = Fixture::new();
    for later_argument in [r#"label.text = "changed"; 0"#, "let moved := label; 0"] {
        f.write(
            "text.mb",
            &format!(
                r#"type Label {{ text: string }}
                fn inspect(label: borrow Label, extra: u32) -> u32 {{ label.text.len() + extra }}
                fn main() {{
                    var label := Label {{ text: "old".concat("!") }};
                    inspect(label.borrow(), {{ {later_argument} }});
                }}"#
            ),
        );
        err(f.run(&["ownership", "text.mb"]), "BE005");
    }
}

#[test]
fn string_struct_share_reads_keep_caller_ownership_and_artifact_parity() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='string-struct-share'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        type Label { text: string, number: u32 }
        fn inspect(label: share Label, expected: u8) -> bool {
            label.number == 7 && label.text.len() == 3
                && match label.text.byte_at(2) {
                    Some(byte) => byte == expected,
                    None => false,
                }
        }
        pub fn main() -> bool ! Error {
            let prefix := "é";
            var label := Label { text: prefix.concat("!"), number: 7 };
            let first := inspect(label.share(), 33);
            label.text = prefix.concat("?");
            let second := inspect(label.share(), 63);
            let moved := label;
            Ok(first && second && moved.text.len() == 3)
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "share.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "share.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn string_struct_share_replaces_fields_with_caller_cleanup_and_parity() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='string-struct-share-write'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        type Record { text: string, sibling: string, number: u32 }
        fn byte_is(value: borrow string, index: u32, expected: u8) -> bool {
            match value.byte_at(index) { Some(byte) => byte == expected, None => false }
        }
        fn direct_result() -> string { let text := "call".concat("!"); text }
        fn replace(record: share Record, mode: u32) {
            let sibling := record.sibling.borrow();
            if mode == 0 {
                record.text = "fresh".concat("!");
            } else if mode == 1 {
                let next := "other".concat("?");
                record.text = next;
            } else if mode == 2 {
                record.text = record.text.concat("!");
            } else if mode == 3 {
                record.text = direct_result();
            } else {
                record.text = "fixed";
            }
            if sibling.len() != 4 { return; }
        }
        pub fn main() -> bool ! Error {
            var record := Record { text: "old", sibling: "keep", number: 8 };
            replace(record.share(), 0);
            if record.text.len() != 6 || !byte_is(record.text.borrow(), 5, 33) { return Ok(false); }
            replace(record.share(), 1);
            if record.text.len() != 6 || !byte_is(record.text.borrow(), 5, 63) { return Ok(false); }
            replace(record.share(), 2);
            if record.text.len() != 7 || !byte_is(record.text.borrow(), 6, 33) { return Ok(false); }
            replace(record.share(), 3);
            if record.text.len() != 5 || !byte_is(record.text.borrow(), 4, 33) { return Ok(false); }
            replace(record.share(), 4);
            let moved := record;
            Ok(moved.number == 8 && moved.text.len() == 5
                && byte_is(moved.text.borrow(), 0, 102)
                && byte_is(moved.sibling.borrow(), 0, 107))
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "share-write.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "share-write.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn string_struct_share_keeps_storage_alias_and_mutation_gates() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='string-struct-share-gates'\nentry='main::main'\n",
    );
    for (source, code, message) in [
        (
            "type Label { text: string } fn inspect(label: share Label) {} fn main() { let label := Label { text: \"x\" }; inspect(label.share()); }",
            "TE017",
            "share conversion requires a mutable local owner",
        ),
        (
            "type Label { text: string } fn inspect(label: share Label) {} fn main() { var label := Label { text: \"x\" }; let view := label.share(); }",
            "LE900",
            "cannot be stored in local bindings",
        ),
        (
            "type Label { text: string } fn inspect(left: share Label, right: share Label) {} fn main() { var label := Label { text: \"x\" }; inspect(label.share(), label.share()); }",
            "BE005",
            "already shares it",
        ),
        (
            "type Label { text: string } fn inspect(label: share Label, extra: u32) {} fn main() { var label := Label { text: \"x\" }; inspect(label.share(), label.text.len()); }",
            "BE005",
            "while it is shared",
        ),
        (
            "type Label { text: string } fn inspect(label: share Label, extra: u32) {} fn main() { var label := Label { text: \"x\" }; inspect(label.share(), { label.text = \"y\"; 0 }); }",
            "BE005",
            "while it is shared",
        ),
        (
            "type Label { text: string } fn replace(label: share Label) { label.text = \"new\"; } fn main() { var label := Label { text: \"old\" }; let view := label.text.borrow(); replace(label.share()); view.len(); }",
            "BE005",
            "while it is borrowed",
        ),
        (
            "type Label { text: string } fn inspect(label: share Label) {} fn forward(label: share Label) { inspect(label); } fn main() {}",
            "LE900",
            "requires a named owner and direct use",
        ),
    ] {
        f.write("src/main.mb", source);
        let output = f.run(&["build"]);
        assert_eq!(output.status.code(), Some(1), "{source}: {output:?}");
        let diagnostic = String::from_utf8(output.stderr).unwrap();
        assert!(diagnostic.contains(code), "{source}: {diagnostic}");
        assert!(diagnostic.contains(message), "{source}: {diagnostic}");
    }
}

#[test]
fn string_struct_reference_is_not_an_exported_parameter() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='labels'\nentry='main::main'\n[export]\ninspect='main::inspect'\n",
    );
    f.write(
        "src/main.mb",
        "pub type Label { text: string } pub fn inspect(label: share Label) -> u32 { label.text.len() }",
    );
    let diagnostic = err(f.run(&["build", "--lib"]), "LE900");
    assert!(
        diagnostic.contains("Wasm exported signatures cannot take structs"),
        "{diagnostic}"
    );
}

#[test]
fn string_field_replacement_rejects_conflicting_loans_and_unavailable_owners() {
    let f = Fixture::new();
    for (body, code) in [
        (
            "let view := label.text.borrow(); label.text = replacement; inspect(view);",
            "BE005",
        ),
        (
            "let view := replacement.borrow(); label.text = replacement; inspect(view);",
            "BE005",
        ),
        (
            "label.text = replacement; inspect(replacement.borrow());",
            "BE001",
        ),
        ("let moved := label; label.text = replacement;", "BE001"),
    ] {
        f.write(
            "text.mb",
            &format!(
                r#"type Label {{ text: string }}
                fn inspect(value: borrow string) {{}}
                fn main() {{
                    var label := Label {{ text: "old" }};
                    let replacement := "new".concat("!");
                    {body}
                }}"#
            ),
        );
        err(f.run(&["ownership", "text.mb"]), code);
    }
}

#[test]
fn temporary_string_field_replacement_checks_loans_during_rhs_and_write() {
    let f = Fixture::new();
    for body in [
        r#"let view := label.text.borrow(); label.text = label.text.concat("!"); inspect(view);"#,
        r#"label.text = label.text.concat({ label.text = "other"; "!" });"#,
        r#"let view := label.text.borrow(); label.text = append(view); inspect(view);"#,
    ] {
        f.write(
            "text.mb",
            &format!(
                r#"type Label {{ text: string }}
                fn inspect(value: borrow string) {{}}
                fn append(value: borrow string) -> string {{
                    let text := value.concat("!");
                    text
                }}
                fn main() {{
                    var label := Label {{ text: "old" }};
                    {body}
                }}"#
            ),
        );
        err(f.run(&["ownership", "text.mb"]), "BE005");
    }
}

#[test]
fn temporary_string_field_initializer_keeps_operand_loan_live() {
    let f = Fixture::new();
    f.write(
        "text.mb",
        r#"
        type Label { text: string }
        fn main() {
            var original := Label { text: "old" };
            let label := Label {
                text: original.text.concat({ original.text = "new"; "!" }),
            };
        }
        "#,
    );
    err(f.run(&["ownership", "text.mb"]), "BE005");
}

#[test]
fn string_struct_moves_invalidate_the_source_and_respect_field_loans() {
    let f = Fixture::new();
    for (body, code) in [
        (r#"let moved := label; label.text.len();"#, "BE001"),
        (
            r#"let view := label.text.borrow(); let moved := label; inspect(view);"#,
            "BE005",
        ),
        (
            r#"label.text.byte_at({ label = Label { text: "x" }; let offset: u32 = 0; offset });"#,
            "BE005",
        ),
    ] {
        f.write(
            "text.mb",
            &format!(
                r#"type Label {{ text: string }}
                fn inspect(text: borrow string) {{}}
                fn main() {{ var label := Label {{ text: "é" }}; {body} }}"#
            ),
        );
        err(f.run(&["ownership", "text.mb"]), code);
    }
}

#[test]
fn heap_string_struct_moves_respect_loans_and_invalidate_the_source() {
    let f = Fixture::new();
    for (body, code) in [
        ("inspect(text.borrow());", "BE001"),
        (
            "let view := label.text.borrow(); let moved := label; inspect(view);",
            "BE005",
        ),
    ] {
        f.write(
            "text.mb",
            &format!(
                r#"type Label {{ text: string }}
                fn inspect(text: borrow string) {{}}
                fn main() {{
                    let text := "é".concat("!");
                    let label := Label {{ text: text }};
                    {body}
                }}"#
            ),
        );
        err(f.run(&["ownership", "text.mb"]), code);
    }
}

#[test]
fn string_ownership_uses_last_borrow_use_and_rejects_moves_and_reads() {
    let f = Fixture::new();
    let helpers = "fn inspect(s: borrow string) {} fn consume(s: string) {}";
    for (body, expected) in [
        (
            r#"let s := "é"; consume(s); inspect(s.borrow());"#,
            Some("BE001"),
        ),
        (
            r#"let s := "é"; let view := s.borrow(); consume(s); inspect(view);"#,
            Some("BE005"),
        ),
        (
            r#"let s := "é"; let view := s.borrow(); inspect(view); consume(s);"#,
            None,
        ),
    ] {
        f.write("text.mb", &format!("{helpers} fn main() {{ {body} }}"));
        let output = f.run(&["ownership", "text.mb"]);
        if let Some(code) = expected {
            err(output, code);
        } else {
            assert!(output.status.success(), "{output:?}");
        }
    }
}

#[test]
fn string_byte_and_scalar_reads_respect_receiver_loans() {
    let f = Fixture::new();
    for (body, code) in [
        (r#"let s := "é"; let moved := s; s.byte_at(0);"#, "BE001"),
        (
            r#"let s := "é"; let view := s.borrow(); let moved := s; view.byte_at(0);"#,
            "BE005",
        ),
        (
            r#"var s := "é"; s.byte_at({ s = "x"; let index: u32 = 0; index });"#,
            "BE005",
        ),
    ] {
        for method in ["byte_at", "scalar_at"] {
            let body = body.replace("byte_at", method);
            f.write("text.mb", &format!("fn main() {{ {body} }}"));
            err(f.run(&["ownership", "text.mb"]), code);
        }
    }
}

#[test]
fn string_boundary_keeps_receiver_loans_live_until_the_read() {
    let f = Fixture::new();
    for (body, expected) in [
        (
            r#"let s := "é"; let moved := s; s.is_char_boundary(0);"#,
            Some("BE001"),
        ),
        (
            r#"let s := "é"; let view := s.borrow(); let moved := s; view.is_char_boundary(0);"#,
            Some("BE005"),
        ),
        (
            r#"var s := "é"; let editor := s.share(); s.is_char_boundary(0); editor.len();"#,
            Some("BE005"),
        ),
        (
            r#"var s := "é"; s.is_char_boundary({ s = "x"; let offset: u32 = 0; offset });"#,
            Some("BE005"),
        ),
        (
            r#"let s := "é"; let view := s.borrow(); s.is_char_boundary(0); view.is_char_boundary(2); let moved := s; moved.is_char_boundary(2);"#,
            None,
        ),
    ] {
        f.write("text.mb", &format!("fn main() {{ {body} }}"));
        let output = f.run(&["ownership", "text.mb"]);
        if let Some(code) = expected {
            err(output, code);
        } else {
            assert!(output.status.success(), "{output:?}");
        }
    }
}

#[test]
fn string_length_observes_move_and_loan_rules() {
    let f = Fixture::new();
    for (body, expected) in [
        (r#"let s := "é"; let moved := s; s.len();"#, Some("BE001")),
        (
            r#"let s := "é"; let view := s.borrow(); let moved := s; view.len();"#,
            Some("BE005"),
        ),
        (
            r#"var s := "é"; let editor := s.share(); s.len(); editor.len();"#,
            Some("BE005"),
        ),
        (
            r#"let s := "é"; let view := s.borrow(); let n := s.len(); view.len(); let moved := s; moved.len();"#,
            None,
        ),
    ] {
        f.write("text.mb", &format!("fn main() {{ {body} }}"));
        let output = f.run(&["ownership", "text.mb"]);
        if let Some(code) = expected {
            err(output, code);
        } else {
            assert!(output.status.success(), "{output:?}");
        }
    }
}

#[test]
fn astar_example_checks_optimal_cost_and_unreachable_in_source_and_wasm() {
    assert_example_runs_in_both_modes("apps/astar", b"Result: Ok(i32(12))\n");
}

#[test]
fn enf_lexer_example_checks_byte_fixtures_in_source_and_wasm() {
    assert_example_runs_in_both_modes("apps/enf-lexer", b"Result: Ok(i32(0))\n");
}

#[test]
fn strict_utf8_construction_runs_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='utf8-construction'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn convert(input: borrow array<u8, 4>, length: i32) -> string ! Utf8Error {
            input.to_utf8_string(length)
        }
        fn byte_is(text: borrow string, offset: u32, expected: u8) -> bool {
            match text.byte_at(offset) { Some(byte) => byte == expected, None => false }
        }
        fn error_is(input: borrow array<u8, 4>, length: i32, code: u32, offset: i32) -> bool {
            match input.to_utf8_string(length) {
                Ok(text) => false,
                Err(error) => {
                    let Utf8Error { code: actual, offset: found } := error;
                    actual == code && match found {
                        Some(value) => value == offset, None => offset == -1
                    }
                }
            }
        }
        fn main() -> bool ! Error {
            let input: array<u8, 4> = [195, 169, 0, 255];
            let result := convert(input.borrow(), 3);
            let exact := match result {
                Ok(text) => text.len() == 3 && byte_is(text.borrow(), 0, 195)
                    && byte_is(text.borrow(), 1, 169) && byte_is(text.borrow(), 2, 0),
                Err(_) => false
            };
            let empty_input: array<u8, 2> = [255, 255];
            let empty := match empty_input.to_utf8_string(0) {
                Ok(text) => text.len() == 0, Err(_) => false
            };
            let malformed: array<u8, 4> = [65, 237, 160, 128];
            Ok(exact && empty && input[3] == 255
                && error_is(input.borrow(), 4, 2, 3)
                && error_is(input.borrow(), 1, 3, 1)
                && error_is(input.borrow(), -1, 1, -1)
                && error_is(input.borrow(), 5, 1, -1)
                && error_is(malformed.borrow(), 3, 4, 2))
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "utf8.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "utf8.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn utf8_constructor_rejects_unclaimed_results() {
    let f = Fixture::new();
    for body in [
        "input.to_utf8_string(1);",
        "match input.to_utf8_string(1) { Ok(_) => {}, Err(_) => {} };",
    ] {
        f.write(
            "utf8.mb",
            &format!("fn main() {{ let input: array<u8, 1> = [65]; {body} }}"),
        );
        let diagnostic = err(f.run(&["ownership", "utf8.mb"]), "TE018");
        assert!(
            diagnostic.contains("must be returned directly or immediately matched"),
            "{diagnostic}"
        );
    }
}

#[test]
fn utf8_validation_checks_receiver_type_and_borrows_through_length_evaluation() {
    let f = Fixture::new();
    for (source, code, message) in [
        (
            "fn main() { let values := [1, 2]; values.validate_utf8(1); }",
            "TE017",
            "requires a fixed byte array",
        ),
        (
            "fn main() { var bytes: array<u8, 2> = [1, 2]; bytes.validate_utf8({ bytes[0] = 0; 1 }); }",
            "BE005",
            "borrowed",
        ),
    ] {
        f.write("utf8.mb", source);
        let diagnostic = err(f.run(&["ownership", "utf8.mb"]), code);
        assert!(diagnostic.contains(message), "{diagnostic}");
    }
}

#[test]
fn utf8_validator_example_checks_byte_fixtures_in_source_and_wasm() {
    assert_example_runs_in_both_modes("apps/utf8-validator", b"Result: Ok(i32(0))\n");
}

#[test]
fn scalar_traversal_counts_scalars_separately_from_utf8_bytes_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='scalar-traversal'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn scalar_width(value: u32) -> u32 {
            if value <= 127 { 1 }
            else if value <= 2_047 { 2 }
            else if value <= 65_535 { 3 }
            else { 4 }
        }
        fn scalar_count(value: borrow string) -> u32 {
            let bytes := value.len();
            var offset: u32 = 0;
            var count: u32 = 0;
            loop {
                if offset == bytes { break; }
                let scalar := match value.scalar_at(offset) {
                    Some(decoded) => decoded,
                    None => { return count; },
                };
                offset += scalar_width(scalar);
                count += 1;
            }
            count
        }
        fn main() -> bool ! Error {
            let text := "aé€😀";
            let ascii_text := "abc";
            let supplementary_text := "😀";
            let empty_text := "";
            let count := scalar_count(text.borrow());
            let moved := text;
            Ok(count == 4 && moved.len() == 10
                && scalar_count(ascii_text.borrow()) == 3 && ascii_text.len() == 3
                && scalar_count(supplementary_text.borrow()) == 1 && supplementary_text.len() == 4
                && scalar_count(empty_text.borrow()) == 0 && empty_text.len() == 0)
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "scalar-traversal.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "scalar-traversal.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn language_guide_checks_bytes_array_equivalence_in_source_and_wasm() {
    assert_example_runs_in_both_modes("guide", b"Result: Ok(i32(42))\n");
}

#[test]
fn user_defined_add_selects_core_ops_interface_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='add-interface-identity'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use other;
        pub type Point { pub value: i32 }
        pub type Counter { pub value: i32 }
        use core::ops::Add;
        extend Point of Add {
            type Rhs = Point;
            type Output = Point;
            fn add(self, rhs: Point) -> Point {
                Point { value: self.value + rhs.value }
            }
        }
        fn make_left(counter: share Counter) -> Point {
            counter.value = counter.value + 1;
            Point { value: counter.value * 10 }
        }
        fn make_right(counter: share Counter) -> Point {
            counter.value = counter.value + 1;
            Point { value: counter.value }
        }
        fn main() -> i32 {
            var counter := Counter { value: 0 };
            let total := make_left(counter.share()) + make_right(counter.share());
            if total.value == 12 && counter.value == 2 { 42 } else { 0 }
        }
        "#,
    );
    f.write(
        "src/other.mb",
        "use self::main::Point; pub interface Add { fn add(self, rhs: Point) -> Point; } pub extend Point of Add { fn add(self, rhs: Point) -> Point { Point { value: 0 } } }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "add-interface.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "add-interface.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn user_defined_sub_supports_heterogeneous_generic_operands_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='sub-interface'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Sub; type Left { value: i32 } type Right { value: i32 } type Difference { value: i32 } extend Left of Sub { type Rhs = Right; type Output = Difference; fn sub(self, rhs: Right) -> Difference { Difference { value: self.value - rhs.value } } } fn subtract<T>(left: T, right: T::Rhs) -> T::Output where T: Sub { left - right } fn main() -> i32 { let result: Difference = subtract(Left { value: 50 }, Right { value: 8 }); result.value }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "sub-interface.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "sub-interface.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn user_defined_mul_supports_heterogeneous_generic_operands_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='mul-interface'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Mul; type Left { value: i32 } type Right { value: i32 } type Product { value: i32 } extend Left of Mul { type Rhs = Right; type Output = Product; fn mul(self, rhs: Right) -> Product { Product { value: self.value * rhs.value } } } fn multiply<T>(left: T, right: T::Rhs) -> T::Output where T: Mul { left * right } fn main() -> i32 { let result: Product = multiply(Left { value: 6 }, Right { value: 7 }); result.value }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "mul-interface.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "mul-interface.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn user_defined_mul_rejects_wrong_rhs_type() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='mul-rhs'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Mul; type Left { value: i32 } type Right { value: i32 } type Other { value: i32 } type Difference { value: i32 } extend Left of Mul { type Rhs = Right; type Output = Difference; fn mul(self, rhs: Right) -> Difference { Difference { value: self.value * rhs.value } } } fn main() -> i32 { let result := Left { value: 50 } * Other { value: 8 }; result.value }",
    );
    let diagnostic = err(f.run(&["build", "--output", "mul-rhs.wasm"]), "TE007");
    assert!(
        diagnostic.contains("Mul requires an owned receiver"),
        "{diagnostic}"
    );
}

#[test]
fn user_defined_mul_rejects_missing_inactive_and_ambiguous_implementations() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='mul-selection'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Mul; type Left {} type Right {} fn main() -> i32 { let value := Left {} * Right {}; 0 }",
    );
    let missing = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        missing.contains("no visible Mul implementation"),
        "{missing}"
    );

    f.write(
        "src/main.mb",
        "use other::marker; use core::ops::Mul; pub type Left {} pub type Right {} pub type Difference { pub value: i32 } fn main() -> i32 { let value := Left {} * Right {}; value.value }",
    );
    f.write(
        "src/other.mb",
        "use self::main::Left; use self::main::Right; use self::main::Difference; pub fn marker() {} pub extend Left of core::ops::Mul { type Rhs = Right; type Output = Difference; fn mul(self, rhs: Right) -> Difference { Difference { value: 42 } } }",
    );
    let inactive = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        inactive.contains("no visible Mul implementation"),
        "{inactive}"
    );

    f.write(
        "src/main.mb",
        "use core::ops::Mul; type Left {} type Right {} type Difference { value: i32 } extend Left of Mul { type Rhs = Right; type Output = Difference; fn mul(self, rhs: Right) -> Difference { Difference { value: 20 } } } extend Left of Mul { type Rhs = Right; type Output = Difference; fn mul(self, rhs: Right) -> Difference { Difference { value: 22 } } } fn main() -> i32 { let value := Left {} * Right {}; value.value }",
    );
    let ambiguous = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        ambiguous.contains("ambiguous Mul implementation"),
        "{ambiguous}"
    );
}

#[test]
fn user_defined_sub_rejects_wrong_rhs_type() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='sub-rhs'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Sub; type Left { value: i32 } type Right { value: i32 } type Other { value: i32 } type Difference { value: i32 } extend Left of Sub { type Rhs = Right; type Output = Difference; fn sub(self, rhs: Right) -> Difference { Difference { value: self.value - rhs.value } } } fn main() -> i32 { let result := Left { value: 50 } - Other { value: 8 }; result.value }",
    );
    let diagnostic = err(f.run(&["build", "--output", "sub-rhs.wasm"]), "TE007");
    assert!(
        diagnostic.contains("Sub requires an owned receiver"),
        "{diagnostic}"
    );
}

#[test]
fn user_defined_sub_rejects_missing_inactive_and_ambiguous_implementations() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='sub-selection'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Sub; type Left {} type Right {} fn main() -> i32 { let value := Left {} - Right {}; 0 }",
    );
    let missing = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        missing.contains("no visible Sub implementation"),
        "{missing}"
    );

    f.write(
        "src/main.mb",
        "use other::marker; use core::ops::Sub; pub type Left {} pub type Right {} pub type Difference { pub value: i32 } fn main() -> i32 { let value := Left {} - Right {}; value.value }",
    );
    f.write(
        "src/other.mb",
        "use self::main::Left; use self::main::Right; use self::main::Difference; pub fn marker() {} pub extend Left of core::ops::Sub { type Rhs = Right; type Output = Difference; fn sub(self, rhs: Right) -> Difference { Difference { value: 42 } } }",
    );
    let inactive = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        inactive.contains("no visible Sub implementation"),
        "{inactive}"
    );

    f.write(
        "src/main.mb",
        "use core::ops::Sub; type Left {} type Right {} type Difference { value: i32 } extend Left of Sub { type Rhs = Right; type Output = Difference; fn sub(self, rhs: Right) -> Difference { Difference { value: 20 } } } extend Left of Sub { type Rhs = Right; type Output = Difference; fn sub(self, rhs: Right) -> Difference { Difference { value: 22 } } } fn main() -> i32 { let value := Left {} - Right {}; value.value }",
    );
    let ambiguous = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        ambiguous.contains("ambiguous Sub implementation"),
        "{ambiguous}"
    );
}

#[test]
fn user_defined_sub_consumes_both_owned_operands() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='sub-move'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Sub; type Point { value: i32 } extend Point of Sub { type Rhs = Point; type Output = Point; fn sub(self, rhs: Point) -> Point { Point { value: self.value - rhs.value } } } fn take(value: Point) {} fn main() -> i32 { let left := Point { value: 20 }; let right := Point { value: 22 }; let difference := left - right; take(left); difference.value }",
    );
    let diagnostic = err(f.run(&["ownership-project"]), "BE001");
    assert!(diagnostic.contains("left"), "{diagnostic}");
}

#[test]
fn user_defined_sub_rhs_early_return_unwinds_staged_owned_operand() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='sub-early-return'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Sub; type Point { value: i32 } extend Point of Sub { type Rhs = Point; type Output = Point; fn sub(self, rhs: Point) -> Point { Point { value: self.value - rhs.value } } } fn main() -> i32 { let left := Point { value: 20 }; let difference := left - { return 42; Point { value: 22 } }; difference.value }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "sub-early-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "sub-early-return.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn user_defined_mul_consumes_both_owned_operands() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='mul-move'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Mul; type Point { value: i32 } extend Point of Mul { type Rhs = Point; type Output = Point; fn mul(self, rhs: Point) -> Point { Point { value: self.value * rhs.value } } } fn take(value: Point) {} fn main() -> i32 { let left := Point { value: 20 }; let right := Point { value: 22 }; let difference := left * right; take(left); difference.value }",
    );
    let diagnostic = err(f.run(&["ownership-project"]), "BE001");
    assert!(diagnostic.contains("left"), "{diagnostic}");
    f.write(
        "src/main.mb",
        "use core::ops::Mul; type Point { value: i32 } extend Point of Mul { type Rhs = Point; type Output = Point; fn mul(self, rhs: Point) -> Point { Point { value: self.value * rhs.value } } } fn take(value: Point) {} fn main() -> i32 { let left := Point { value: 20 }; let right := Point { value: 22 }; let product := left * right; take(right); product.value }",
    );
    let diagnostic = err(f.run(&["ownership-project"]), "BE001");
    assert!(diagnostic.contains("right"), "{diagnostic}");
}

#[test]
fn user_defined_mul_rhs_early_return_unwinds_staged_owned_operand() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='mul-early-return'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Mul; type Point { value: i32 } extend Point of Mul { type Rhs = Point; type Output = Point; fn mul(self, rhs: Point) -> Point { Point { value: self.value * rhs.value } } } fn main() -> i32 { let left := Point { value: 20 }; let difference := left * { return 42; Point { value: 22 } }; difference.value }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "mul-early-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "mul-early-return.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn user_defined_div_supports_heterogeneous_generic_operands_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='div-interface'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Div; type Left { value: i32 } type Right { value: i32 } type Quotient { value: i32 } extend Left of Div { type Rhs = Right; type Output = Quotient; fn div(self, rhs: Right) -> Quotient { Quotient { value: self.value / rhs.value } } } fn divide<T>(left: T, right: T::Rhs) -> T::Output where T: Div { left / right } fn main() -> i32 { let result: Quotient = divide(Left { value: 84 }, Right { value: 2 }); result.value }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "div-interface.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "div-interface.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn user_defined_div_rejects_wrong_rhs_type() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='div-rhs'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Div; type Left { value: i32 } type Right { value: i32 } type Other { value: i32 } type Quotient { value: i32 } extend Left of Div { type Rhs = Right; type Output = Quotient; fn div(self, rhs: Right) -> Quotient { Quotient { value: self.value / rhs.value } } } fn main() -> i32 { let result := Left { value: 84 } / Other { value: 2 }; result.value }",
    );
    let diagnostic = err(f.run(&["build", "--output", "div-rhs.wasm"]), "TE007");
    assert!(
        diagnostic.contains("Div requires an owned receiver"),
        "{diagnostic}"
    );
}

#[test]
fn user_defined_div_rejects_missing_inactive_and_ambiguous_implementations() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='div-selection'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Div; type Left {} type Right {} fn main() -> i32 { let value := Left {} / Right {}; 0 }",
    );
    let missing = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        missing.contains("no visible Div implementation"),
        "{missing}"
    );

    f.write(
        "src/main.mb",
        "use other::marker; use core::ops::Div; pub type Left {} pub type Right {} pub type Quotient { pub value: i32 } fn main() -> i32 { let value := Left {} / Right {}; value.value }",
    );
    f.write(
        "src/other.mb",
        "use self::main::Left; use self::main::Right; use self::main::Quotient; pub fn marker() {} pub extend Left of core::ops::Div { type Rhs = Right; type Output = Quotient; fn div(self, rhs: Right) -> Quotient { Quotient { value: 42 } } }",
    );
    let inactive = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        inactive.contains("no visible Div implementation"),
        "{inactive}"
    );

    f.write(
        "src/main.mb",
        "use core::ops::Div; type Left {} type Right {} type Quotient { value: i32 } extend Left of Div { type Rhs = Right; type Output = Quotient; fn div(self, rhs: Right) -> Quotient { Quotient { value: 20 } } } extend Left of Div { type Rhs = Right; type Output = Quotient; fn div(self, rhs: Right) -> Quotient { Quotient { value: 22 } } } fn main() -> i32 { let value := Left {} / Right {}; value.value }",
    );
    let ambiguous = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        ambiguous.contains("ambiguous Div implementation"),
        "{ambiguous}"
    );
}

#[test]
fn user_defined_div_consumes_both_owned_operands() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='div-move'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Div; type Point { value: i32 } extend Point of Div { type Rhs = Point; type Output = Point; fn div(self, rhs: Point) -> Point { Point { value: self.value / rhs.value } } } fn take(value: Point) {} fn main() -> i32 { let left := Point { value: 84 }; let right := Point { value: 2 }; let quotient := left / right; take(left); quotient.value }",
    );
    let diagnostic = err(f.run(&["ownership-project"]), "BE001");
    assert!(diagnostic.contains("left"), "{diagnostic}");
    f.write(
        "src/main.mb",
        "use core::ops::Div; type Point { value: i32 } extend Point of Div { type Rhs = Point; type Output = Point; fn div(self, rhs: Point) -> Point { Point { value: self.value / rhs.value } } } fn take(value: Point) {} fn main() -> i32 { let left := Point { value: 84 }; let right := Point { value: 2 }; let quotient := left / right; take(right); quotient.value }",
    );
    let diagnostic = err(f.run(&["ownership-project"]), "BE001");
    assert!(diagnostic.contains("right"), "{diagnostic}");
}

#[test]
fn user_defined_div_rhs_early_return_unwinds_staged_owned_operand() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='div-early-return'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Div; type Point { value: i32 } extend Point of Div { type Rhs = Point; type Output = Point; fn div(self, rhs: Point) -> Point { Point { value: self.value / rhs.value } } } fn main() -> i32 { let left := Point { value: 84 }; let quotient := left / { return 42; Point { value: 2 } }; quotient.value }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "div-early-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "div-early-return.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn user_defined_rem_supports_heterogeneous_generic_operands_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='rem-interface'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Rem; type Left { value: i32 } type Right { value: i32 } type Remainder { value: i32 } extend Left of Rem { type Rhs = Right; type Output = Remainder; fn rem(self, rhs: Right) -> Remainder { Remainder { value: self.value % rhs.value } } } fn remainder<T>(left: T, right: T::Rhs) -> T::Output where T: Rem { left % right } fn main() -> i32 { let result: Remainder = remainder(Left { value: 84 }, Right { value: 2 }); result.value }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(0)\n");
    let build = f.run(&["build", "--output", "rem-interface.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "rem-interface.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn user_defined_rem_rejects_wrong_rhs_type() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='rem-rhs'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Rem; type Left { value: i32 } type Right { value: i32 } type Other { value: i32 } type Remainder { value: i32 } extend Left of Rem { type Rhs = Right; type Output = Remainder; fn rem(self, rhs: Right) -> Remainder { Remainder { value: self.value % rhs.value } } } fn main() -> i32 { let result := Left { value: 84 } % Other { value: 2 }; result.value }",
    );
    let diagnostic = err(f.run(&["build", "--output", "rem-rhs.wasm"]), "TE007");
    assert!(
        diagnostic.contains("Rem requires an owned receiver"),
        "{diagnostic}"
    );
}

#[test]
fn user_defined_rem_rejects_missing_inactive_and_ambiguous_implementations() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='rem-selection'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Rem; type Left {} type Right {} fn main() -> i32 { let value := Left {} % Right {}; 0 }",
    );
    let missing = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        missing.contains("no visible Rem implementation"),
        "{missing}"
    );

    f.write(
        "src/main.mb",
        "use other::marker; use core::ops::Rem; pub type Left {} pub type Right {} pub type Remainder { pub value: i32 } fn main() -> i32 { let value := Left {} % Right {}; value.value }",
    );
    f.write(
        "src/other.mb",
        "use self::main::Left; use self::main::Right; use self::main::Remainder; pub fn marker() {} pub extend Left of core::ops::Rem { type Rhs = Right; type Output = Remainder; fn rem(self, rhs: Right) -> Remainder { Remainder { value: 42 } } }",
    );
    let inactive = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        inactive.contains("no visible Rem implementation"),
        "{inactive}"
    );

    f.write(
        "src/main.mb",
        "use core::ops::Rem; type Left {} type Right {} type Remainder { value: i32 } extend Left of Rem { type Rhs = Right; type Output = Remainder; fn rem(self, rhs: Right) -> Remainder { Remainder { value: 20 } } } extend Left of Rem { type Rhs = Right; type Output = Remainder; fn rem(self, rhs: Right) -> Remainder { Remainder { value: 22 } } } fn main() -> i32 { let value := Left {} % Right {}; value.value }",
    );
    let ambiguous = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        ambiguous.contains("ambiguous Rem implementation"),
        "{ambiguous}"
    );
}

#[test]
fn user_defined_rem_consumes_both_owned_operands() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='rem-move'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Rem; type Point { value: i32 } extend Point of Rem { type Rhs = Point; type Output = Point; fn rem(self, rhs: Point) -> Point { Point { value: self.value % rhs.value } } } fn take(value: Point) {} fn main() -> i32 { let left := Point { value: 84 }; let right := Point { value: 2 }; let remainder := left % right; take(left); remainder.value }",
    );
    let diagnostic = err(f.run(&["ownership-project"]), "BE001");
    assert!(diagnostic.contains("left"), "{diagnostic}");
    f.write(
        "src/main.mb",
        "use core::ops::Rem; type Point { value: i32 } extend Point of Rem { type Rhs = Point; type Output = Point; fn rem(self, rhs: Point) -> Point { Point { value: self.value % rhs.value } } } fn take(value: Point) {} fn main() -> i32 { let left := Point { value: 84 }; let right := Point { value: 2 }; let remainder := left % right; take(right); remainder.value }",
    );
    let diagnostic = err(f.run(&["ownership-project"]), "BE001");
    assert!(diagnostic.contains("right"), "{diagnostic}");
}

#[test]
fn user_defined_rem_rhs_early_return_unwinds_staged_owned_operand() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='rem-early-return'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Rem; type Point { value: i32 } extend Point of Rem { type Rhs = Point; type Output = Point; fn rem(self, rhs: Point) -> Point { Point { value: self.value % rhs.value } } } fn main() -> i32 { let left := Point { value: 84 }; let remainder := left % { return 42; Point { value: 2 } }; remainder.value }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "rem-early-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "rem-early-return.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn user_defined_bitand_supports_heterogeneous_generic_operands_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitand-interface'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::BitAnd; type Left { value: u32 } type Right { value: u32 } type MaskResult { value: u32 } extend Left of BitAnd { type Rhs = Right; type Output = MaskResult; fn bitand(self, rhs: Right) -> MaskResult { MaskResult { value: self.value & rhs.value } } } fn intersect<T>(lhs: T, operand: T::Rhs) -> T::Output where T: BitAnd { lhs & operand } fn main() -> u32 { let lhs := Left { value: 12 }; let operand := Right { value: 10 }; let result: MaskResult = intersect(lhs, operand); result.value }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(8)\n");
    let build = f.run(&["build", "--output", "bitand-interface.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitand-interface.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(8)\n");
}

#[test]
fn user_defined_bitand_rejects_wrong_rhs_and_missing_ambiguous_implementations() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitand-selection'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::BitAnd; type Left {} type Right {} type Other {} type Output { value: u32 } extend Left of BitAnd { type Rhs = Right; type Output = Output; fn bitand(self, rhs: Right) -> Output { Output { value: 42 } } } fn main() -> u32 { let result := Left {} & Other {}; result.value }",
    );
    let wrong = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        wrong.contains("BitAnd requires an owned receiver"),
        "{wrong}"
    );

    f.write(
        "src/main.mb",
        "use core::ops::BitAnd; type Left {} type Right {} fn main() -> u32 { let result := Left {} & Right {}; 0 }",
    );
    let missing = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        missing.contains("no visible BitAnd implementation"),
        "{missing}"
    );

    f.write(
        "src/main.mb",
        "use other::marker; use core::ops::BitAnd; pub type Left {} pub type Right {} pub type MaskResult { pub value: u32 } fn main() -> u32 { let result := Left {} & Right {}; result.value }",
    );
    f.write(
        "src/other.mb",
        "use self::main::Left; use self::main::Right; use self::main::MaskResult; pub fn marker() {} pub extend Left of core::ops::BitAnd { type Rhs = Right; type Output = MaskResult; fn bitand(self, rhs: Right) -> MaskResult { MaskResult { value: 42 } } }",
    );
    let inactive = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        inactive.contains("no visible BitAnd implementation"),
        "{inactive}"
    );

    f.write(
        "src/main.mb",
        "use core::ops::BitAnd; type Left {} type Right {} type Output { value: u32 } extend Left of BitAnd { type Rhs = Right; type Output = Output; fn bitand(self, rhs: Right) -> Output { Output { value: 20 } } } extend Left of BitAnd { type Rhs = Right; type Output = Output; fn bitand(self, rhs: Right) -> Output { Output { value: 22 } } } fn main() -> u32 { let result := Left {} & Right {}; result.value }",
    );
    let ambiguous = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        ambiguous.contains("ambiguous BitAnd implementation"),
        "{ambiguous}"
    );
}

#[test]
fn user_defined_bitand_consumes_owned_operands_and_unwinds_rhs_early_return() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitand-move'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::BitAnd; type Point { value: u32 } extend Point of BitAnd { type Rhs = Point; type Output = Point; fn bitand(self, rhs: Point) -> Point { Point { value: self.value & rhs.value } } } fn take(value: Point) {} fn main() -> u32 { let left := Point { value: 15 }; let right := Point { value: 10 }; let result := left & right; take(left); result.value }",
    );
    let moved_left = err(f.run(&["ownership-project"]), "BE001");
    assert!(moved_left.contains("left"), "{moved_left}");
    f.write(
        "src/main.mb",
        "use core::ops::BitAnd; type Point { value: u32 } extend Point of BitAnd { type Rhs = Point; type Output = Point; fn bitand(self, rhs: Point) -> Point { Point { value: self.value & rhs.value } } } fn take(value: Point) {} fn main() -> u32 { let left := Point { value: 15 }; let right := Point { value: 10 }; let result := left & right; take(right); result.value }",
    );
    let moved_right = err(f.run(&["ownership-project"]), "BE001");
    assert!(moved_right.contains("right"), "{moved_right}");
    f.write(
        "src/main.mb",
        "use core::ops::BitAnd; type Point { value: u32 } extend Point of BitAnd { type Rhs = Point; type Output = Point; fn bitand(self, rhs: Point) -> Point { Point { value: self.value & rhs.value } } } fn main() -> u32 { let left := Point { value: 15 }; let result := left & { return 42; Point { value: 10 } }; result.value }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(42)\n");
    let build = f.run(&["build", "--output", "bitand-early-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitand-early-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(42)\n");
}

#[test]
fn user_defined_bitand_evaluates_operands_left_to_right() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitand-order'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::BitAnd; type Point { value: u32 } extend Point of BitAnd { type Rhs = Point; type Output = Point; fn bitand(self, rhs: Point) -> Point { Point { value: self.value & rhs.value } } } fn main() -> u32 { var order: u32 = 0; let result := { order = order * 10 + 1; Point { value: 15 } } & { if order != 1 { return 0; } order = order * 10 + 2; Point { value: 10 } }; if order != 12 { return 0; } result.value }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(10)\n");
    let build = f.run(&["build", "--output", "bitand-order.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitand-order.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(10)\n");
}

#[test]
fn user_defined_bitor_supports_heterogeneous_generic_operands_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitor-interface'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::BitOr; type Left { value: u32 } type Right { value: u32 } type MergeResult { value: u32 } extend Left of BitOr { type Rhs = Right; type Output = MergeResult; fn bitor(self, rhs: Right) -> MergeResult { MergeResult { value: self.value | rhs.value } } } fn merge<T>(lhs: T, operand: T::Rhs) -> T::Output where T: BitOr { lhs | operand } fn main() -> u32 { let result: MergeResult = merge(Left { value: 12 }, Right { value: 10 }); result.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(14)\n");
    let build = f.run(&["build", "--output", "bitor-interface.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitor-interface.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(14)\n");
}

#[test]
fn user_defined_bitor_rejects_wrong_rhs_and_missing_implementation() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitor-selection'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::BitOr; type Left {} type Right {} type Other {} type Output { value: u32 } extend Left of BitOr { type Rhs = Right; type Output = Output; fn bitor(self, rhs: Right) -> Output { Output { value: 42 } } } fn main() -> u32 { let result := Left {} | Other {}; result.value }");
    let wrong = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        wrong.contains("BitOr requires an owned receiver"),
        "{wrong}"
    );
    f.write("src/main.mb", "use core::ops::BitOr; type Left {} type Right {} fn main() -> u32 { let result := Left {} | Right {}; 0 }");
    let missing = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        missing.contains("no visible BitOr implementation"),
        "{missing}"
    );

    f.write("src/main.mb", "use core::ops::BitOr; type Left {} type Right {} type Output { value: u32 } extend Left of BitOr { type Rhs = Right; type Output = Output; fn bitor(self, rhs: Right) -> Output { Output { value: 20 } } } extend Left of BitOr { type Rhs = Right; type Output = Output; fn bitor(self, rhs: Right) -> Output { Output { value: 22 } } } fn main() -> u32 { let result := Left {} | Right {}; result.value }");
    let ambiguous = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        ambiguous.contains("ambiguous BitOr implementation"),
        "{ambiguous}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::BitOr; pub type Left {} pub type Right {} pub type Output { pub value: u32 } fn main() -> u32 { let result := Left {} | Right {}; result.value }");
    f.write("src/other.mb", "use self::main::Left; use self::main::Right; use self::main::Output; pub fn marker() {} pub extend Left of core::ops::BitOr { type Rhs = Right; type Output = Output; fn bitor(self, rhs: Right) -> Output { Output { value: 42 } } }");
    let inactive = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        inactive.contains("no visible BitOr implementation"),
        "{inactive}"
    );
}

#[test]
fn user_defined_bitor_consumes_owned_operands_and_unwinds_rhs_early_return() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitor-move'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::BitOr; type Point { value: u32 } extend Point of BitOr { type Rhs = Point; type Output = Point; fn bitor(self, rhs: Point) -> Point { Point { value: self.value | rhs.value } } } fn take(value: Point) {} fn main() -> u32 { let left := Point { value: 12 }; let right := Point { value: 10 }; let result := left | right; take(left); result.value }");
    let moved = err(f.run(&["ownership-project"]), "BE001");
    assert!(moved.contains("left"), "{moved}");
    f.write("src/main.mb", "use core::ops::BitOr; type Point { value: u32 } extend Point of BitOr { type Rhs = Point; type Output = Point; fn bitor(self, rhs: Point) -> Point { Point { value: self.value | rhs.value } } } fn take(value: Point) {} fn main() -> u32 { let left := Point { value: 12 }; let right := Point { value: 10 }; let result := left | right; take(right); result.value }");
    let moved_rhs = err(f.run(&["ownership-project"]), "BE001");
    assert!(moved_rhs.contains("right"), "{moved_rhs}");
    f.write("src/main.mb", "use core::ops::BitOr; type Point { value: u32 } extend Point of BitOr { type Rhs = Point; type Output = Point; fn bitor(self, rhs: Point) -> Point { Point { value: self.value | rhs.value } } } fn main() -> u32 { let left := Point { value: 12 }; let result := left | { return 42; Point { value: 10 } }; result.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(42)\n");
    let build = f.run(&["build", "--output", "bitor-early-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitor-early-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(42)\n");
}

#[test]
fn user_defined_bitor_evaluates_operands_left_to_right() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitor-order'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::BitOr; type Point { value: u32 } extend Point of BitOr { type Rhs = Point; type Output = Point; fn bitor(self, rhs: Point) -> Point { Point { value: self.value | rhs.value } } } fn main() -> u32 { var order: u32 = 0; let result := { order = order * 10 + 1; Point { value: 12 } } | { if order != 1 { return 0; } order = order * 10 + 2; Point { value: 10 } }; if order != 12 { return 0; } result.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(14)\n");
    let build = f.run(&["build", "--output", "bitor-order.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitor-order.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(14)\n");
}

#[test]
fn user_defined_bitxor_supports_heterogeneous_generic_operands_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitxor-interface'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::BitXor; type Left { value: u32 } type Right { value: u32 } type MergeResult { value: u32 } extend Left of BitXor { type Rhs = Right; type Output = MergeResult; fn bitxor(self, rhs: Right) -> MergeResult { MergeResult { value: self.value ^ rhs.value } } } fn merge<T>(lhs: T, operand: T::Rhs) -> T::Output where T: BitXor { lhs ^ operand } fn main() -> u32 { let result: MergeResult = merge(Left { value: 12 }, Right { value: 10 }); result.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(6)\n");
    let build = f.run(&["build", "--output", "bitxor-interface.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitxor-interface.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(6)\n");
}

#[test]
fn user_defined_bitxor_rejects_wrong_rhs_and_missing_implementation() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitxor-selection'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::BitXor; type Left {} type Right {} type Other {} type Output { value: u32 } extend Left of BitXor { type Rhs = Right; type Output = Output; fn bitxor(self, rhs: Right) -> Output { Output { value: 42 } } } fn main() -> u32 { let result := Left {} ^ Other {}; result.value }");
    let wrong = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        wrong.contains("BitXor requires an owned receiver"),
        "{wrong}"
    );
    f.write("src/main.mb", "use core::ops::BitXor; type Left {} type Right {} fn main() -> u32 { let result := Left {} ^ Right {}; 0 }");
    let missing = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        missing.contains("no visible BitXor implementation"),
        "{missing}"
    );

    f.write("src/main.mb", "use core::ops::BitXor; type Left {} type Right {} type Output { value: u32 } extend Left of BitXor { type Rhs = Right; type Output = Output; fn bitxor(self, rhs: Right) -> Output { Output { value: 20 } } } extend Left of BitXor { type Rhs = Right; type Output = Output; fn bitxor(self, rhs: Right) -> Output { Output { value: 22 } } } fn main() -> u32 { let result := Left {} ^ Right {}; result.value }");
    let ambiguous = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        ambiguous.contains("ambiguous BitXor implementation"),
        "{ambiguous}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::BitXor; pub type Left {} pub type Right {} pub type Output { pub value: u32 } fn main() -> u32 { let result := Left {} ^ Right {}; result.value }");
    f.write("src/other.mb", "use self::main::Left; use self::main::Right; use self::main::Output; pub fn marker() {} pub extend Left of core::ops::BitXor { type Rhs = Right; type Output = Output; fn bitxor(self, rhs: Right) -> Output { Output { value: 42 } } }");
    let inactive = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        inactive.contains("no visible BitXor implementation"),
        "{inactive}"
    );
}

#[test]
fn user_defined_bitxor_consumes_owned_operands_and_unwinds_rhs_early_return() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitxor-move'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::BitXor; type Point { value: u32 } extend Point of BitXor { type Rhs = Point; type Output = Point; fn bitxor(self, rhs: Point) -> Point { Point { value: self.value ^ rhs.value } } } fn take(value: Point) {} fn main() -> u32 { let left := Point { value: 12 }; let right := Point { value: 10 }; let result := left ^ right; take(left); result.value }");
    let moved = err(f.run(&["ownership-project"]), "BE001");
    assert!(moved.contains("left"), "{moved}");
    f.write("src/main.mb", "use core::ops::BitXor; type Point { value: u32 } extend Point of BitXor { type Rhs = Point; type Output = Point; fn bitxor(self, rhs: Point) -> Point { Point { value: self.value ^ rhs.value } } } fn take(value: Point) {} fn main() -> u32 { let left := Point { value: 12 }; let right := Point { value: 10 }; let result := left ^ right; take(right); result.value }");
    let moved_rhs = err(f.run(&["ownership-project"]), "BE001");
    assert!(moved_rhs.contains("right"), "{moved_rhs}");
    f.write("src/main.mb", "use core::ops::BitXor; type Point { value: u32 } extend Point of BitXor { type Rhs = Point; type Output = Point; fn bitxor(self, rhs: Point) -> Point { Point { value: self.value ^ rhs.value } } } fn main() -> u32 { let left := Point { value: 12 }; let result := left ^ { return 42; Point { value: 10 } }; result.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(42)\n");
    let build = f.run(&["build", "--output", "bitxor-early-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitxor-early-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(42)\n");
}

#[test]
fn user_defined_bitxor_consumes_rhs_operand() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitxor-rhs-move'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::BitXor; type Point { value: u32 } extend Point of BitXor { type Rhs = Point; type Output = Point; fn bitxor(self, rhs: Point) -> Point { Point { value: self.value ^ rhs.value } } } fn take(value: Point) {} fn main() -> u32 { let left := Point { value: 12 }; let right := Point { value: 10 }; let result := left ^ right; take(right); result.value }",
    );
    let diagnostic = err(f.run(&["ownership-project"]), "BE001");
    assert!(diagnostic.contains("right"), "{diagnostic}");
}

#[test]
fn user_defined_bitxor_evaluates_operands_left_to_right() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitxor-order'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::BitXor; type Point { value: u32 } extend Point of BitXor { type Rhs = Point; type Output = Point; fn bitxor(self, rhs: Point) -> Point { Point { value: self.value ^ rhs.value } } } fn main() -> u32 { var order: u32 = 0; let result := { order = order * 10 + 1; Point { value: 12 } } ^ { if order != 1 { return 0; } order = order * 10 + 2; Point { value: 10 } }; if order != 12 { return 0; } result.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(6)\n");
    let build = f.run(&["build", "--output", "bitxor-order.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitxor-order.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(6)\n");
}

#[test]
fn user_defined_shl_supports_heterogeneous_generic_operands_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='shl-interface'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::Shl; type Left { value: u32 } type Right { value: u32 } type MergeResult { value: u32 } extend Left of Shl { type Rhs = Right; type Output = MergeResult; fn shl(self, rhs: Right) -> MergeResult { MergeResult { value: self.value << rhs.value } } } fn merge<T>(lhs: T, operand: T::Rhs) -> T::Output where T: Shl { lhs << operand } fn main() -> u32 { let result: MergeResult = merge(Left { value: 12 }, Right { value: 10 }); result.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(12288)\n");
    let build = f.run(&["build", "--output", "shl-interface.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shl-interface.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(12288)\n");
}

#[test]
fn user_defined_shl_rejects_wrong_rhs_and_missing_implementation() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='shl-selection'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::Shl; type Left {} type Right {} type Other {} type Output { value: u32 } extend Left of Shl { type Rhs = Right; type Output = Output; fn shl(self, rhs: Right) -> Output { Output { value: 42 } } } fn main() -> u32 { let result := Left {} << Other {}; result.value }");
    let wrong = err(f.run(&["analyze-project"]), "TE007");
    assert!(wrong.contains("Shl requires an owned receiver"), "{wrong}");
    f.write("src/main.mb", "use core::ops::Shl; type Left {} type Right {} fn main() -> u32 { let result := Left {} << Right {}; 0 }");
    let missing = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        missing.contains("no visible Shl implementation"),
        "{missing}"
    );

    f.write("src/main.mb", "use core::ops::Shl; type Left {} type Right {} type Output { value: u32 } extend Left of Shl { type Rhs = Right; type Output = Output; fn shl(self, rhs: Right) -> Output { Output { value: 20 } } } extend Left of Shl { type Rhs = Right; type Output = Output; fn shl(self, rhs: Right) -> Output { Output { value: 22 } } } fn main() -> u32 { let result := Left {} << Right {}; result.value }");
    let ambiguous = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        ambiguous.contains("ambiguous Shl implementation"),
        "{ambiguous}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::Shl; pub type Left {} pub type Right {} pub type Output { pub value: u32 } fn main() -> u32 { let result := Left {} << Right {}; result.value }");
    f.write("src/other.mb", "use self::main::Left; use self::main::Right; use self::main::Output; pub fn marker() {} pub extend Left of core::ops::Shl { type Rhs = Right; type Output = Output; fn shl(self, rhs: Right) -> Output { Output { value: 42 } } }");
    let inactive = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        inactive.contains("no visible Shl implementation"),
        "{inactive}"
    );
}

#[test]
fn user_defined_shl_consumes_owned_operands_and_unwinds_rhs_early_return() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='shl-move'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::Shl; type Point { value: u32 } extend Point of Shl { type Rhs = Point; type Output = Point; fn shl(self, rhs: Point) -> Point { Point { value: self.value << rhs.value } } } fn take(value: Point) {} fn main() -> u32 { let left := Point { value: 12 }; let right := Point { value: 10 }; let result := left << right; take(left); result.value }");
    let moved = err(f.run(&["ownership-project"]), "BE001");
    assert!(moved.contains("left"), "{moved}");
    f.write("src/main.mb", "use core::ops::Shl; type Point { value: u32 } extend Point of Shl { type Rhs = Point; type Output = Point; fn shl(self, rhs: Point) -> Point { Point { value: self.value << rhs.value } } } fn take(value: Point) {} fn main() -> u32 { let left := Point { value: 12 }; let right := Point { value: 10 }; let result := left << right; take(right); result.value }");
    let moved_rhs = err(f.run(&["ownership-project"]), "BE001");
    assert!(moved_rhs.contains("right"), "{moved_rhs}");
    f.write("src/main.mb", "use core::ops::Shl; type Point { value: u32 } extend Point of Shl { type Rhs = Point; type Output = Point; fn shl(self, rhs: Point) -> Point { Point { value: self.value << rhs.value } } } fn main() -> u32 { let left := Point { value: 12 }; let result := left << { return 42; Point { value: 10 } }; result.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(42)\n");
    let build = f.run(&["build", "--output", "shl-early-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shl-early-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(42)\n");
}

#[test]
fn user_defined_shl_consumes_rhs_operand() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='shl-rhs-move'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Shl; type Point { value: u32 } extend Point of Shl { type Rhs = Point; type Output = Point; fn shl(self, rhs: Point) -> Point { Point { value: self.value << rhs.value } } } fn take(value: Point) {} fn main() -> u32 { let left := Point { value: 12 }; let right := Point { value: 10 }; let result := left << right; take(right); result.value }",
    );
    let diagnostic = err(f.run(&["ownership-project"]), "BE001");
    assert!(diagnostic.contains("right"), "{diagnostic}");
}

#[test]
fn user_defined_shl_evaluates_operands_left_to_right() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='shl-order'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::Shl; type Point { value: u32 } extend Point of Shl { type Rhs = Point; type Output = Point; fn shl(self, rhs: Point) -> Point { Point { value: self.value << rhs.value } } } fn main() -> u32 { var order: u32 = 0; let result := { order = order * 10 + 1; Point { value: 12 } } << { if order != 1 { return 0; } order = order * 10 + 2; Point { value: 10 } }; if order != 12 { return 0; } result.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(12288)\n");
    let build = f.run(&["build", "--output", "shl-order.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shl-order.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(12288)\n");
}

#[test]
fn user_defined_neg_supports_nominal_owned_receiver_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='neg-interface'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::Neg; type Input { value: i32 } type Output { value: i32 } extend Input of Neg { type Output = Output; fn neg(self) -> Output { Output { value: -self.value } } } fn main() -> i32 { let result := -Input { value: 5 }; result.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(-5)\n");
    let build = f.run(&["build", "--output", "neg-interface.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "neg-interface.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(-5)\n");
}

#[test]
fn user_defined_neg_rejects_missing_implementation_and_consumes_receiver() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='neg-selection'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "type Input {} fn main() -> i32 { let result := -Input {}; 0 }",
    );
    let missing = f.run(&["run"]);
    assert!(!missing.status.success(), "{missing:?}");
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("no visible Neg implementation"),
        "{missing:?}"
    );

    f.write("src/main.mb", "use core::ops::Neg; type Input { value: i32 } type Output { value: i32 } extend Input of Neg { type Output = Output; fn neg(self) -> Output { Output { value: -self.value } } } fn take(value: Input) {} fn main() -> i32 { let input := Input { value: 5 }; let result := -input; take(input); result.value }");
    let moved = f.run(&["run"]);
    assert!(!moved.status.success(), "{moved:?}");
}

#[test]
fn user_defined_neg_rejects_inactive_private_and_ambiguous_implementations() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='neg-visibility'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use other::marker; use core::ops::Neg; pub type Input {} pub type Output { pub value: i32 } fn main() -> i32 { let result := -Input {}; result.value }");
    f.write("src/other.mb", "use self::main::Input; use self::main::Output; pub fn marker() {} pub extend Input of core::ops::Neg { type Output = Output; fn neg(self) -> Output { Output { value: 42 } } }");
    let inactive = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        inactive.contains("no visible Neg implementation"),
        "{inactive}"
    );

    f.write("src/main.mb", "use other; use core::ops::Neg; pub type Input {} pub type Output { pub value: i32 } fn main() -> i32 { let result := -Input {}; result.value }");
    f.write("src/other.mb", "use self::main::Input; use self::main::Output; pub fn marker() {} extend Input of core::ops::Neg { type Output = Output; fn neg(self) -> Output { Output { value: 42 } } }");
    let private = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        private.contains("matching Neg implementation is private or inactive"),
        "{private}"
    );

    f.write("src/main.mb", "use core::ops::Neg; type Input {} type Output { value: i32 } extend Input of Neg { type Output = Output; fn neg(self) -> Output { Output { value: 20 } } } extend Input of Neg { type Output = Output; fn neg(self) -> Output { Output { value: 22 } } } fn main() -> i32 { let result := -Input {}; result.value }");
    let ambiguous = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        ambiguous.contains("ambiguous Neg implementation for `-`"),
        "{ambiguous}"
    );
}

#[test]
fn user_defined_neg_evaluates_operand_once_and_primitive_negation_stays_builtin() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='neg-order'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::Neg; type Input { value: i32 } type Output { value: i32 } extend Input of Neg { type Output = Output; fn neg(self) -> Output { Output { value: -self.value } } } fn main() -> i32 { var count: i32 = 0; let result := -{ count = count + 1; Input { value: 5 } }; if count != 1 { return 0; } result.value + -2 }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(-7)\n");
    let build = f.run(&["build", "--output", "neg-order.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "neg-order.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(-7)\n");
}

#[test]
fn user_defined_shr_supports_heterogeneous_generic_operands_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='shr-interface'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::Shr; type Left { value: u32 } type Right { value: u32 } type MergeResult { value: u32 } extend Left of Shr { type Rhs = Right; type Output = MergeResult; fn shr(self, rhs: Right) -> MergeResult { MergeResult { value: self.value >> rhs.value } } } fn merge<T>(lhs: T, operand: T::Rhs) -> T::Output where T: Shr { lhs >> operand } fn main() -> u32 { let result: MergeResult = merge(Left { value: 12 }, Right { value: 2 }); result.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(3)\n");
    let build = f.run(&["build", "--output", "shr-interface.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shr-interface.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(3)\n");
}

#[test]
fn user_defined_shr_rejects_wrong_rhs_and_missing_implementation() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='shr-selection'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::Shr; type Left {} type Right {} type Other {} type Output { value: u32 } extend Left of Shr { type Rhs = Right; type Output = Output; fn shr(self, rhs: Right) -> Output { Output { value: 42 } } } fn main() -> u32 { let result := Left {} >> Other {}; result.value }");
    let wrong = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        wrong.contains(
            "Shr requires an owned receiver and an owned operand matching its associated Rhs"
        ),
        "{wrong}"
    );
    f.write("src/main.mb", "use core::ops::Shr; type Left {} type Right {} fn main() -> u32 { let result := Left {} >> Right {}; 0 }");
    let missing = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        missing.contains("no visible Shr implementation"),
        "{missing}"
    );

    f.write("src/main.mb", "use core::ops::Shr; type Left {} type Right {} type Output { value: u32 } extend Left of Shr { type Rhs = Right; type Output = Output; fn shr(self, rhs: Right) -> Output { Output { value: 20 } } } extend Left of Shr { type Rhs = Right; type Output = Output; fn shr(self, rhs: Right) -> Output { Output { value: 22 } } } fn main() -> u32 { let result := Left {} >> Right {}; result.value }");
    let ambiguous = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        ambiguous.contains("ambiguous Shr implementation"),
        "{ambiguous}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::Shr; pub type Left {} pub type Right {} pub type Output { pub value: u32 } fn main() -> u32 { let result := Left {} >> Right {}; result.value }");
    f.write("src/other.mb", "use self::main::Left; use self::main::Right; use self::main::Output; pub fn marker() {} pub extend Left of core::ops::Shr { type Rhs = Right; type Output = Output; fn shr(self, rhs: Right) -> Output { Output { value: 42 } } }");
    let inactive = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        inactive.contains("no visible Shr implementation"),
        "{inactive}"
    );
}

#[test]
fn user_defined_shr_consumes_owned_operands_and_unwinds_rhs_early_return() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='shr-move'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::Shr; type Point { value: u32 } extend Point of Shr { type Rhs = Point; type Output = Point; fn shr(self, rhs: Point) -> Point { Point { value: self.value >> rhs.value } } } fn take(value: Point) {} fn main() -> u32 { let left := Point { value: 12 }; let right := Point { value: 2 }; let result := left >> right; take(left); result.value }");
    let moved = err(f.run(&["ownership-project"]), "BE001");
    assert!(moved.contains("left"), "{moved}");
    f.write("src/main.mb", "use core::ops::Shr; type Point { value: u32 } extend Point of Shr { type Rhs = Point; type Output = Point; fn shr(self, rhs: Point) -> Point { Point { value: self.value >> rhs.value } } } fn take(value: Point) {} fn main() -> u32 { let left := Point { value: 12 }; let right := Point { value: 2 }; let result := left >> right; take(right); result.value }");
    let moved_rhs = err(f.run(&["ownership-project"]), "BE001");
    assert!(moved_rhs.contains("right"), "{moved_rhs}");
    f.write("src/main.mb", "use core::ops::Shr; type Point { value: u32 } extend Point of Shr { type Rhs = Point; type Output = Point; fn shr(self, rhs: Point) -> Point { Point { value: self.value >> rhs.value } } } fn main() -> u32 { let left := Point { value: 12 }; let result := left >> { return 42; Point { value: 2 } }; result.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(42)\n");
    let build = f.run(&["build", "--output", "shr-early-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shr-early-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(42)\n");
}

#[test]
fn user_defined_shr_consumes_rhs_operand() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='shr-rhs-move'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Shr; type Point { value: u32 } extend Point of Shr { type Rhs = Point; type Output = Point; fn shr(self, rhs: Point) -> Point { Point { value: self.value >> rhs.value } } } fn take(value: Point) {} fn main() -> u32 { let left := Point { value: 12 }; let right := Point { value: 2 }; let result := left >> right; take(right); result.value }",
    );
    let diagnostic = err(f.run(&["ownership-project"]), "BE001");
    assert!(diagnostic.contains("right"), "{diagnostic}");
}

#[test]
fn user_defined_shr_evaluates_operands_left_to_right() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='shr-order'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::Shr; type Point { value: u32 } extend Point of Shr { type Rhs = Point; type Output = Point; fn shr(self, rhs: Point) -> Point { Point { value: self.value >> rhs.value } } } fn main() -> u32 { var order: u32 = 0; let result := { order = order * 10 + 1; Point { value: 12 } } >> { if order != 1 { return 0; } order = order * 10 + 2; Point { value: 2 } }; if order != 12 { return 0; } result.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(3)\n");
    let build = f.run(&["build", "--output", "shr-order.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shr-order.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(3)\n");
}

#[test]
fn user_defined_ordering_borrows_receiver_and_runs_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='partial-ord'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::PartialOrd; type Key { value: u32 } type Other { value: u32 } extend Key of PartialOrd { type Rhs = Other; fn lt(borrow self, rhs: Other) -> bool { self.value < rhs.value } fn le(borrow self, rhs: Other) -> bool { self.value <= rhs.value } fn gt(borrow self, rhs: Other) -> bool { self.value > rhs.value } fn ge(borrow self, rhs: Other) -> bool { self.value >= rhs.value } } fn before<T>(lhs: T, rhs: T::Rhs) -> bool where T: PartialOrd { lhs < rhs } fn main() -> u32 { var order: u32 = 0; let base := { order = 1; Key { value: 10 } }; let gt_left := Key { value: 11 }; let rhs11 := Other { value: 11 }; let rhs10 := Other { value: 10 }; let rhs10d := Other { value: 10 }; let rhs10b := Other { value: 10 }; let rhs9 := Other { value: 9 }; let rhs11b := Other { value: 11 }; let rhs10c := Other { value: 10 }; let rhs11c := Other { value: 11 }; let one := Key { value: 1 }; let two := Other { value: 2 }; let tests := base < rhs11 && !(base < rhs10) && base <= rhs10b && !(base <= rhs9) && gt_left > rhs10d && !(gt_left > rhs11b) && base >= rhs10c && !(base >= rhs11c) && before(one, two); if !tests { return 0; } if order != 1 || base.value != 10 { return 0; } 42 }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(42)\n");
    let build = f.run(&["build", "--output", "partial-ord.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "partial-ord.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(42)\n");

    f.write("src/main.mb", "use core::ops::PartialOrd; type Key {} type Other {} extend Key of PartialOrd { type Rhs = Key; fn lt(borrow self, rhs: Key) -> bool { true } fn le(borrow self, rhs: Key) -> bool { true } fn gt(borrow self, rhs: Key) -> bool { true } fn ge(borrow self, rhs: Key) -> bool { true } } fn main() -> bool { Key {} < Other {} }");
    let wrong_rhs = err(f.run(&["analyze-project"]), "TE007");
    assert!(wrong_rhs.contains("PartialOrd requires"), "{wrong_rhs}");
    f.write(
        "src/main.mb",
        "type Key {} fn main() -> bool { Key {} < Key {} }",
    );
    let missing = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        missing.contains("no visible PartialOrd implementation"),
        "{missing}"
    );
    f.write("src/main.mb", "use core::ops::PartialOrd; type Key { value: u32 } extend Key of PartialOrd { type Rhs = Key; fn lt(borrow self, rhs: Key) -> bool { true } fn le(borrow self, rhs: Key) -> bool { true } fn gt(borrow self, rhs: Key) -> bool { true } fn ge(borrow self, rhs: Key) -> bool { true } } fn main() -> u32 { let left := Key { value: 1 }; let right := Key { value: 2 }; let _less := left < right; right.value }");
    let moved_rhs = err(f.run(&["ownership-project"]), "BE001");
    assert!(moved_rhs.contains("right"), "{moved_rhs}");
    f.write("src/main.mb", "use core::ops::PartialOrd; type Key {} extend Key of PartialOrd { type Rhs = Key; fn lt(borrow self, rhs: Key) -> bool { true } fn le(borrow self, rhs: Key) -> bool { true } fn gt(borrow self, rhs: Key) -> bool { true } fn ge(borrow self, rhs: Key) -> bool { true } } extend Key of PartialOrd { type Rhs = Key; fn lt(borrow self, rhs: Key) -> bool { false } fn le(borrow self, rhs: Key) -> bool { false } fn gt(borrow self, rhs: Key) -> bool { false } fn ge(borrow self, rhs: Key) -> bool { false } } fn main() -> bool { Key {} < Key {} }");
    let ambiguous = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        ambiguous.contains("ambiguous PartialOrd implementation for `<`"),
        "{ambiguous}"
    );
    f.write("src/main.mb", "use other; use core::ops::PartialOrd; pub type Key { value: u32 } fn main() -> bool { Key { value: 1 } < Key { value: 2 } }");
    f.write("src/other.mb", "use self::main::Key; pub fn marker() {} extend Key of core::ops::PartialOrd { type Rhs = Key; fn lt(borrow self, rhs: Key) -> bool { true } fn le(borrow self, rhs: Key) -> bool { true } fn gt(borrow self, rhs: Key) -> bool { true } fn ge(borrow self, rhs: Key) -> bool { true } }");
    let private = err(f.run(&["analyze-project"]), "TE007");
    assert!(private.contains("private or inactive"), "{private}");
    f.write("src/main.mb", "use other::marker; use core::ops::PartialOrd; pub type Key { value: u32 } fn main() -> bool { Key { value: 1 } < Key { value: 2 } }");
    f.write("src/other.mb", "use self::main::Key; pub fn marker() {} pub extend Key of core::ops::PartialOrd { type Rhs = Key; fn lt(borrow self, rhs: Key) -> bool { true } fn le(borrow self, rhs: Key) -> bool { true } fn gt(borrow self, rhs: Key) -> bool { true } fn ge(borrow self, rhs: Key) -> bool { true } }");
    let inactive = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        inactive.contains("no visible PartialOrd implementation"),
        "{inactive}"
    );
    f.write("src/main.mb", "use core::ops::PartialOrd; type Key {} extend Key of PartialOrd { type Rhs = Key; fn lt(borrow self, rhs: Key) -> bool { true } fn le(borrow self, rhs: Key) -> bool { true } fn gt(borrow self, rhs: Key) -> bool { true } fn ge(borrow self, rhs: Key) -> u32 { 1 } } fn main() -> bool { Key {} < Key {} }");
    let wrong_signature = err(f.run(&["analyze-project"]), "ME005");
    assert!(wrong_signature.contains("bool"), "{wrong_signature}");
}

#[test]
fn user_defined_add_assign_mutates_nominal_target_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='add-assign'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::AddAssign; type Counter { value: u32 } type Wrapper { item: Counter } extend Counter of AddAssign { type Rhs = u32; fn add_assign(share self, rhs: u32) { self.value += rhs; } } fn next_index(c: share u32) -> u32 { c += 1; 0 } fn main() -> u32 { var counter := Counter { value: 4 }; counter += 3; counter += 5; var wrapper := Wrapper { item: Counter { value: 1 } }; wrapper.item += 2; var index_calls: u32 = 0; var items := [Counter { value: 2 }, Counter { value: 3 }]; items[next_index(index_calls.share())] += 2; if index_calls == 1 { counter.value + wrapper.item.value + items[0].value } else { 0 } }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(19)\n");
    let build = f.run(&["build", "--output", "add-assign.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "add-assign.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(19)\n");

    f.write("src/main.mb", "use core::ops::AddAssign; type Counter { value: u32 } type Delta { value: u32 } extend Counter of AddAssign { type Rhs = Delta; fn add_assign(share self, rhs: Delta) { self.value += rhs.value; } } fn update<T>(target: T, rhs: T::Rhs) -> T where T: AddAssign { var value := target; value += rhs; value } fn main() -> u32 { let result := update(Counter { value: 7 }, Delta { value: 5 }); result.value }");
    let generic = f.run(&["run"]);
    assert!(generic.status.success(), "{generic:?}");
    assert_eq!(generic.stdout, b"Result: u32(12)\n");
    let generic_build = f.run(&["build", "--output", "add-assign-generic.wasm"]);
    assert!(generic_build.status.success(), "{generic_build:?}");
    let generic_artifact = f.run(&["run", "add-assign-generic.wasm"]);
    assert!(generic_artifact.status.success(), "{generic_artifact:?}");
    assert_eq!(generic_artifact.stdout, b"Result: i32(12)\n");

    f.write("src/main.mb", "use core::ops::AddAssign; type Plain { value: u32 } fn update<T>(target: T, rhs: T::Rhs) -> T where T: AddAssign { var value := target; value += rhs; value } fn main() -> u32 { let result := update(Plain { value: 7 }, 5); result.value }");
    let missing_evidence = f.run(&["analyze-project"]);
    assert!(!missing_evidence.status.success(), "{missing_evidence:?}");
    assert!(
        String::from_utf8_lossy(&missing_evidence.stderr)
            .contains("no visible implementation of 'core::ops::AddAssign'"),
        "{missing_evidence:?}"
    );

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var value: u32 = 7; value += 5; value }",
    );
    let primitive = f.run(&["run"]);
    assert!(primitive.status.success(), "{primitive:?}");
    assert_eq!(primitive.stdout, b"Result: u32(12)\n");
    let primitive_build = f.run(&["build", "--output", "add-assign-primitive.wasm"]);
    assert!(primitive_build.status.success(), "{primitive_build:?}");
    let primitive_artifact = f.run(&["run", "add-assign-primitive.wasm"]);
    assert!(
        primitive_artifact.status.success(),
        "{primitive_artifact:?}"
    );
    assert_eq!(primitive_artifact.stdout, b"Result: i32(12)\n");

    f.write("src/main.mb", "use core::ops::AddAssign; type Counter { value: u32 } extend Counter of AddAssign { type Rhs = u32; fn add_assign(share self, rhs: u32) { self.value += rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter += { return 9; 5 }; counter.value }");
    let early_return = f.run(&["run"]);
    assert!(early_return.status.success(), "{early_return:?}");
    assert_eq!(early_return.stdout, b"Result: u32(9)\n");
    let early_build = f.run(&["build", "--output", "add-assign-return.wasm"]);
    assert!(early_build.status.success(), "{early_build:?}");
    let early_wasm = f.run(&["run", "add-assign-return.wasm"]);
    assert!(early_wasm.status.success(), "{early_wasm:?}");
    assert_eq!(early_wasm.stdout, b"Result: i32(9)\n");

    // The indexed place is captured before RHS evaluation. Returning from the
    // RHS block must skip AddAssign and its deliberate dynamic divide-by-zero.
    f.write("src/main.mb", "use core::ops::AddAssign; type Counter { value: u32 } extend Counter of AddAssign { type Rhs = u32; fn add_assign(share self, rhs: u32) { self.value += 10 / rhs; } } fn index(calls: share u32) -> u32 { calls += 1; 0 } fn main() -> u32 { var calls: u32 = 0; var items := [Counter { value: 4 }]; items[index(calls.share())] += { return 11; 0 }; 0 }");
    let indexed_early_return = f.run(&["run"]);
    assert!(
        indexed_early_return.status.success(),
        "{indexed_early_return:?}"
    );
    assert_eq!(indexed_early_return.stdout, b"Result: u32(11)\n");
    let indexed_build = f.run(&["build", "--output", "add-assign-indexed-return.wasm"]);
    assert!(indexed_build.status.success(), "{indexed_build:?}");
    let indexed_wasm = f.run(&["run", "add-assign-indexed-return.wasm"]);
    assert!(indexed_wasm.status.success(), "{indexed_wasm:?}");
    assert_eq!(indexed_wasm.stdout, b"Result: i32(11)\n");

    // A field-projected target must also skip the method when RHS evaluation
    // returns from the enclosing function.
    f.write("src/main.mb", "use core::ops::AddAssign; type Counter { value: u32 } type Wrapper { item: Counter } extend Counter of AddAssign { type Rhs = u32; fn add_assign(share self, rhs: u32) { self.value += 10 / rhs; } } fn main() -> u32 { var wrapper := Wrapper { item: Counter { value: 4 } }; wrapper.item += { return 12; 0 }; 0 }");
    let field_early_return = f.run(&["run"]);
    assert!(
        field_early_return.status.success(),
        "{field_early_return:?}"
    );
    assert_eq!(field_early_return.stdout, b"Result: u32(12)\n");
    let field_build = f.run(&["build", "--output", "add-assign-field-return.wasm"]);
    assert!(field_build.status.success(), "{field_build:?}");
    let field_wasm = f.run(&["run", "add-assign-field-return.wasm"]);
    assert!(field_wasm.status.success(), "{field_wasm:?}");
    assert_eq!(field_wasm.stdout, b"Result: i32(12)\n");

    f.write("src/main.mb", "use core::ops::AddAssign; type Counter { value: u32 } extend Counter of AddAssign { type Rhs = bool; fn add_assign(share self, rhs: u32) { self.value += rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter += true; counter.value }");
    let wrong_signature = f.run(&["analyze-project"]);
    assert!(!wrong_signature.status.success(), "{wrong_signature:?}");
    assert!(
        String::from_utf8_lossy(&wrong_signature.stderr).contains("extension method 'add_assign'"),
        "{wrong_signature:?}"
    );

    f.write("src/main.mb", "use core::ops::AddAssign; type Counter { value: u32 } extend Counter of AddAssign { type Rhs = u32; fn add_assign(share self, rhs: u32) { self.value += rhs; } } fn read(c: share Counter) -> u32 { c.value += 1; c.value } fn main() -> u32 { var counter := Counter { value: 4 }; counter += read(counter.share()); counter.value }");
    f.write("src/main.mb", "use core::ops::BitAndAssign; type Bits { value: u32 } type Mask { value: u32 } extend Bits of BitAndAssign { type Rhs = Mask; fn bitand_assign(share self, rhs: Mask) { self.value &= rhs.value; } } fn read(bits: borrow Bits) -> Mask { Mask { value: bits.value } } fn main() -> u32 { var bits := Bits { value: 3 }; bits &= read(bits.borrow()); bits.value }");
    let alias = f.run(&["ownership-project"]);
    assert!(!alias.status.success(), "{alias:?}");
    assert!(
        String::from_utf8_lossy(&alias.stderr).contains("while it is shared"),
        "{alias:?}"
    );

    f.write("src/main.mb", "use core::ops::AddAssign; type Counter { value: u32 } fn main() -> u32 { var counter := Counter { value: 4 }; counter += 1; counter.value }");
    let missing = f.run(&["analyze-project"]);
    assert!(!missing.status.success(), "{missing:?}");
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("no visible AddAssign implementation"),
        "{missing:?}"
    );

    f.write("src/main.mb", "use core::ops::AddAssign; type Counter { value: u32 } extend Counter of AddAssign { type Rhs = u32; fn add_assign(share self, rhs: u32) { self.value += rhs; } } fn main() -> u32 { let counter := Counter { value: 4 }; counter += 1; counter.value }");
    let immutable = f.run(&["analyze-project"]);
    assert!(!immutable.status.success(), "{immutable:?}");

    f.write("src/main.mb", "use core::ops::AddAssign; type Counter { value: u32 } extend Counter of AddAssign { type Rhs = u32; fn add_assign(share self, rhs: u32) { self.value += rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter += true; counter.value }");
    let wrong_rhs = f.run(&["analyze-project"]);
    assert!(!wrong_rhs.status.success(), "{wrong_rhs:?}");

    f.write("src/main.mb", "use core::ops::AddAssign; type Counter { value: u32 } extend Counter of AddAssign { type Rhs = u32; fn add_assign(share self, rhs: u32) { self.value += rhs; } } extend Counter of AddAssign { type Rhs = u32; fn add_assign(share self, rhs: u32) { self.value += rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter += 1; counter.value }");
    let ambiguous = f.run(&["analyze-project"]);
    assert!(!ambiguous.status.success(), "{ambiguous:?}");
    assert!(
        String::from_utf8_lossy(&ambiguous.stderr).contains("ambiguous AddAssign"),
        "{ambiguous:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::AddAssign; pub type Counter { value: u32 } fn main() -> u32 { var counter := Counter { value: 4 }; counter += 1; counter.value }");
    f.write("src/other.mb", "use self::main::Counter; pub fn marker() {} pub extend Counter of core::ops::AddAssign { type Rhs = u32; fn add_assign(share self, rhs: u32) { self.value += rhs; } }");
    let inactive = f.run(&["analyze-project"]);
    assert!(!inactive.status.success(), "{inactive:?}");
    assert!(
        String::from_utf8_lossy(&inactive.stderr).contains("no visible AddAssign implementation"),
        "{inactive:?}"
    );
}

#[test]
fn user_defined_sub_assign_mutates_nominal_target_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='sub-assign'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::SubAssign; type Counter { value: u32 } type Delta { value: u32 } type Wrapper { item: Counter } extend Counter of SubAssign { type Rhs = Delta; fn sub_assign(share self, rhs: Delta) { self.value -= rhs.value; } } fn index(calls: share u32) -> u32 { calls += 1; 0 } fn main() -> u32 { var counter := Counter { value: 20 }; let d1 := Delta { value: 3 }; counter -= d1; var wrapper := Wrapper { item: Counter { value: 10 } }; let d2 := Delta { value: 2 }; wrapper.item -= d2; var calls: u32 = 0; var items := [Counter { value: 8 }]; let d3 := Delta { value: 1 }; items[index(calls.share())] -= d3; if calls == 1 { counter.value + wrapper.item.value + items[0].value } else { 0 } }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(32)\n");
    let build = f.run(&["build", "--output", "sub-assign.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "sub-assign.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(32)\n");

    f.write("src/main.mb", "use core::ops::SubAssign; type Counter { value: u32 } type Delta { value: u32 } extend Counter of SubAssign { type Rhs = Delta; fn sub_assign(share self, rhs: Delta) { self.value -= rhs.value; } } fn update<T>(target: T, rhs: T::Rhs) -> T where T: SubAssign { var value := target; value -= rhs; value } fn main() -> u32 { let result := update(Counter { value: 20 }, Delta { value: 7 }); result.value }");
    let generic = f.run(&["run"]);
    assert!(generic.status.success(), "{generic:?}");
    assert_eq!(generic.stdout, b"Result: u32(13)\n");
    let generic_build = f.run(&["build", "--output", "sub-assign-generic.wasm"]);
    assert!(generic_build.status.success(), "{generic_build:?}");
    let generic_artifact = f.run(&["run", "sub-assign-generic.wasm"]);
    assert!(generic_artifact.status.success(), "{generic_artifact:?}");
    assert_eq!(generic_artifact.stdout, b"Result: i32(13)\n");

    f.write("src/main.mb", "use core::ops::SubAssign; type Plain { value: u32 } fn update<T>(target: T, rhs: T::Rhs) -> T where T: SubAssign { var value := target; value -= rhs; value } fn main() -> u32 { let result := update(Plain { value: 20 }, 7); result.value }");
    let missing_evidence = f.run(&["analyze-project"]);
    assert!(!missing_evidence.status.success(), "{missing_evidence:?}");
    assert!(
        String::from_utf8_lossy(&missing_evidence.stderr)
            .contains("no visible implementation of 'core::ops::SubAssign'"),
        "{missing_evidence:?}"
    );

    f.write("src/main.mb", "use core::ops::SubAssign; type Counter { value: u32 } extend Counter of SubAssign { type Rhs = u32; fn sub_assign(share self, rhs: u32) { self.value -= rhs; } } fn update<T>(target: T, rhs: T::Rhs) -> T where T: SubAssign { var value := target; value -= rhs; value } fn main() -> u32 { let result := update(Counter { value: 20 }, true); result.value }");
    let generic_wrong_rhs = f.run(&["analyze-project"]);
    assert!(!generic_wrong_rhs.status.success(), "{generic_wrong_rhs:?}");

    f.write("src/main.mb", "use core::ops::SubAssign; type Counter { value: u32 } extend Counter of SubAssign { type Rhs = u32; fn sub_assign(share self, rhs: u32) { self.value -= 10 / rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter -= { return 13; 0 }; 0 }");
    let early = f.run(&["run"]);
    assert!(early.status.success(), "{early:?}");
    assert_eq!(early.stdout, b"Result: u32(13)\n");
    let build = f.run(&["build", "--output", "sub-assign-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "sub-assign-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(13)\n");

    f.write("src/main.mb", "use core::ops::SubAssign; type Counter { value: u32 } type Wrapper { item: Counter } extend Counter of SubAssign { type Rhs = u32; fn sub_assign(share self, rhs: u32) { self.value -= 10 / rhs; } } fn main() -> u32 { var wrapper := Wrapper { item: Counter { value: 4 } }; wrapper.item -= { return 14; 0 }; 0 }");
    let field_early = f.run(&["run"]);
    assert!(field_early.status.success(), "{field_early:?}");
    assert_eq!(field_early.stdout, b"Result: u32(14)\n");
    let build = f.run(&["build", "--output", "sub-assign-field-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "sub-assign-field-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(14)\n");

    f.write("src/main.mb", "use core::ops::SubAssign; type Counter { value: u32 } extend Counter of SubAssign { type Rhs = u32; fn sub_assign(share self, rhs: u32) { self.value -= 10 / rhs; } } fn index(calls: share u32) -> u32 { calls += 1; 0 } fn main() -> u32 { var calls: u32 = 0; var items := [Counter { value: 4 }]; items[index(calls.share())] -= { return 15; 0 }; 0 }");
    let index_early = f.run(&["run"]);
    assert!(index_early.status.success(), "{index_early:?}");
    assert_eq!(index_early.stdout, b"Result: u32(15)\n");
    let build = f.run(&["build", "--output", "sub-assign-index-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "sub-assign-index-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(15)\n");

    f.write("src/main.mb", "use core::ops::SubAssign; type Counter { value: u32 } fn main() -> u32 { var counter := Counter { value: 1 }; counter -= 2; counter.value }");
    let missing = f.run(&["analyze-project"]);
    assert!(!missing.status.success(), "{missing:?}");
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("no visible SubAssign implementation"),
        "{missing:?}"
    );

    f.write("src/main.mb", "use core::ops::SubAssign; type Counter { value: u32 } extend Counter of SubAssign { type Rhs = u32; fn sub_assign(share self, rhs: u32) { self.value -= rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter -= true; counter.value }");
    let wrong_rhs = f.run(&["analyze-project"]);
    assert!(!wrong_rhs.status.success(), "{wrong_rhs:?}");

    f.write("src/main.mb", "use core::ops::SubAssign; type Counter { value: u32 } extend Counter of SubAssign { type Rhs = u32; fn sub_assign(share self, rhs: u32) { self.value -= rhs; } } fn main() -> u32 { let counter := Counter { value: 4 }; counter -= 1; counter.value }");
    let immutable = f.run(&["analyze-project"]);
    assert!(!immutable.status.success(), "{immutable:?}");

    f.write("src/main.mb", "use core::ops::SubAssign; type Counter { value: u32 } extend Counter of SubAssign { type Rhs = u32; fn sub_assign(share self, rhs: u32) { self.value -= rhs; } } extend Counter of SubAssign { type Rhs = u32; fn sub_assign(share self, rhs: u32) { self.value -= rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter -= 1; counter.value }");
    let ambiguous = f.run(&["analyze-project"]);
    assert!(!ambiguous.status.success(), "{ambiguous:?}");
    assert!(
        String::from_utf8_lossy(&ambiguous.stderr).contains("ambiguous SubAssign"),
        "{ambiguous:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::SubAssign; pub type Counter { value: u32 } fn main() -> u32 { var counter := Counter { value: 4 }; counter -= 1; counter.value }");
    f.write("src/other.mb", "use self::main::Counter; pub fn marker() {} pub extend Counter of core::ops::SubAssign { type Rhs = u32; fn sub_assign(share self, rhs: u32) { self.value -= rhs; } }");
    let inactive = f.run(&["analyze-project"]);
    assert!(!inactive.status.success(), "{inactive:?}");
    assert!(
        String::from_utf8_lossy(&inactive.stderr).contains("no visible SubAssign implementation"),
        "{inactive:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::SubAssign; pub type Counter { value: u32 } fn main() -> u32 { var counter := Counter { value: 4 }; counter -= 1; counter.value }");
    f.write("src/other.mb", "use self::main::Counter; pub fn marker() {} extend Counter of core::ops::SubAssign { type Rhs = u32; fn sub_assign(share self, rhs: u32) { self.value -= rhs; } }");
    // Keep the imported module live while its implementation remains private.
    let private = f.run(&["analyze-project"]);
    assert!(!private.status.success(), "{private:?}");

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var value: u32 = 9; value -= 4; value }",
    );
    let primitive = f.run(&["run"]);
    assert!(primitive.status.success(), "{primitive:?}");
    assert_eq!(primitive.stdout, b"Result: u32(5)\n");
    let primitive_build = f.run(&["build", "--output", "sub-assign-primitive.wasm"]);
    assert!(primitive_build.status.success(), "{primitive_build:?}");
    let primitive_artifact = f.run(&["run", "sub-assign-primitive.wasm"]);
    assert!(
        primitive_artifact.status.success(),
        "{primitive_artifact:?}"
    );
    assert_eq!(primitive_artifact.stdout, b"Result: i32(5)\n");

    f.write("src/main.mb", "use core::ops::SubAssign; type Counter { value: u32 } extend Counter of SubAssign { type Rhs = u32; fn sub_assign(share self, rhs: u32) { self.value -= rhs; } } fn read(c: share Counter) -> u32 { c.value -= 1; c.value } fn main() -> u32 { var counter := Counter { value: 4 }; counter -= read(counter.share()); counter.value }");
    f.write("src/main.mb", "use core::ops::BitAndAssign; type Bits { value: u32 } type Mask { value: u32 } extend Bits of BitAndAssign { type Rhs = Mask; fn bitand_assign(share self, rhs: Mask) { self.value &= rhs.value; } } fn read(bits: borrow Bits) -> Mask { Mask { value: bits.value } } fn main() -> u32 { var bits := Bits { value: 3 }; bits &= read(bits.borrow()); bits.value }");
    let alias = f.run(&["ownership-project"]);
    assert!(!alias.status.success(), "{alias:?}");
    assert!(
        String::from_utf8_lossy(&alias.stderr).contains("while it is shared"),
        "{alias:?}"
    );
}

#[test]
fn user_defined_mul_assign_mutates_nominal_target_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='sub-assign'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::MulAssign; type Counter { value: u32 } type Delta { value: u32 } type Wrapper { item: Counter } extend Counter of MulAssign { type Rhs = Delta; fn mul_assign(share self, rhs: Delta) { self.value *= rhs.value; } } fn index(calls: share u32) -> u32 { calls += 1; 0 } fn main() -> u32 { var counter := Counter { value: 20 }; let d1 := Delta { value: 3 }; counter *= d1; var wrapper := Wrapper { item: Counter { value: 10 } }; let d2 := Delta { value: 2 }; wrapper.item *= d2; var calls: u32 = 0; var items := [Counter { value: 8 }]; let d3 := Delta { value: 1 }; items[index(calls.share())] *= d3; if calls == 1 { counter.value + wrapper.item.value + items[0].value } else { 0 } }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(88)\n");
    let build = f.run(&["build", "--output", "sub-assign.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "sub-assign.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(88)\n");

    f.write("src/main.mb", "use core::ops::MulAssign; type Counter { value: u32 } extend Counter of MulAssign { type Rhs = u32; fn mul_assign(share self, rhs: u32) { self.value *= 10 / rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter *= { return 13; 0 }; 0 }");
    let early = f.run(&["run"]);
    assert!(early.status.success(), "{early:?}");
    assert_eq!(early.stdout, b"Result: u32(13)\n");
    let build = f.run(&["build", "--output", "sub-assign-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "sub-assign-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(13)\n");

    f.write("src/main.mb", "use core::ops::MulAssign; type Counter { value: u32 } type Wrapper { item: Counter } extend Counter of MulAssign { type Rhs = u32; fn mul_assign(share self, rhs: u32) { self.value *= 10 / rhs; } } fn main() -> u32 { var wrapper := Wrapper { item: Counter { value: 4 } }; wrapper.item *= { return 14; 0 }; 0 }");
    let field_early = f.run(&["run"]);
    assert!(field_early.status.success(), "{field_early:?}");
    assert_eq!(field_early.stdout, b"Result: u32(14)\n");
    let build = f.run(&["build", "--output", "sub-assign-field-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "sub-assign-field-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(14)\n");

    f.write("src/main.mb", "use core::ops::MulAssign; type Counter { value: u32 } extend Counter of MulAssign { type Rhs = u32; fn mul_assign(share self, rhs: u32) { self.value *= 10 / rhs; } } fn index(calls: share u32) -> u32 { calls += 1; 0 } fn main() -> u32 { var calls: u32 = 0; var items := [Counter { value: 4 }]; items[index(calls.share())] *= { return 15; 0 }; 0 }");
    let index_early = f.run(&["run"]);
    assert!(index_early.status.success(), "{index_early:?}");
    assert_eq!(index_early.stdout, b"Result: u32(15)\n");
    let build = f.run(&["build", "--output", "sub-assign-index-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "sub-assign-index-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(15)\n");

    f.write("src/main.mb", "use core::ops::MulAssign; type Counter { value: u32 } fn main() -> u32 { var counter := Counter { value: 1 }; counter *= 2; counter.value }");
    let missing = f.run(&["analyze-project"]);
    assert!(!missing.status.success(), "{missing:?}");
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("no visible MulAssign implementation"),
        "{missing:?}"
    );

    f.write("src/main.mb", "use core::ops::MulAssign; type Counter { value: u32 } extend Counter of MulAssign { type Rhs = u32; fn mul_assign(share self, rhs: u32) { self.value *= rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter *= true; counter.value }");
    let wrong_rhs = f.run(&["analyze-project"]);
    assert!(!wrong_rhs.status.success(), "{wrong_rhs:?}");

    f.write("src/main.mb", "use core::ops::MulAssign; type Counter { value: u32 } type Delta { value: u32 } extend Counter of MulAssign { type Rhs = Delta; fn mul_assign(share self, rhs: Delta) { self.value *= rhs.value; } } fn scale<T>(initial: T, rhs: T::Rhs) -> T where T: MulAssign { var value := initial; value *= rhs; value } fn main() -> u32 { let result := scale(Counter { value: 7 }, Delta { value: 6 }); result.value }");
    let generic = f.run(&["run"]);
    assert!(generic.status.success(), "{generic:?}");
    assert_eq!(generic.stdout, b"Result: u32(42)\n");
    let generic_build = f.run(&["build", "--output", "mul-assign-generic.wasm"]);
    assert!(generic_build.status.success(), "{generic_build:?}");
    let generic_artifact = f.run(&["run", "mul-assign-generic.wasm"]);
    assert!(generic_artifact.status.success(), "{generic_artifact:?}");
    assert_eq!(generic_artifact.stdout, b"Result: i32(42)\n");

    f.write("src/main.mb", "use core::ops::MulAssign; type Counter { value: u32 } type Delta { value: u32 } extend Counter of MulAssign { type Rhs = Delta; fn mul_assign(share self, rhs: Delta) { self.value *= rhs.value; } } fn scale<T>(initial: T, rhs: T::Rhs) -> T where T: MulAssign { var value := initial; value *= rhs; value } fn main() -> u32 { let rhs := Delta { value: 6 }; let result := scale(Counter { value: 7 }, rhs); rhs.value + result.value }");
    let moved_rhs = f.run(&["ownership-project"]);
    assert!(!moved_rhs.status.success(), "{moved_rhs:?}");
    assert!(
        String::from_utf8_lossy(&moved_rhs.stderr).contains("rhs"),
        "{moved_rhs:?}"
    );

    f.write("src/main.mb", "use core::ops::MulAssign; type Plain { value: u32 } fn scale<T>(initial: T, rhs: T::Rhs) -> T where T: MulAssign { var value := initial; value *= rhs; value } fn main() -> u32 { let result := scale(Plain { value: 7 }, 6); result.value }");
    let missing_generic = f.run(&["analyze-project"]);
    assert!(!missing_generic.status.success(), "{missing_generic:?}");
    assert!(
        String::from_utf8_lossy(&missing_generic.stderr)
            .contains("no visible implementation of 'core::ops::MulAssign'"),
        "{missing_generic:?}"
    );

    f.write("src/main.mb", "use core::ops::MulAssign; type Counter { value: u32 } extend Counter of MulAssign { type Rhs = u32; fn mul_assign(share self, rhs: u32) { self.value *= rhs; } } fn scale<T>(initial: T, rhs: T::Rhs) -> T where T: MulAssign { var value := initial; value *= rhs; value } fn main() -> u32 { let result := scale(Counter { value: 7 }, true); result.value }");
    let wrong_generic_rhs = f.run(&["analyze-project"]);
    assert!(!wrong_generic_rhs.status.success(), "{wrong_generic_rhs:?}");

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var value: u32 = 7; value *= 6; value }",
    );
    let primitive = f.run(&["run"]);
    assert!(primitive.status.success(), "{primitive:?}");
    assert_eq!(primitive.stdout, b"Result: u32(42)\n");
    let primitive_build = f.run(&["build", "--output", "mul-assign-primitive.wasm"]);
    assert!(primitive_build.status.success(), "{primitive_build:?}");
    let primitive_artifact = f.run(&["run", "mul-assign-primitive.wasm"]);
    assert!(
        primitive_artifact.status.success(),
        "{primitive_artifact:?}"
    );
    assert_eq!(primitive_artifact.stdout, b"Result: i32(42)\n");

    f.write("src/main.mb", "use core::ops::MulAssign; type Counter { value: u32 } extend Counter of MulAssign { type Rhs = u32; fn mul_assign(share self, rhs: u32) { self.value *= rhs; } } fn main() -> u32 { let counter := Counter { value: 4 }; counter *= 1; counter.value }");
    let immutable = f.run(&["analyze-project"]);
    assert!(!immutable.status.success(), "{immutable:?}");

    f.write("src/main.mb", "use core::ops::MulAssign; type Counter { value: u32 } extend Counter of MulAssign { type Rhs = u32; fn mul_assign(share self, rhs: u32) { self.value *= rhs; } } extend Counter of MulAssign { type Rhs = u32; fn mul_assign(share self, rhs: u32) { self.value *= rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter *= 1; counter.value }");
    let ambiguous = f.run(&["analyze-project"]);
    assert!(!ambiguous.status.success(), "{ambiguous:?}");
    assert!(
        String::from_utf8_lossy(&ambiguous.stderr).contains("ambiguous MulAssign"),
        "{ambiguous:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::MulAssign; pub type Counter { value: u32 } fn main() -> u32 { var counter := Counter { value: 4 }; counter *= 1; counter.value }");
    f.write("src/other.mb", "use self::main::Counter; pub fn marker() {} pub extend Counter of core::ops::MulAssign { type Rhs = u32; fn mul_assign(share self, rhs: u32) { self.value *= rhs; } }");
    let inactive = f.run(&["analyze-project"]);
    assert!(!inactive.status.success(), "{inactive:?}");
    assert!(
        String::from_utf8_lossy(&inactive.stderr).contains("no visible MulAssign implementation"),
        "{inactive:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::MulAssign; pub type Counter { value: u32 } fn main() -> u32 { var counter := Counter { value: 4 }; counter *= 1; counter.value }");
    f.write("src/other.mb", "use self::main::Counter; pub fn marker() {} extend Counter of core::ops::MulAssign { type Rhs = u32; fn mul_assign(share self, rhs: u32) { self.value *= rhs; } }");
    // Keep the imported module live while its implementation remains private.
    let private = f.run(&["analyze-project"]);
    assert!(!private.status.success(), "{private:?}");

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var value: u32 = 9; value *= 4; value }",
    );
    let primitive = f.run(&["run"]);
    assert!(primitive.status.success(), "{primitive:?}");
    assert_eq!(primitive.stdout, b"Result: u32(36)\n");

    f.write("src/main.mb", "use core::ops::MulAssign; type Counter { value: u32 } extend Counter of MulAssign { type Rhs = u32; fn mul_assign(share self, rhs: u32) { self.value *= rhs; } } fn read(c: share Counter) -> u32 { c.value *= 1; c.value } fn main() -> u32 { var counter := Counter { value: 4 }; counter *= read(counter.share()); counter.value }");
    f.write("src/main.mb", "use core::ops::BitAndAssign; type Bits { value: u32 } type Mask { value: u32 } extend Bits of BitAndAssign { type Rhs = Mask; fn bitand_assign(share self, rhs: Mask) { self.value &= rhs.value; } } fn read(bits: borrow Bits) -> Mask { Mask { value: bits.value } } fn main() -> u32 { var bits := Bits { value: 3 }; bits &= read(bits.borrow()); bits.value }");
    let alias = f.run(&["ownership-project"]);
    assert!(!alias.status.success(), "{alias:?}");
    assert!(
        String::from_utf8_lossy(&alias.stderr).contains("while it is shared"),
        "{alias:?}"
    );
}

#[test]
fn user_defined_div_assign_mutates_nominal_target_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='div-assign'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::DivAssign; type Counter { value: u32 } type Delta { value: u32 } type Wrapper { item: Counter } extend Counter of DivAssign { type Rhs = Delta; fn div_assign(share self, rhs: Delta) { self.value /= rhs.value; } } fn index(calls: share u32) -> u32 { calls += 1; 0 } fn main() -> u32 { var counter := Counter { value: 20 }; let d1 := Delta { value: 3 }; counter /= d1; var wrapper := Wrapper { item: Counter { value: 10 } }; let d2 := Delta { value: 2 }; wrapper.item /= d2; var calls: u32 = 0; var items := [Counter { value: 8 }]; let d3 := Delta { value: 1 }; items[index(calls.share())] /= d3; if calls == 1 { counter.value + wrapper.item.value + items[0].value } else { 0 } }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(19)\n");
    let build = f.run(&["build", "--output", "div-assign.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "div-assign.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(19)\n");

    f.write("src/main.mb", "use core::ops::DivAssign; type Counter { value: u32 } extend Counter of DivAssign { type Rhs = u32; fn div_assign(share self, rhs: u32) { self.value /= 10 / rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter /= { return 13; 0 }; 0 }");
    let early = f.run(&["run"]);
    assert!(early.status.success(), "{early:?}");
    assert_eq!(early.stdout, b"Result: u32(13)\n");
    let build = f.run(&["build", "--output", "div-assign-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "div-assign-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(13)\n");

    f.write("src/main.mb", "use core::ops::DivAssign; type Counter { value: u32 } type Wrapper { item: Counter } extend Counter of DivAssign { type Rhs = u32; fn div_assign(share self, rhs: u32) { self.value /= 10 / rhs; } } fn main() -> u32 { var wrapper := Wrapper { item: Counter { value: 4 } }; wrapper.item /= { return 14; 0 }; 0 }");
    let field_early = f.run(&["run"]);
    assert!(field_early.status.success(), "{field_early:?}");
    assert_eq!(field_early.stdout, b"Result: u32(14)\n");
    let build = f.run(&["build", "--output", "div-assign-field-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "div-assign-field-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(14)\n");

    f.write("src/main.mb", "use core::ops::DivAssign; type Counter { value: u32 } extend Counter of DivAssign { type Rhs = u32; fn div_assign(share self, rhs: u32) { self.value /= 10 / rhs; } } fn index(calls: share u32) -> u32 { calls += 1; 0 } fn main() -> u32 { var calls: u32 = 0; var items := [Counter { value: 4 }]; items[index(calls.share())] /= { return 15; 0 }; 0 }");
    let index_early = f.run(&["run"]);
    assert!(index_early.status.success(), "{index_early:?}");
    assert_eq!(index_early.stdout, b"Result: u32(15)\n");
    let build = f.run(&["build", "--output", "div-assign-index-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "div-assign-index-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(15)\n");

    f.write("src/main.mb", "use core::ops::DivAssign; type Counter { value: u32 } fn main() -> u32 { var counter := Counter { value: 1 }; counter /= 2; counter.value }");
    let missing = f.run(&["analyze-project"]);
    assert!(!missing.status.success(), "{missing:?}");
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("no visible DivAssign implementation"),
        "{missing:?}"
    );

    f.write("src/main.mb", "use core::ops::DivAssign; type Counter { value: u32 } extend Counter of DivAssign { type Rhs = u32; fn div_assign(share self, rhs: u32) { self.value /= rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter /= true; counter.value }");
    let wrong_rhs = f.run(&["analyze-project"]);
    assert!(!wrong_rhs.status.success(), "{wrong_rhs:?}");

    f.write("src/main.mb", "use core::ops::DivAssign; type Counter { value: u32 } type Delta { value: u32 } extend Counter of DivAssign { type Rhs = Delta; fn div_assign(share self, rhs: Delta) { self.value /= rhs.value; } } fn scale<T>(initial: T, rhs: T::Rhs) -> T where T: DivAssign { var value := initial; value /= rhs; value } fn main() -> u32 { let result := scale(Counter { value: 81 }, Delta { value: 3 }); result.value }");
    let generic = f.run(&["run"]);
    assert!(generic.status.success(), "{generic:?}");
    assert_eq!(generic.stdout, b"Result: u32(27)\n");
    let generic_build = f.run(&["build", "--output", "div-assign-generic.wasm"]);
    assert!(generic_build.status.success(), "{generic_build:?}");
    let generic_artifact = f.run(&["run", "div-assign-generic.wasm"]);
    assert!(generic_artifact.status.success(), "{generic_artifact:?}");
    assert_eq!(generic_artifact.stdout, b"Result: i32(27)\n");

    f.write("src/main.mb", "use core::ops::DivAssign; type Counter { value: u32 } type Delta { value: u32 } extend Counter of DivAssign { type Rhs = Delta; fn div_assign(share self, rhs: Delta) { self.value /= rhs.value; } } fn scale<T>(initial: T, rhs: T::Rhs) -> T where T: DivAssign { var value := initial; value /= rhs; value } fn main() -> u32 { let delta := Delta { value: 3 }; let result := scale(Counter { value: 81 }, delta); delta.value + result.value }");
    let moved_rhs = f.run(&["ownership-project"]);
    assert!(
        !moved_rhs.status.success(),
        "owned generic RHS must be consumed: {moved_rhs:?}"
    );

    f.write("src/main.mb", "use core::ops::DivAssign; type Counter { value: u32 } type Delta { value: u32 } extend Counter of DivAssign { type Rhs = Delta; fn div_assign(share self, rhs: Delta) { self.value /= rhs.value; } } fn scale<T>(initial: T, rhs: T::Rhs) -> T where T: DivAssign { var value := initial; value /= rhs; value } fn main() -> u32 { let result := scale(Counter { value: 81 }, 3); result.value }");
    let generic_wrong_rhs = f.run(&["analyze-project"]);
    assert!(!generic_wrong_rhs.status.success(), "{generic_wrong_rhs:?}");

    f.write("src/main.mb", "use core::ops::DivAssign; type Plain { value: u32 } fn scale<T>(initial: T, rhs: T::Rhs) -> T where T: DivAssign { var value := initial; value /= rhs; value } fn main() -> u32 { let result := scale(Plain { value: 81 }, 3); result.value }");
    let missing_evidence = f.run(&["analyze-project"]);
    assert!(!missing_evidence.status.success(), "{missing_evidence:?}");
    assert!(
        String::from_utf8_lossy(&missing_evidence.stderr)
            .contains("no visible implementation of 'core::ops::DivAssign'"),
        "{missing_evidence:?}"
    );

    f.write("src/main.mb", "use core::ops::DivAssign; type Counter { value: u32 } extend Counter of DivAssign { type Rhs = u32; fn div_assign(share self, rhs: u32) { self.value /= rhs; } } fn main() -> u32 { let counter := Counter { value: 4 }; counter /= 1; counter.value }");
    let immutable = f.run(&["analyze-project"]);
    assert!(!immutable.status.success(), "{immutable:?}");

    f.write("src/main.mb", "use core::ops::DivAssign; type Counter { value: u32 } extend Counter of DivAssign { type Rhs = u32; fn div_assign(share self, rhs: u32) { self.value /= rhs; } } extend Counter of DivAssign { type Rhs = u32; fn div_assign(share self, rhs: u32) { self.value /= rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter /= 1; counter.value }");
    let ambiguous = f.run(&["analyze-project"]);
    assert!(!ambiguous.status.success(), "{ambiguous:?}");
    assert!(
        String::from_utf8_lossy(&ambiguous.stderr).contains("ambiguous DivAssign"),
        "{ambiguous:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::DivAssign; pub type Counter { value: u32 } fn main() -> u32 { var counter := Counter { value: 4 }; counter /= 1; counter.value }");
    f.write("src/other.mb", "use self::main::Counter; pub fn marker() {} pub extend Counter of core::ops::DivAssign { type Rhs = u32; fn div_assign(share self, rhs: u32) { self.value /= rhs; } }");
    let inactive = f.run(&["analyze-project"]);
    assert!(!inactive.status.success(), "{inactive:?}");
    assert!(
        String::from_utf8_lossy(&inactive.stderr).contains("no visible DivAssign implementation"),
        "{inactive:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::DivAssign; pub type Counter { value: u32 } fn main() -> u32 { var counter := Counter { value: 4 }; counter /= 1; counter.value }");
    f.write("src/other.mb", "use self::main::Counter; pub fn marker() {} extend Counter of core::ops::DivAssign { type Rhs = u32; fn div_assign(share self, rhs: u32) { self.value /= rhs; } }");
    // Keep the imported module live while its implementation remains private.
    let private = f.run(&["analyze-project"]);
    assert!(!private.status.success(), "{private:?}");

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var value: u32 = 9; value /= 4; value }",
    );
    let primitive = f.run(&["run"]);
    assert!(primitive.status.success(), "{primitive:?}");
    assert_eq!(primitive.stdout, b"Result: u32(2)\n");
    let primitive_build = f.run(&["build", "--output", "primitive-div-assign.wasm"]);
    assert!(primitive_build.status.success(), "{primitive_build:?}");
    let primitive_artifact = f.run(&["run", "primitive-div-assign.wasm"]);
    assert!(
        primitive_artifact.status.success(),
        "{primitive_artifact:?}"
    );
    assert_eq!(primitive_artifact.stdout, b"Result: i32(2)\n");

    f.write("src/main.mb", "use core::ops::DivAssign; type Counter { value: u32 } extend Counter of DivAssign { type Rhs = u32; fn div_assign(share self, rhs: u32) { self.value /= rhs; } } fn read(c: share Counter) -> u32 { c.value /= 1; c.value } fn main() -> u32 { var counter := Counter { value: 4 }; counter /= read(counter.share()); counter.value }");
    f.write("src/main.mb", "use core::ops::BitAndAssign; type Bits { value: u32 } type Mask { value: u32 } extend Bits of BitAndAssign { type Rhs = Mask; fn bitand_assign(share self, rhs: Mask) { self.value &= rhs.value; } } fn read(bits: borrow Bits) -> Mask { Mask { value: bits.value } } fn main() -> u32 { var bits := Bits { value: 3 }; bits &= read(bits.borrow()); bits.value }");
    let alias = f.run(&["ownership-project"]);
    assert!(!alias.status.success(), "{alias:?}");
    assert!(
        String::from_utf8_lossy(&alias.stderr).contains("while it is shared"),
        "{alias:?}"
    );
}

#[test]
fn user_defined_rem_assign_mutates_nominal_target_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='rem-assign'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::RemAssign; type Counter { value: u32 } type Delta { value: u32 } type Wrapper { item: Counter } extend Counter of RemAssign { type Rhs = Delta; fn rem_assign(share self, rhs: Delta) { self.value %= rhs.value; } } fn index(calls: share u32) -> u32 { calls += 1; 0 } fn main() -> u32 { var counter := Counter { value: 20 }; let d1 := Delta { value: 3 }; counter %= d1; var wrapper := Wrapper { item: Counter { value: 10 } }; let d2 := Delta { value: 2 }; wrapper.item %= d2; var calls: u32 = 0; var items := [Counter { value: 8 }]; let d3 := Delta { value: 1 }; items[index(calls.share())] %= d3; if calls == 1 { counter.value + wrapper.item.value + items[0].value } else { 0 } }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(2)\n");
    let build = f.run(&["build", "--output", "rem-assign.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "rem-assign.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(2)\n");

    f.write("src/main.mb", "use core::ops::RemAssign; type Counter { value: u32 } extend Counter of RemAssign { type Rhs = u32; fn rem_assign(share self, rhs: u32) { self.value %= 10 / rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter %= { return 13; 0 }; 0 }");
    let early = f.run(&["run"]);
    assert!(early.status.success(), "{early:?}");
    assert_eq!(early.stdout, b"Result: u32(13)\n");
    let build = f.run(&["build", "--output", "rem-assign-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "rem-assign-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(13)\n");

    f.write("src/main.mb", "use core::ops::RemAssign; type Counter { value: u32 } type Wrapper { item: Counter } extend Counter of RemAssign { type Rhs = u32; fn rem_assign(share self, rhs: u32) { self.value %= 10 / rhs; } } fn main() -> u32 { var wrapper := Wrapper { item: Counter { value: 4 } }; wrapper.item %= { return 14; 0 }; 0 }");
    let field_early = f.run(&["run"]);
    assert!(field_early.status.success(), "{field_early:?}");
    assert_eq!(field_early.stdout, b"Result: u32(14)\n");
    let build = f.run(&["build", "--output", "rem-assign-field-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "rem-assign-field-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(14)\n");

    f.write("src/main.mb", "use core::ops::RemAssign; type Counter { value: u32 } extend Counter of RemAssign { type Rhs = u32; fn rem_assign(share self, rhs: u32) { self.value %= 10 / rhs; } } fn index(calls: share u32) -> u32 { calls += 1; 0 } fn main() -> u32 { var calls: u32 = 0; var items := [Counter { value: 4 }]; items[index(calls.share())] %= { return 15; 0 }; 0 }");
    let index_early = f.run(&["run"]);
    assert!(index_early.status.success(), "{index_early:?}");
    assert_eq!(index_early.stdout, b"Result: u32(15)\n");
    let build = f.run(&["build", "--output", "rem-assign-index-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "rem-assign-index-return.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(15)\n");

    f.write("src/main.mb", "use core::ops::RemAssign; type Counter { value: u32 } fn main() -> u32 { var counter := Counter { value: 1 }; counter %= 2; counter.value }");
    let missing = f.run(&["analyze-project"]);
    assert!(!missing.status.success(), "{missing:?}");
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("no visible RemAssign implementation"),
        "{missing:?}"
    );

    f.write("src/main.mb", "use core::ops::RemAssign; type Counter { value: u32 } extend Counter of RemAssign { type Rhs = u32; fn rem_assign(share self, rhs: u32) { self.value %= rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter %= true; counter.value }");
    let wrong_rhs = f.run(&["analyze-project"]);
    assert!(!wrong_rhs.status.success(), "{wrong_rhs:?}");

    f.write("src/main.mb", "use core::ops::RemAssign; fn scale<T>(initial: T, rhs: T::Rhs) where T: RemAssign { var value := initial; value %= rhs; } fn main() -> u32 { 0 }");
    let generic = f.run(&["analyze-project"]);
    assert!(
        !generic.status.success(),
        "generic constrained RemAssign remains gated: {generic:?}"
    );

    f.write("src/main.mb", "use core::ops::RemAssign; type Counter { value: u32 } extend Counter of RemAssign { type Rhs = u32; fn rem_assign(share self, rhs: u32) { self.value %= rhs; } } fn main() -> u32 { let counter := Counter { value: 4 }; counter %= 1; counter.value }");
    let immutable = f.run(&["analyze-project"]);
    assert!(!immutable.status.success(), "{immutable:?}");

    f.write("src/main.mb", "use core::ops::RemAssign; type Counter { value: u32 } extend Counter of RemAssign { type Rhs = u32; fn rem_assign(share self, rhs: u32) { self.value %= rhs; } } extend Counter of RemAssign { type Rhs = u32; fn rem_assign(share self, rhs: u32) { self.value %= rhs; } } fn main() -> u32 { var counter := Counter { value: 4 }; counter %= 1; counter.value }");
    let ambiguous = f.run(&["analyze-project"]);
    assert!(!ambiguous.status.success(), "{ambiguous:?}");
    assert!(
        String::from_utf8_lossy(&ambiguous.stderr).contains("ambiguous RemAssign"),
        "{ambiguous:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::RemAssign; pub type Counter { value: u32 } fn main() -> u32 { var counter := Counter { value: 4 }; counter %= 1; counter.value }");
    f.write("src/other.mb", "use self::main::Counter; pub fn marker() {} pub extend Counter of core::ops::RemAssign { type Rhs = u32; fn rem_assign(share self, rhs: u32) { self.value %= rhs; } }");
    let inactive = f.run(&["analyze-project"]);
    assert!(!inactive.status.success(), "{inactive:?}");
    assert!(
        String::from_utf8_lossy(&inactive.stderr).contains("no visible RemAssign implementation"),
        "{inactive:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::RemAssign; pub type Counter { value: u32 } fn main() -> u32 { var counter := Counter { value: 4 }; counter %= 1; counter.value }");
    f.write("src/other.mb", "use self::main::Counter; pub fn marker() {} extend Counter of core::ops::RemAssign { type Rhs = u32; fn rem_assign(share self, rhs: u32) { self.value %= rhs; } }");
    // Keep the imported module live while its implementation remains private.
    let private = f.run(&["analyze-project"]);
    assert!(!private.status.success(), "{private:?}");

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var value: u32 = 9; value %= 4; value }",
    );
    let primitive = f.run(&["run"]);
    assert!(primitive.status.success(), "{primitive:?}");
    assert_eq!(primitive.stdout, b"Result: u32(1)\n");
    let primitive_build = f.run(&["build", "--output", "primitive-rem-assign.wasm"]);
    assert!(primitive_build.status.success(), "{primitive_build:?}");
    let primitive_artifact = f.run(&["run", "primitive-rem-assign.wasm"]);
    assert!(
        primitive_artifact.status.success(),
        "{primitive_artifact:?}"
    );
    assert_eq!(primitive_artifact.stdout, b"Result: i32(1)\n");

    f.write(
        "src/main.mb",
        "fn main() -> i32 { var value: i32 = -2147483648; value %= -1; value }",
    );
    let signed_min = f.run(&["run"]);
    assert!(signed_min.status.success(), "{signed_min:?}");
    assert_eq!(signed_min.stdout, b"Result: i32(0)\n");
    let signed_min_build = f.run(&["build", "--output", "signed-min-rem-assign.wasm"]);
    assert!(signed_min_build.status.success(), "{signed_min_build:?}");
    let signed_min_artifact = f.run(&["run", "signed-min-rem-assign.wasm"]);
    assert!(
        signed_min_artifact.status.success(),
        "{signed_min_artifact:?}"
    );
    assert_eq!(signed_min_artifact.stdout, b"Result: i32(0)\n");

    f.write(
        "src/main.mb",
        "fn main() -> i32 { var value: i32 = 7; value %= 0; value }",
    );
    let remainder_zero = f.run(&["run"]);
    let remainder_zero_error = err(remainder_zero, "RE007");
    assert!(
        remainder_zero_error.contains("remainder by zero"),
        "{remainder_zero_error}"
    );
    let remainder_zero_build = f.run(&["build", "--output", "remainder-zero.wasm"]);
    assert!(
        remainder_zero_build.status.success(),
        "{remainder_zero_build:?}"
    );
    let remainder_zero_artifact = err(f.run(&["run", "remainder-zero.wasm"]), "RE007");
    assert!(
        remainder_zero_artifact.contains("remainder by zero"),
        "{remainder_zero_artifact}"
    );

    f.write("src/main.mb", "use core::ops::RemAssign; type Counter { value: u32 } extend Counter of RemAssign { type Rhs = u32; fn rem_assign(share self, rhs: u32) { self.value %= rhs; } } fn read(c: share Counter) -> u32 { c.value %= 1; c.value } fn main() -> u32 { var counter := Counter { value: 4 }; counter %= read(counter.share()); counter.value }");
    f.write("src/main.mb", "use core::ops::BitAndAssign; type Bits { value: u32 } type Mask { value: u32 } extend Bits of BitAndAssign { type Rhs = Mask; fn bitand_assign(share self, rhs: Mask) { self.value &= rhs.value; } } fn read(bits: borrow Bits) -> Mask { Mask { value: bits.value } } fn main() -> u32 { var bits := Bits { value: 3 }; bits &= read(bits.borrow()); bits.value }");
    let alias = f.run(&["ownership-project"]);
    assert!(!alias.status.success(), "{alias:?}");
    assert!(
        String::from_utf8_lossy(&alias.stderr).contains("while it is shared"),
        "{alias:?}"
    );
}

#[test]
fn user_defined_equality_borrows_receiver_and_runs_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='partial-eq'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::PartialEq; type Key { value: u32 } extend Key of PartialEq { type Rhs = Key; fn eq(borrow self, rhs: Key) -> bool { self.value == rhs.value } } fn same<T>(lhs: T, rhs: T::Rhs) -> bool where T: PartialEq { lhs == rhs } fn main() -> u32 { let left := Key { value: 12 }; let same_key := Key { value: 12 }; let different := Key { value: 13 }; if !(left == same_key) { return 0; } if left != different { return left.value; } if !same(Key { value: 5 }, Key { value: 5 }) { return 0; } left.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(12)\n");
    let build = f.run(&["build", "--output", "partial-eq.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "partial-eq.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(12)\n");
    f.write("src/main.mb", "use core::ops::PartialEq; type Key { value: u32 } extend Key of PartialEq { type Rhs = Key; fn eq(borrow self, rhs: Key) -> bool { self.value == rhs.value } } fn main() -> u32 { let left := Key { value: 1 }; let right := Key { value: 1 }; let _equal := left == right; right.value }");
    let moved_rhs = err(f.run(&["ownership-project"]), "BE001");
    assert!(moved_rhs.contains("right"), "{moved_rhs}");
    f.write("src/main.mb", "use core::ops::PartialEq; type Key {} type Other {} extend Key of PartialEq { type Rhs = Key; fn eq(borrow self, rhs: Key) -> bool { true } } fn main() -> bool { Key {} == Other {} }");
    let wrong_rhs = err(f.run(&["analyze-project"]), "TE007");
    assert!(wrong_rhs.contains("PartialEq requires"), "{wrong_rhs}");
    f.write(
        "src/main.mb",
        "type Key {} fn main() -> bool { Key {} == Key {} }",
    );
    let missing = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        missing.contains("no visible PartialEq implementation"),
        "{missing}"
    );
    f.write("src/main.mb", "use core::ops::PartialEq; type Key {} extend Key of PartialEq { type Rhs = Key; fn eq(borrow self, rhs: Key) -> bool { true } } extend Key of PartialEq { type Rhs = Key; fn eq(borrow self, rhs: Key) -> bool { false } } fn main() -> bool { Key {} != Key {} }");
    let ambiguous = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        ambiguous.contains("ambiguous PartialEq implementation for `!=`"),
        "{ambiguous}"
    );
    f.write("src/main.mb", "use core::ops::PartialEq; type Key {} extend Key of PartialEq { type Rhs = Key; fn eq(self, rhs: Key) -> bool { true } } fn main() -> bool { Key {} == Key {} }");
    let wrong_receiver = err(f.run(&["analyze-project"]), "ME005");
    assert!(
        wrong_receiver.contains("does not match interface"),
        "{wrong_receiver}"
    );
    f.write("src/main.mb", "use core::ops::PartialEq; type Key {} extend Key of PartialEq { type Rhs = Key; fn eq(borrow self, rhs: Key) -> u32 { 1 } } fn main() -> bool { Key {} == Key {} }");
    let wrong_result = err(f.run(&["analyze-project"]), "ME005");
    assert!(wrong_result.contains("bool"), "{wrong_result}");
    f.write("src/main.mb", "use core::ops::PartialEq; type Key {} extend Key of PartialEq { type Rhs = Key; fn eq(borrow self, rhs: Key) -> bool { true } } fn main() -> u32 { let lhs := Key {}; let result := lhs == { return 42; Key {} }; 0 }");
    let early_return = f.run(&["run"]);
    assert!(early_return.status.success(), "{early_return:?}");
    assert_eq!(early_return.stdout, b"Result: u32(42)\n");
    f.write("src/main.mb", "use core::ops::PartialEq; type Key { value: u32 } extend Key of PartialEq { type Rhs = Key; fn eq(borrow self, rhs: Key) -> bool { self.value == rhs.value } } fn main() -> u32 { var order: u32 = 0; let equal := { order = 1; Key { value: 9 } } == { if order != 1 { return 0; } order = 12; Key { value: 9 } }; if order != 12 || !equal { return 0; } 42 }");
    let order_source = f.run(&["run"]);
    assert!(order_source.status.success(), "{order_source:?}");
    assert_eq!(order_source.stdout, b"Result: u32(42)\n");
    let order_build = f.run(&["build", "--output", "partial-eq-order.wasm"]);
    assert!(order_build.status.success(), "{order_build:?}");
    let order_artifact = f.run(&["run", "partial-eq-order.wasm"]);
    assert!(order_artifact.status.success(), "{order_artifact:?}");
    assert_eq!(order_artifact.stdout, b"Result: i32(42)\n");
    f.write("src/main.mb", "use other; use core::ops::PartialEq; pub type Key {} fn main() -> bool { Key {} == Key {} }");
    f.write("src/other.mb", "use self::main::Key; pub fn marker() {} extend Key of core::ops::PartialEq { type Rhs = Key; fn eq(borrow self, rhs: Key) -> bool { true } }");
    let private = err(f.run(&["analyze-project"]), "TE007");
    assert!(private.contains("private or inactive"), "{private}");
    f.write("src/main.mb", "use other::marker; use core::ops::PartialEq; pub type Key {} fn main() -> bool { Key {} == Key {} }");
    f.write("src/other.mb", "use self::main::Key; pub fn marker() {} pub extend Key of core::ops::PartialEq { type Rhs = Key; fn eq(borrow self, rhs: Key) -> bool { true } }");
    let inactive = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        inactive.contains("no visible PartialEq implementation"),
        "{inactive}"
    );
}

#[test]
fn user_defined_add_ignores_local_interface_named_add() {
    let f = Fixture::new();
    f.write(
        "add-gate.mb",
        "type Point { value: i32 } interface Add { fn add(self, rhs: Point) -> Point; } extend Point of Add { fn add(self, rhs: Point) -> Point { self } } fn main() -> i32 { let left := Point { value: 1 }; let right := Point { value: 2 }; let result := left + right; result.value }",
    );
    let diagnostic = err(f.run(&["analyze", "add-gate.mb"]), "TE007");
    assert!(
        diagnostic.contains("no visible Add implementation"),
        "{diagnostic}"
    );
}

#[test]
fn core_add_extension_requires_direct_public_module_visibility() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='add-visibility'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use other::marker; pub type Point { pub value: i32 } use core::ops::Add; fn main() -> i32 { let a := Point { value: 1 }; let b := Point { value: 2 }; (a + b).value }");
    f.write("src/other.mb", "use self::main::Point; pub fn marker() {} pub extend Point of core::ops::Add { type Rhs = Point; type Output = Point; fn add(self, rhs: Point) -> Point { Point { value: 42 } } }");
    let inactive = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        inactive.contains("no visible Add implementation"),
        "{inactive}"
    );

    f.write("src/main.mb", "use other; pub type Point { pub value: i32 } use core::ops::Add; fn main() -> i32 { let a := Point { value: 1 }; let b := Point { value: 2 }; (a + b).value }");
    f.write("src/other.mb", "use self::main::Point; pub fn marker() {} extend Point of core::ops::Add { type Rhs = Point; type Output = Point; fn add(self, rhs: Point) -> Point { Point { value: 42 } } }");
    let private = err(f.run(&["analyze-project"]), "TE007");
    assert!(private.contains("private or inactive"), "{private}");
}

#[test]
fn generic_add_bound_dispatches_through_core_evidence() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-add-bound'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::Add; type Point { value: i32 } type Right { value: i32 } type Output { value: i32 } extend Point of Add { type Rhs = Right; type Output = Output; fn add(self, rhs: Right) -> Output { Output { value: self.value + rhs.value } } } fn sum<T>(left: T, right: Right) -> Output where T: Add { left + right } fn main() -> i32 { let result: Output = sum(Point { value: 20 }, Right { value: 22 }); result.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "generic-add.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "generic-add.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn heterogeneous_add_rejects_wrong_rhs_missing_bindings_and_unresolved_projection() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='add-associated-rejections'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::Add; type Left { value: i32 } type Right { value: i32 } type Output { value: i32 } type Other { value: i32 } extend Left of Add { type Rhs = Right; type Output = Output; fn add(self, rhs: Right) -> Output { Output { value: self.value + rhs.value } } } fn main() -> i32 { let left := Left { value: 20 }; let wrong := Other { value: 22 }; let result := left + wrong; result.value }");
    let wrong_rhs = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        wrong_rhs.contains("matching its associated Rhs"),
        "{wrong_rhs}"
    );

    f.write("src/main.mb", "use core::ops::Add; type Left { value: i32 } type Right { value: i32 } type Output { value: i32 } extend Left of Add { type Rhs = Right; fn add(self, rhs: Right) -> Output { Output { value: self.value + rhs.value } } } fn main() -> i32 { 0 }");
    let missing_binding = err(f.run(&["analyze-project"]), "ME005");
    assert!(
        missing_binding.contains("missing associated type binding 'Output'"),
        "{missing_binding}"
    );

    f.write("src/main.mb", "use core::ops::Add; type Left { value: i32 } type Right { value: i32 } type Output { value: i32 } extend Left of Add { type Rhs = Right; type Output = Output; fn add(self, rhs: Right) -> Output { Output { value: self.value + rhs.value } } } fn project<T>(left: T) -> T::Output { left } fn main() { let value := project(Left { value: 1 }); value.value }");
    let unresolved_projection = err(f.run(&["analyze-project"]), "TE008");
    assert!(
        unresolved_projection.contains("associated type projection 'T::Output' is unresolved"),
        "{unresolved_projection}"
    );

    f.write("src/main.mb", "use core::ops::Add; type Left { value: i32 } type Right { value: i32 } type Output { value: i32 } extend Left of Add { type Rhs = Right; type Output = Output; fn add(self, rhs: Right) -> Output { Output { value: self.value + rhs.value } } } extend Left of Add { type Rhs = Right; type Output = Output; fn add(self, rhs: Right) -> Output { Output { value: self.value + rhs.value } } } fn combine<T>(right: T::Rhs, left: T) -> T::Output where T: Add { left + right } fn main() -> i32 { let output := combine(Right { value: 1 }, Left { value: 2 }); output.value }");
    let ambiguous_projection = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        ambiguous_projection.contains("ambiguous generic evidence"),
        "{ambiguous_projection}"
    );
}

#[test]
fn generic_heterogeneous_add_forwards_each_callers_selected_evidence() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-associated-add-evidence'\nentry='main::main'\n",
    );
    f.write(
        "src/model.mb",
        "pub type Left {} pub type Right {} pub type Output { pub value: i32 }",
    );
    f.write("src/common.mb", "use model; pub fn combine<T>(right: T::Rhs, left: T) -> T::Output where T: core::ops::Add { left + right }");
    f.write("src/left.mb", "use model; use common; use core::ops::Add; extend model::Left of Add { type Rhs = model::Right; type Output = model::Output; fn add(self, rhs: model::Right) -> model::Output { model::Output { value: 20 } } } pub fn run() -> i32 { let output: model::Output = common::combine(model::Right {}, model::Left {}); output.value }");
    f.write("src/right.mb", "use model; use common; use core::ops::Add; extend model::Left of Add { type Rhs = model::Right; type Output = model::Output; fn add(self, rhs: model::Right) -> model::Output { model::Output { value: 22 } } } pub fn run() -> i32 { let output: model::Output = common::combine(model::Right {}, model::Left {}); output.value }");
    f.write(
        "src/main.mb",
        "use left; use right; fn main() -> i32 { left::run() + right::run() }",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&[
        "build",
        "--output",
        "/tmp/memobits-generic-associated-add-evidence.wasm",
    ]);
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&["run", "/tmp/memobits-generic-associated-add-evidence.wasm"]);
    assert!(
        wasm.status.success(),
        "{}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn user_defined_add_consumes_both_owned_operands() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='add-move'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Add; type Point { value: i32 } extend Point of Add { type Rhs = Point; type Output = Point; fn add(self, rhs: Point) -> Point { Point { value: self.value + rhs.value } } } fn take(value: Point) {} fn main() -> i32 { let left := Point { value: 20 }; let right := Point { value: 22 }; let total := left + right; take(left); total.value }",
    );
    let diagnostic = err(f.run(&["ownership-project"]), "BE001");
    assert!(diagnostic.contains("left"), "{diagnostic}");
}

#[test]
fn user_defined_add_rhs_early_return_unwinds_staged_owned_operand() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='add-early-return'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Add; type Point { value: i32 } extend Point of Add { type Rhs = Point; type Output = Point; fn add(self, rhs: Point) -> Point { Point { value: self.value + rhs.value } } } fn main() -> i32 { let left := Point { value: 20 }; let total := left + { return 42; Point { value: 22 } }; total.value }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "add-early-return.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "add-early-return.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn user_defined_add_rejects_wrong_signature_and_ambiguous_evidence() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='add-signature'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use core::ops::Add; type Point { value: i32 } extend Point of Add { type Rhs = Point; type Output = Point; fn add(self, rhs: i32) -> Point { self } } fn main() -> i32 { let left := Point { value: 20 }; let right := Point { value: 22 }; let total := left + right; total.value }",
    );
    let wrong_signature = err(f.run(&["analyze-project"]), "ME005");
    assert!(
        wrong_signature.contains("does not match interface 'core::ops::Add'"),
        "{wrong_signature}"
    );

    f.write(
        "src/main.mb",
        "use core::ops::Add; type Point { value: i32 } extend Point of Add { type Rhs = Point; type Output = Point; fn add(self, rhs: Point) -> Point { self } } extend Point of Add { type Rhs = Point; type Output = Point; fn add(self, rhs: Point) -> Point { rhs } } fn main() -> i32 { let left := Point { value: 20 }; let right := Point { value: 22 }; let total := left + right; total.value }",
    );
    let ambiguous = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        ambiguous.contains("ambiguous Add implementation"),
        "{ambiguous}"
    );
}

#[test]
fn char_and_u32_are_distinct_scalar_types() {
    let f = Fixture::new();
    f.write("char-mismatch.mb", "fn main() -> bool { 'A' == 65 }");
    let message = err(f.run(&["analyze", "char-mismatch.mb"]), "TE002");
    assert!(message.contains("expected char"), "{message}");
}

#[test]
fn tuple_element_order_is_checked_by_type() {
    let f = Fixture::new();
    f.write(
        "tuple.mb",
        "fn need(pair: (i32, bool)) {} fn main() { need((true, 1)); }",
    );
    err(f.run(&["analyze", "tuple.mb"]), "TE002");
}

#[test]
fn tuple_labels_are_occurrence_local_independently_of_function_order() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-label-scope'\nentry='main::main'\n",
    );
    for (index, source) in [
        "fn left(pair: (left: i32, right: i32)) -> i32 { pair.left } fn right(pair: (right: i32, left: i32)) -> i32 { pair.left } fn main() -> i32 { left((left: 40, right: 0)) + right((right: 0, left: 2)) }",
        "fn right(pair: (right: i32, left: i32)) -> i32 { pair.left } fn left(pair: (left: i32, right: i32)) -> i32 { pair.left } fn main() -> i32 { left((left: 40, right: 0)) + right((right: 0, left: 2)) }",
    ]
    .into_iter()
    .enumerate()
    {
        f.write("src/main.mb", source);
        let output = f.run(&["run"]);
        assert!(output.status.success(), "{output:?}");
        assert_eq!(output.stdout, b"Result: i32(42)\n");

        let artifact = format!("tuple-label-scope-{index}.wasm");
        let build = f.run(&["build", "--output", &artifact]);
        assert!(build.status.success(), "{build:?}");
        let wasm = f.run(&["run", &artifact]);
        assert!(wasm.status.success(), "{wasm:?}");
        assert_eq!(wasm.stdout, output.stdout);
    }
}

#[test]
fn user_type_named_tuple_marker_does_not_collide_with_synthetic_tuple_identity() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-name-collision'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "type __Tuple { value: i32 } fn main() -> i32 { let value := __Tuple { value: 42 }; value.value }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
}

#[test]
fn tuple_reference_elements_are_gated_before_ir_validation() {
    let f = Fixture::new();
    f.write(
        "references.mb",
        "fn main() -> i32 { var value := 1; let view := value.borrow(); let pair := (view,); 0 }",
    );
    let message = err(f.run(&["analyze", "references.mb"]), "TE017");
    assert!(
        message.contains("tuple elements cannot contain direct or nested references"),
        "{message}"
    );
}

#[test]
fn tuple_nested_option_reference_is_gated_before_owner_can_escape() {
    let f = Fixture::new();
    f.write("option-reference.mb", "fn main() -> i32 { var value := 1; let maybe: (borrow i32)? = None; let tuple := (maybe, 0); value = 2; tuple.1 }");
    let message = err(f.run(&["analyze", "option-reference.mb"]), "TE017");
    assert!(
        message.contains("reference type arguments require embedded-loan tracking")
            || message.contains("tuple elements cannot contain direct or nested references")
            || message.contains("tuple types cannot contain direct or nested references"),
        "{message}"
    );
}

#[test]
fn tuples_preserve_order_across_internal_arguments_results_and_projections() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuples'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "fn identity(pair: (i32, bool)) -> (i32, bool) { (pair.0, pair.1) } fn main() -> i32 { let value := identity((40, true)); if value.1 { value.0 + 2 } else { 0 } }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "tuples.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "tuples.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn tuples_own_string_elements_locally_and_release_them() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-owners'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn main() -> i32 { let pair := (\"xy\", 40 as u32); (pair.0.len() + pair.1) as i32 }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "tuple-owners.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "tuple-owners.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn tuple_destructuring_moves_owned_elements_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-destructure'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn first() -> i32 { let text := \"xy\".concat(\"!\"); let second := \"ab\".concat(\"?\"); let pair := (text, second, 36 as u32); let (moved, moved_second, count) := pair; if moved.len() == 3 && moved_second.len() == 3 { (count as i32) + 6 } else { 0 } } fn last() -> i32 { let text := \"xy\".concat(\"!\"); let second := \"ab\".concat(\"?\"); let pair := (39 as u32, text, second); let (count, moved, moved_second) := pair; if moved.len() == 3 && moved_second.len() == 3 { (count as i32) + 3 } else { 0 } } fn main() -> i32 { first() + last() }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(84)\n");
    let build = f.run(&["build", "--output", "tuple-destructure.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "tuple-destructure.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn scalar_tuple_destructuring_runs_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-destructure-scalars'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn main() -> i32 { let pair := (40, true); let (number, enabled) := pair; if enabled { number + 2 } else { 0 } }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "tuple-destructure-scalars.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "tuple-destructure-scalars.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn nested_tuple_patterns_and_string_wildcards_transfer_cleanup_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-pattern-ownership'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn main() -> i32 {
            let text := "xy".concat("!");
            let tuple := ((40, true), text, 0 as u32);
            let ((number, enabled), _, _) := tuple;
            if enabled { number + 2 } else { 0 }
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "tuple-pattern-ownership.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "tuple-pattern-ownership.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn nested_string_tuple_patterns_cover_final_binding_and_all_wildcards_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-pattern-final-and-discard'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn main() -> i32 {
            let () := ();
            let first := "a".concat("");
            let last := "bc".concat("");
            let nested := ((40, true), first, last);
            let ((number, enabled), _, final_text) := nested;

            let discard_left := "left".concat("");
            let discard_right := "right".concat("");
            let discard := ((1, false), discard_left, discard_right);
            let ((_, _), _, _) := discard;

            if enabled { number + final_text.len() as i32 } else { 0 }
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "tuple-pattern-final-and-discard.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "tuple-pattern-final-and-discard.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn owned_string_tuples_move_through_internal_calls_and_returns() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-owner-transport'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn forward(pair: (string, u32), early: bool) -> (string, u32) {
            if early { return pair; }
            pair
        }
        fn exact(value: borrow string) -> bool {
            value.len() == 3 && match value.byte_at(0) {
                Some(a) => a == 120 && match value.byte_at(1) {
                    Some(b) => b == 121 && match value.byte_at(2) {
                        Some(c) => c == 33,
                        None => false
                    },
                    None => false
                },
                None => false
            }
        }
        fn main() -> i32 {
            let text := "xy".concat("!");
            let pair := (text, 39 as u32);
            let forwarded := forward(pair, true);
            if exact(forwarded.0.borrow()) && forwarded.1 == 39 { 42 } else { 0 }
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "tuple-owner-transport.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "tuple-owner-transport.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn owned_string_tuple_transport_rejects_use_after_move_and_nominal_structs() {
    let f = Fixture::new();
    f.write("move.mb", "fn forward(pair: (string, u32)) -> u32 { let (text, count) := pair; count } fn main() { let pair := (\"x\", 1 as u32); forward(pair); pair.1; }");
    let moved = err(f.run(&["ownership", "move.mb"]), "BE001");
    assert!(moved.contains("pair"), "{moved}");
    f.write("project.toml", "[package]\nname='nominal-owner-gate'\nentry='main::main'\n[export]\nforward='main::forward'\n");
    f.write("src/main.mb", "pub type Box { pub text: string } pub fn forward(value: Box) -> Box { value } fn main() {}");
    let nominal = err(f.run(&["build", "--lib"]), "LE900");
    assert!(
        nominal.contains("exported signatures cannot take structs or struct references"),
        "{nominal}"
    );

    f.write(
        "src/main.mb",
        "pub type Box { pub text: string, pub nested: (i32, bool) } pub fn forward(value: Box) -> Box { value } fn main() {}",
    );
    let nominal_nested = err(f.run(&["build", "--lib"]), "LE900");
    assert!(
        nominal_nested
            .contains("structs with String fields support only String and primitive fields"),
        "{nominal_nested}"
    );
}

#[test]
fn later_argument_early_return_cleans_staged_owned_tuple() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-owner-early-argument'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "fn forward(pair: (string, u32), later: bool) -> (string, u32) { pair } fn main() -> i32 { let text := \"xy\".concat(\"!\"); let pair := (text, 39 as u32); let forwarded := forward(pair, { return 42; false }); 0 }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "tuple-owner-early-argument.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "tuple-owner-early-argument.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn tuples_nest_in_struct_fields_and_enum_payloads() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='nested-tuples'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "type Holder { pair: (i32, bool) } type Data [Pair((i32, bool))] fn main() -> i32 { let holder := Holder { pair: (40, true) }; let data := Data::Pair((holder.pair.0, holder.pair.1)); match data { Data::Pair(pair) => if pair.1 { pair.0 + 2 } else { 0 } } }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "nested-tuples.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "nested-tuples.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn labeled_tuple_initializer_reorders_written_values_to_local_alias_slots() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='tuple-labels'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "fn sum(pair: (left: i32, right: i32)) -> i32 { pair.left + pair.right } fn main() -> i32 { let pair := (right: 2, left: 40); sum(pair) }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "tuple-labels.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "tuple-labels.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn nested_tuple_identity_ignores_occurrence_local_labels_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='nested-tuple-labels'\nentry='main::main'\n",
    );
    for (index, source_text) in [
        "fn make() -> (outer: (first: i32, second: i32), tag: i32) { (outer: (first: 40, second: 2), tag: 0) } fn consume(value: (container: (left: i32, right: i32), marker: i32)) -> i32 { value.container.left + value.container.right } fn main() -> i32 { consume(make()) }",
        "fn consume(value: (container: (left: i32, right: i32), marker: i32)) -> i32 { value.container.left + value.container.right } fn make() -> (outer: (first: i32, second: i32), tag: i32) { (outer: (first: 40, second: 2), tag: 0) } fn main() -> i32 { consume(make()) }",
    ]
    .into_iter()
    .enumerate()
    {
        f.write("src/main.mb", source_text);
        let source = f.run(&["run"]);
        assert!(source.status.success(), "{source:?}");
        assert_eq!(source.stdout, b"Result: i32(42)\n");
        let artifact = format!("nested-tuple-labels-{index}.wasm");
        let build = f.run(&["build", "--output", &artifact]);
        assert!(build.status.success(), "{build:?}");
        let wasm = f.run(&["run", &artifact]);
        assert!(wasm.status.success(), "{wasm:?}");
        assert_eq!(wasm.stdout, source.stdout);
    }

    f.write("src/main.mb", "fn make() -> (outer: (first: i32, second: i32), tag: i32) { (outer: (first: 40, second: 2), tag: 0) } fn consume(value: (container: (left: i32, right: bool), marker: i32)) -> i32 { value.container.left } fn main() -> i32 { consume(make()) }");
    let output = f.run(&["analyze", "src/main.mb"]);
    assert!(!output.status.success(), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("TE002"),
        "{output:?}"
    );
}

#[test]
fn labeled_tuple_malformed_forms_are_rejected() {
    let f = Fixture::new();
    for (source, expected) in [
        (
            "fn take(pair: (left: i32, right: i32)) {} fn main() { take((left: 1, 2)); }",
            "TE002",
        ),
        (
            "fn take(pair: (left: i32, right: i32)) {} fn main() { take((left: 1, left: 2)); }",
            "TE002",
        ),
        (
            "fn take(pair: (left: i32, right: i32)) {} fn main() { take((first: 1, second: 2)); }",
            "TE002",
        ),
        (
            "fn take(pair: (left: i32, left: bool)) {} fn main() -> i32 { 42 }",
            "TE002",
        ),
        (
            "fn main() { let pair := (left: 1, left: 2); }",
            "duplicate tuple initializer label 'left'",
        ),
        (
            "fn main() { let pair := (left: 1, 2); }",
            "all labeled or all positional",
        ),
        (
            "fn main() { let pair := ((left: 1, left: 2), 0); }",
            "duplicate tuple initializer label 'left'",
        ),
    ] {
        f.write("labels.mb", source);
        let message = err(f.run(&["analyze", "labels.mb"]), "TE002");
        assert!(message.contains(expected), "{message}");
    }
}

#[test]
fn generic_nominal_structs_specialize_types_and_const_lengths_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-structs'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        type Box<T> { value: T }
        type Buffer<T, const N: u32> { data: array<T, N> }
        fn main() -> i32 {
            let left := Box<i32> { value: 40 };
            let right := Box<u32> { value: 1 };
            let tail := Buffer<u8, 1> { data: [1] };
            left.value + right.value as i32 + tail.data[0] as i32
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "generic-structs.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "generic-structs.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn generic_nominal_structs_reject_mismatched_and_missing_arguments() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-errors'\nentry='main::main'\n",
    );
    for (source, message) in [
        (
            "type Box<T> { value: T } fn main() -> i32 { let boxed: Box<i32> = Box<u32> { value: 1 }; boxed.value }",
            "expected Box<i32>, found Box<u32>",
        ),
        (
            "type Box<T> { value: T } fn main() -> i32 { let boxed := Box { value: 1 }; boxed.value }",
            "requires 1 generic arguments",
        ),
    ] {
        f.write("src/main.mb", source);
        let diagnostic = err(f.run(&["run"]), "TE002");
        assert!(diagnostic.contains(message), "{diagnostic}");
    }
}

#[test]
fn generic_nominal_enums_construct_and_match_contextual_instances() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-enums'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        type Maybe<T> [None, Some(T)]
        fn main() -> i32 {
            let signed: Maybe<i32> = Maybe::Some(40);
            let absent: Maybe<u32> = Maybe::None;
            let unsigned: Maybe<u32> = Maybe::Some(2);
            let first := match signed {
                Maybe::Some(value) => value,
                Maybe::None => 0,
            };
            let second := match absent {
                Maybe::Some(value) => value as i32,
                Maybe::None => 0,
            };
            let third := match unsigned {
                Maybe::Some(value) => value as i32,
                Maybe::None => 0,
            };
            first + second + third
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "generic-enums.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "generic-enums.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn generic_nominal_enums_substitute_const_array_payloads_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-enum-arrays'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        type Packet<const N: u32> [Data(array<u8, N>)]
        fn main() -> i32 {
            let one: Packet<1> = Packet::Data([40]);
            let three: Packet<3> = Packet::Data([1, 1, 1]);
            let first := match one {
                Packet::Data(bytes) => bytes[0] as i32,
            };
            let count := match three {
                Packet::Data(bytes) => bytes[0] as i32 + bytes[1] as i32 + bytes[2] as i32,
            };
            first + count
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(43)\n");
    let build = f.run(&["build", "--output", "generic-enum-arrays.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "generic-enum-arrays.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn generic_nominal_enum_constructors_reject_invalid_origins_and_payloads() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-enum-errors'\nentry='main::main'\n",
    );
    for (source, code, message) in [
        (
            "type Packet<const N: u32> [Data(array<u8, N>)] type Other<const N: u32> [Data(array<u8, N>)] fn main() { let packet: Packet<1> = Other::Data([1]); }",
            "TE009",
            "unresolved or unsupported qualified function 'Other::Data'",
        ),
        (
            "type Packet<const N: u32> [Data(array<u8, N>)] fn main() { let packet: Packet<2> = Packet::Data([1]); }",
            "TE002",
            "expected array<u8, 2>, found array<u8, 1>",
        ),
        (
            "type Packet<const N: u32> [Data(array<u8, N>)] fn main() { let packet: Packet<1> = Packet::Data(); }",
            "TE010",
            "variant 'Packet<1>::Data' expects 1 argument(s), found 0",
        ),
        (
            "type Packet<const N: u32> [Data(array<u8, N>)] fn main() { let packet: Packet<1> = Packet::Missing; }",
            "NE004",
            "unknown variant 'Packet::Missing'",
        ),
    ] {
        f.write("src/main.mb", source);
        let output = f.run(&["run"]);
        assert!(!output.status.success(), "unexpected acceptance: {source}");
        let diagnostic = String::from_utf8(output.stderr).unwrap();
        assert!(diagnostic.contains(code), "{source}: {diagnostic}");
        assert!(diagnostic.contains(message), "{source}: {diagnostic}");
    }
}

#[test]
fn generic_functions_specialize_semantic_types_nested_and_recursive_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-function'
entry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn identity<T>(value: T) -> T { value }\nfn choose<T>(value: T, enabled: bool, fallback: T) -> T { if enabled { value } else { fallback } }\nfn forward<T>(value: T) -> T { identity(value) }\nfn recurse<T>(value: T, again: bool) -> T { if again { recurse(value, false) } else { value } }\nfn main() -> i32 { let enabled: bool = identity(true); let value: i32 = identity(40); let selected: i32 = choose(value, enabled, 0); let forwarded: i32 = forward(selected); if enabled { recurse(forwarded, true) + identity(2) } else { 0 } }\n",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(
        String::from_utf8(source.stdout).unwrap(),
        "Result: i32(42)\n"
    );
    assert!(f
        .run(&["build", "--output", "/tmp/memobits-generic-identity.wasm"])
        .status
        .success());
    assert_eq!(
        String::from_utf8(
            f.run(&["run", "/tmp/memobits-generic-identity.wasm"])
                .stdout
        )
        .unwrap(),
        "Result: i32(42)\n"
    );
}

#[test]
fn generic_functions_forward_array_type_and_const_arguments_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-array-function'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn echo<T, const N: u32>(value: array<T, N>) -> array<T, N> { value }\nfn relay<T, const N: u32>(value: array<T, N>) -> array<T, N> { echo(value) }\nfn main() -> i32 { let one: array<i32, 1> = [40]; let two: array<i32, 2> = [1, 1]; let a := relay(one); let b := relay(two); a[0] + b[0] + b[1] }\n",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&[
        "build",
        "--output",
        "/tmp/memobits-generic-array-function.wasm",
    ]);
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&["run", "/tmp/memobits-generic-array-function.wasm"]);
    assert!(
        wasm.status.success(),
        "{}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn generic_functions_forward_caller_selected_interface_evidence() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-interface-evidence'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "type Point { value: i32 }\ninterface Draw { fn draw(borrow self) -> i32; }\nextend Point of Draw { fn draw(borrow self) -> i32 { self.value } }\nfn render<T>(value: T) -> i32 where T: Draw { value.draw() of Draw }\nfn relay<T>(value: T) -> i32 where T: Draw { render(value) }\nfn main() -> i32 { let point := Point { value: 42 }; relay(point) }\n",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&[
        "build",
        "--output",
        "/tmp/memobits-generic-interface-evidence.wasm",
    ]);
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&["run", "/tmp/memobits-generic-interface-evidence.wasm"]);
    assert!(
        wasm.status.success(),
        "{}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn generic_interface_evidence_specializations_keep_caller_selections_distinct() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-interface-specializations'\nentry='main::main'\n",
    );
    f.write(
        "src/model.mb",
        "pub type Point { pub value: i32 } pub interface Draw { fn draw(borrow self) -> i32; }",
    );
    f.write("src/common.mb", "use model; pub fn render<T>(value: T) -> i32 where T: model::Draw { value.draw() of model::Draw } pub fn relay<T>(value: T) -> i32 where T: model::Draw { render(value) }");
    f.write("src/left.mb", "use model; use common; extend model::Point of model::Draw { fn draw(borrow self) -> i32 { 20 } } pub fn run() -> i32 { let point := model::Point { value: 1 }; common::relay(point) }");
    f.write("src/right.mb", "use model; use common; extend model::Point of model::Draw { fn draw(borrow self) -> i32 { 22 } } pub fn run() -> i32 { let point := model::Point { value: 1 }; common::relay(point) }");
    f.write(
        "src/main.mb",
        "use left; use right; fn main() -> i32 { left::run() + right::run() }",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&[
        "build",
        "--output",
        "/tmp/memobits-generic-interface-specializations.wasm",
    ]);
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&[
        "run",
        "/tmp/memobits-generic-interface-specializations.wasm",
    ]);
    assert!(
        wasm.status.success(),
        "{}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn generic_interface_evidence_rejects_missing_and_ambiguous_candidates() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-interface-evidence-errors'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "type Point { value: i32 } interface Draw { fn draw(borrow self) -> i32; } fn render<T>(value: T) -> i32 where T: Draw { value.draw() of Draw } fn main() -> i32 { let point := Point { value: 1 }; render(point) }");
    let missing = err(f.run(&["run"]), "TE007");
    assert!(missing.contains("no visible implementation"), "{missing}");
    f.write("src/main.mb", "type Point { value: i32 } interface Draw { fn draw(borrow self) -> i32; } extend Point of Draw { fn draw(borrow self) -> i32 { 1 } } extend Point of Draw { fn draw(borrow self) -> i32 { 2 } } fn render<T>(value: T) -> i32 where T: Draw { value.draw() of Draw } fn main() -> i32 { let point := Point { value: 1 }; render(point) }");
    let ambiguous = err(f.run(&["run"]), "TE007");
    assert!(
        ambiguous.contains("ambiguous generic evidence"),
        "{ambiguous}"
    );
}

#[test]
fn generic_array_call_checks_written_order_and_keeps_ownership_diagnostics() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-array-order'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn tick(counter: share i32) -> i32 { counter += 1; 0 }\nfn relay<T, const N: u32>(marker: i32, value: array<T, N>) -> array<T, N> { value }\nfn main() -> i32 { var counter := 0; let input: array<i32, 1> = [42]; let output := relay(tick(counter.share()), input); if counter == 1 { output[0] } else { 0 } }\n",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&[
        "build",
        "--output",
        "/tmp/memobits-generic-array-order.wasm",
    ]);
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&["run", "/tmp/memobits-generic-array-order.wasm"]);
    assert!(
        wasm.status.success(),
        "{}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, source.stdout);

    f.write(
        "src/main.mb",
        "fn consume_then_infer<T>(marker: i32, first: string, second: T) -> T { second } fn main() -> i32 { let text := \"owned\"; let result := consume_then_infer(0, text, text); result.len() as i32 }\n",
    );
    let diagnostic = err(f.run(&["run"]), "BE001");
    assert!(diagnostic.contains("text"), "{diagnostic}");
}

#[test]
fn generic_inference_suppresses_followup_error_for_invalid_inference_argument() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-array-inference-error'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn identity<T>(value: T) -> T { value } fn main() -> i32 { identity(missing) }\n",
    );
    let output = f.run(&["run"]);
    assert!(!output.status.success());
    let diagnostic = String::from_utf8(output.stderr).unwrap();
    assert!(
        !diagnostic.contains("cannot infer a consistent type"),
        "{diagnostic}"
    );
}

#[test]
fn generic_call_preserves_diverging_inference_argument_semantics() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-divergence'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn identity<T>(value: T) -> T { value } fn main() -> i32 { identity({ return 42; 1 }) }\n",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "/tmp/memobits-generic-divergence.wasm"]);
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = f.run(&["run", "/tmp/memobits-generic-divergence.wasm"]);
    assert!(
        wasm.status.success(),
        "{}",
        String::from_utf8_lossy(&wasm.stderr)
    );
    assert_eq!(wasm.stdout, source.stdout);

    f.write(
        "src/main.mb",
        "fn identity<T>(value: T) -> T { value } fn main() { identity({ return; 1 }); }\n",
    );
    let diagnostic = err(f.run(&["run"]), "TE002");
    assert!(
        diagnostic.contains("diverging argument without an expected result type"),
        "{diagnostic}"
    );
}

#[test]
fn generic_array_function_rejects_conflicting_const_arguments() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-array-function-errors'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn same<T, const N: u32>(first: array<T, N>, second: array<T, N>) -> array<T, N> { first }\nfn main() -> i32 { let one: array<i32, 1> = [1]; let two: array<i32, 2> = [2, 3]; same(one, two)[0] }\n",
    );
    let diagnostic = err(f.run(&["run"]), "TE002");
    assert!(
        diagnostic.contains("expected array<i32, 1>, found array<i32, 2>"),
        "{diagnostic}"
    );

    f.write(
        "src/main.mb",
        "fn nested<T>(value: T?) -> T? { value } fn main() -> i32 { 0 }\n",
    );
    let diagnostic = err(f.run(&["run"]), "TE007");
    assert!(
        diagnostic.contains(
            "outside the supported unconstrained direct-type-parameter specialization subset"
        ),
        "{diagnostic}"
    );
}

#[test]
fn generic_functions_reject_conflicting_types_and_preserve_owned_moves() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-function-errors'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn choose<T>(first: T, second: T) -> T { first } fn main() -> i32 { choose(1, true) }",
    );
    let diagnostic = err(f.run(&["run"]), "TE002");
    assert!(
        diagnostic.contains("expected i32, found bool"),
        "{diagnostic}"
    );

    f.write(
        "src/main.mb",
        "fn unsupported<T, U>(value: T) -> T { value } fn main() -> i32 { 0 }",
    );
    let diagnostic = err(f.run(&["run"]), "TE007");
    assert!(
        diagnostic.contains(
            "outside the supported unconstrained direct-type-parameter specialization subset"
        ),
        "{diagnostic}"
    );

    f.write(
        "src/main.mb",
        "fn identity<T>(value: T) -> T { value } fn main() -> i32 { let text := \"owned\"; let returned := identity(text); returned.len() as i32 }",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(source.stdout, b"Result: i32(5)\n");
    let build = f.run(&["build", "--output", "generic-owned.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "generic-owned.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);

    f.write(
        "src/main.mb",
        "fn identity<T>(value: T) -> T { value } fn main() { let text := \"owned\"; let returned := identity(text); text.len(); returned.len(); }",
    );
    let diagnostic = err(f.run(&["run"]), "BE001");
    assert!(diagnostic.contains("text"), "{diagnostic}");

    f.write(
        "src/generics.mb",
        "pub fn public_identity<T>(value: T) -> T { value }",
    );
    f.write(
        "src/main.mb",
        "use self::generics::public_identity; fn main() -> i32 { public_identity(42) }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "generic-import.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "generic-import.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn generic_specialization_keeps_declaring_module_imports_and_prelude_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-import-env'\nentry='main::main'\n[prelude]\nprelude_normalize='ops::normalize'\n",
    );
    f.write(
        "src/ops.mb",
        "pub fn identity<T>(value: T) -> T { value } pub fn normalize(value: bool) -> bool { value }",
    );
    f.write(
        "src/wrappers.mb",
        "use self::ops::identity as echo; pub fn wrap<T>(value: T, enabled: bool) -> T { if prelude_normalize(enabled) { echo(value) } else { value } }",
    );
    f.write(
        "src/main.mb",
        "use self::wrappers::wrap; fn main() -> i32 { if wrap(42, true) == 42 && wrap(true, false) { 42 } else { 0 } }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "generic-import-env.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "generic-import-env.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn generic_specialization_uses_declaring_module_extensions_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='generic-extension-env'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use self::wrappers::exercise; use methods; pub type Point { pub value: i32 } pub interface Measure { fn measure(borrow self) -> i32; } fn main() -> i32 { let point := Point { value: 21 }; let result := exercise(point); result.value * 2 }",
    );
    f.write(
        "src/methods.mb",
        "use self::main::{Point, Measure}; pub extend Point { pub fn doubled(borrow self) -> i32 { self.value * 2 } } pub extend Point of Measure { fn measure(borrow self) -> i32 { self.value } }",
    );
    f.write(
        "src/wrappers.mb",
        "use methods; use self::main::Measure; pub fn exercise<T>(point: T) -> T { let doubled := point.doubled(); let measured := point.measure() of Measure; point }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "generic-extension-env.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "generic-extension-env.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);

    f.write(
        "src/wrappers.mb",
        "pub fn exercise<T>(point: T) -> T { let doubled := point.doubled(); point }",
    );
    let diagnostic = err(f.run(&["run"]), "TE024");
    assert!(
        diagnostic.contains("struct 'Point' has no field 'doubled'"),
        "{diagnostic}"
    );
}

#[test]
fn postfix_optional_type_runs_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='optional-sugar'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn main() -> i32 { let present: i32? = Some(40); let absent: i32? = None; (match present { Some(value) => value, None => 0 }) + (match absent { Some(_) => 0, None => 2 }) }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "optional-sugar.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "optional-sugar.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn bodyless_nominal_types_remain_distinct_and_unconstructable() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bodyless-types'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "type Token; type Empty {} fn accept(token: Token) {} fn main() { let value := Empty {}; accept(value); }",
    );
    let diagnostic = err(f.run(&["run"]), "TE002");
    assert!(
        diagnostic.contains("expected Token, found Empty"),
        "{diagnostic}"
    );

    f.write(
        "src/main.mb",
        "type Token; fn main() { let value := Token {}; }",
    );
    let diagnostic = err(f.run(&["run"]), "TE023");
    assert!(
        diagnostic.contains("bodyless nominal type 'Token' cannot be constructed"),
        "{diagnostic}"
    );

    f.write("src/main.mb", "type Token<T>; fn main() {}");
    let diagnostic = err(f.run(&["run"]), "TE002");
    assert!(
        diagnostic.contains("generic bodyless types are not supported"),
        "{diagnostic}"
    );
}

#[test]
fn inherent_extension_methods_run_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='inherent-extension'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        type Point { x: i32 }
        extend {
            fn doubled(borrow self) -> i32 { self.x + self.x }
        }
        fn main() -> i32 {
            let point := Point { x: 21 };
            point.doubled()
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "inherent-extension.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "inherent-extension.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn directly_imported_public_inherent_extension_runs_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='inherent-module'\nentry='main::main'\n",
    );
    f.write(
        "src/geometry.mb",
        "pub type Point { pub x: i32 } extend { pub fn doubled(borrow self) -> i32 { self.x * 2 } }",
    );
    f.write(
        "src/main.mb",
        "use geometry; fn main() -> i32 { let point := geometry::Point { x: 21 }; point.doubled() }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "inherent-module.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "inherent-module.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn inherent_extension_selection_rejects_wrong_receivers_and_ambiguity() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='inherent-errors'\nentry='main::main'\n",
    );
    for (source, message) in [
        (
            "type Point { x: i32 } type Other { x: i32 } extend Point { fn value(borrow self) -> i32 { self.x } } fn main() -> i32 { let other := Other { x: 42 }; other.value() }",
            "no visible inherent method 'value' for Other",
        ),
        (
            "type Point { x: i32 } extend Point { fn value(borrow self) -> i32 { self.x } } extend Point { fn value(borrow self) -> i32 { self.x + 1 } } fn main() -> i32 { let point := Point { x: 41 }; point.value() }",
            "ambiguous inherent method 'value'",
        ),
    ] {
        f.write("src/main.mb", source);
        let diagnostic = err(f.run(&["run"]), "TE007");
        assert!(diagnostic.contains(message), "{source}: {diagnostic}");
    }
}

#[test]
fn inherent_extension_visibility_uses_direct_module_edges_and_public_declarations() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='inherent-visibility'\nentry='main::main'\n",
    );
    f.write(
        "src/geometry.mb",
        "pub type Point { pub x: i32 } extend Point { pub fn doubled(borrow self) -> i32 { self.x * 2 } }",
    );
    f.write(
        "src/main.mb",
        "use geometry::Point; fn main() -> i32 { let point := Point { x: 21 }; point.doubled() }",
    );
    let diagnostic = err(f.run(&["run"]), "TE024");
    assert!(
        diagnostic.contains("struct 'Point' has no field 'doubled'"),
        "{diagnostic}"
    );

    f.write(
        "src/geometry.mb",
        "pub type Point { pub x: i32 } extend Point { fn doubled(borrow self) -> i32 { self.x * 2 } }",
    );
    f.write(
        "src/main.mb",
        "use geometry; fn main() -> i32 { let point := geometry::Point { x: 21 }; point.doubled() }",
    );
    let diagnostic = err(f.run(&["run"]), "TE007");
    assert!(
        diagnostic.contains("matching inherent extension is private or inactive"),
        "{diagnostic}"
    );

    for geometry in [
        "pub type Point { pub x: i32 } pub extend Point { fn hidden(borrow self) -> i32 { self.x } }",
        "pub type Point { pub x: i32 } extend { fn hidden(borrow self) -> i32 { self.x } }",
    ] {
        f.write("src/geometry.mb", geometry);
        f.write(
            "src/main.mb",
            "use geometry; fn main() -> i32 { let point := geometry::Point { x: 21 }; point.hidden() }",
        );
        let diagnostic = err(f.run(&["run"]), "TE007");
        assert!(
            diagnostic.contains("matching inherent extension is private or inactive"),
            "{geometry}: {diagnostic}"
        );
    }
}

#[test]
fn postfix_optional_type_rejects_mismatched_and_uninferred_values() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='optional-errors'\nentry='main::main'\n",
    );
    for (source, code, message) in [
        (
            "fn main() { let value: i32? = Some(true); }",
            "TE002",
            "expected i32, found bool",
        ),
        (
            "fn main() { let value := None; }",
            "TE002",
            "cannot determine None's outcome type; provide a 'T?' annotation",
        ),
    ] {
        f.write("src/main.mb", source);
        let diagnostic = err(f.run(&["run"]), code);
        assert!(diagnostic.contains(message), "{source}: {diagnostic}");
    }
}

#[test]
fn postfix_optional_some_evaluates_its_payload_once_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='optional-once'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        type Counter { calls: u32 }
        fn payload(counter: share Counter) -> i32 {
            counter.calls += 1;
            40
        }
        fn main() -> i32 {
            var counter := Counter { calls: 0 };
            let value: i32? = Some(payload(counter.share()));
            (match value { Some(number) => number, None => 0 }) + counter.calls as i32 + 1
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "optional-once.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "optional-once.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn postfix_optional_reference_grouping_keeps_current_transport_gate() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='optional-reference-forms'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn take_optional_borrow(value: borrow i32?) {} fn main() {}",
    );
    let result = f.run(&["run"]);
    assert!(result.status.success(), "{result:?}");

    f.write(
        "src/main.mb",
        "fn take_borrowed_option(value: (borrow i32)?) {} fn main() {}",
    );
    let diagnostic = err(f.run(&["run"]), "TE017");
    assert!(
        diagnostic.contains("reference type arguments require embedded-loan tracking"),
        "{diagnostic}"
    );
}

#[test]
fn option_some_value_roundtrips_through_match() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='option-roundtrip'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "fn main() -> i32 { let present: i32? = Some(40); match present { Some(value) => value, None => 0 } }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(40)\n");
}

#[test]
fn a_user_type_named_bytes_is_an_ordinary_type_and_arrays_move() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bytes'\nentry='main::main'\n",
    );
    f.write("src/model.mb", "pub type Bytes = u8;");
    let source = "use self::model::Bytes;
        fn consume(data: array<u8, 1>) -> u8 { data[0] }
        fn main() -> u8 {
            let value: Bytes = 42;
            let data: array<u8, 1> = [value];
            consume(data)
        }";
    f.write("src/main.mb", source);
    let output = f.run(&["run"]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(output.stdout, b"Result: u8(42)\n");

    f.write(
        "src/main.mb",
        &source.replace("consume(data)", "consume(data); data[0]"),
    );
    err(f.run(&["run"]), "BE001");
}

fn assert_example_runs_in_both_modes(project: &str, expected: &[u8]) {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(project)
        .join("project.toml");
    let manifest = manifest.to_str().unwrap();
    // Build into an isolated directory so the standalone run uses only Wasm.
    let f = Fixture::new();
    let source = f.run(&["run", "--project", manifest]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, expected);

    let build = f.run(&["build", "--project", manifest, "--output", "example.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "example.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn compiler_error_root_executes_as_an_owned_value() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='errors'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn make() -> Error { Error { code: 17 } }
        fn main() -> u32 { let error := make(); error.code }",
    );
    let output = f.run(&["run"]);
    assert!(output.status.success(), "{:?}", output);
    assert_eq!(output.stdout, b"Result: u32(17)\n");
}

#[test]
fn inferred_options_execute_payload_once_in_source_and_artifact() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='outcomes'\nentry='main::main'\n",
    );
    f.write(
        "src/helper.mb",
        "pub fn bump(n: share i32) -> i32 { n += 1; n }",
    );
    f.write(
        "src/main.mb",
        "use helper::bump;
        fn main() -> i32 {
            var count := 0;
            let value := Some(Some(bump(count.share())));
            let empty: i32? = None;
            let result := match value {
                Some(inner) => match inner { Some(n) => n, None => 0 },
                None => 0
            };
            result + count * 10 + match empty { Some(n) => n, None => 0 }
        }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{:?}", source);
    assert_eq!(source.stdout, b"Result: i32(11)\n");
    let build = f.run(&["build", "--output", "option.wasm"]);
    assert!(build.status.success(), "{:?}", build);
    let bytes = fs::read(f.0.join("option.wasm")).unwrap();
    assert!(wasm_exports(&bytes).contains(&"main".to_owned()));
    let bare = Fixture::new();
    fs::write(bare.0.join("option.wasm"), bytes).unwrap();
    let artifact = bare.run(&["run", "option.wasm"]);
    assert!(artifact.status.success(), "{:?}", artifact);
    assert_eq!(source.stdout, artifact.stdout);
}

#[test]
fn unresolved_none_preserves_previous_artifact() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='outcomes'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "fn main() { let value := None; }");
    f.write("option.wasm", "existing artifact");
    let message = err(f.run(&["build", "--output", "option.wasm"]), "TE002");
    assert!(message.contains("'T?' annotation"), "{message}");
    assert_eq!(
        fs::read(f.0.join("option.wasm")).unwrap(),
        b"existing artifact"
    );
}

#[test]
fn owned_outcomes_execute_once_through_imported_aliases_in_source_and_artifact() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='outcomes'\nentry='main::main'\n",
    );
    f.write(
        "src/model.mb",
        "pub type Maybe = u32?;
         pub type Failure = Error;
         pub type Read = u32 ! Failure;
         pub type Work = Read ?! Failure;
         pub fn bump(n: share u32) -> u32 { n += 1; n }
         pub fn fail(n: share u32) -> Failure { Error { code: bump(n) } }
         pub fn zero() -> u32 { 0 }",
    );
    f.write(
        "src/main.mb",
        "use model::Maybe;
         use model::Read as R;
         use model::Work;
         use model::bump;
         use model::fail;
         use model::zero as nothing;
         fn read(value: Work) -> u32 {
             match value {
                 Work::Ok(Some(r)) => match r { Ok(n) => n, R::Err(e) => e.code },
                 Work::Ok(None) => nothing(),
                 Err(e) => e.code
             }
         }
         fn main() -> i32 {
             var count: u32 = 0;
             let value := Work::Ok(Some(Ok(bump(count.share()))));
             let failure: Work = Err(fail(count.share()));
             let miss := model::Work::Ok(None);
             let optional := match Maybe::Some(7) { Maybe::Some(n) => n, Maybe::None => 0 };
             if optional + read(value) + read(failure) + read(miss) + count * 10 == 30 { 30 } else { 0 }
         }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(30)\n");

    let build = f.run(&["build", "--output", "outcomes.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let bytes = fs::read(f.0.join("outcomes.wasm")).unwrap();
    assert!(wasm_exports(&bytes).contains(&"main".to_owned()));
    let bare = Fixture::new();
    fs::write(bare.0.join("outcomes.wasm"), bytes).unwrap();
    let artifact = bare.run(&["run", "outcomes.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(source.stdout, artifact.stdout);
}

#[test]
fn project_outcomes_reject_invalid_error_argument_and_missing_context() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='outcomes'\nentry='main::main'\n",
    );
    for (source, diagnostic) in [
        ("fn main() { let value := Ok(7); }", "'T ! E' annotation"),
        (
            "fn main() { let value: i32 ?! u32 = Ok(Some(7)); }",
            "requires Error",
        ),
    ] {
        f.write("src/main.mb", source);
        let message = err(f.run(&["analyze-project"]), "TE002");
        assert!(message.contains(diagnostic), "{message}");
    }
}

#[test]
fn derived_errors_execute_across_modules_in_source_and_artifact() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='errors'\nentry='main::main'\n",
    );
    f.write(
        "src/origin.mb",
        "pub type Base: Error { pub stage: u32 }
         pub type Parent = Base;
         pub fn bump(e: share Parent) { e.code += 4; }
         pub fn code(e: borrow Error) -> u32 { e.code }",
    );
    f.write(
        "src/model.mb",
        "use origin::Parent as Ancestor;
         pub type ParseError: Ancestor { pub line: u32 }
         pub type Read = u32 ! ParseError;
         pub type Work = Read ?! ParseError;
         pub fn wrap(e: ParseError) -> Work { Ok(Some(Err(e))) }",
    );
    f.write(
        "src/main.mb",
        "use model::ParseError;
         use model::Work;
         use model::wrap;
         fn inspect(work: Work) -> u32 {
             match work {
                 Ok(Some(read)) => match read { Err(e) => e.code + 10 * e.stage + 100 * e.line, Ok(n) => n },
                 Err(e) => e.code,
                 Ok(None) => 0
             }
         }
         fn main() -> i32 {
             var err := ParseError { line: 3, code: 1, stage: 2 };
             origin::bump(err.share());
             let n := origin::code(err.borrow());
             let failed: Work = Err(ParseError { stage: 9, code: 7, line: 8 });
             if n == 5 && inspect(wrap(err)) + inspect(failed) == 332 { 332 } else { 0 }
         }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(332)\n");
    let build = f.run(&["build", "--output", "errors.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let bare = Fixture::new();
    fs::copy(f.0.join("errors.wasm"), bare.0.join("errors.wasm")).unwrap();
    let artifact = bare.run(&["run", "errors.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(source.stdout, artifact.stdout);
}

#[test]
fn inherited_private_fields_keep_their_declaring_module() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='errors'\nentry='main::main'\n",
    );
    f.write(
        "src/origin.mb",
        "use model::Leaf;
         pub type Base: Error { secret: u32 }
         pub fn make() -> Leaf {
             var value := Leaf { code: 2, secret: 3, line: 5 };
             value.secret += 1;
             value
         }
         pub fn read(value: Leaf) -> u32 {
             let Leaf { code, secret, line } := value;
             code + secret + line
         }",
    );
    f.write(
        "src/model.mb",
        "use origin::Base;
         pub type Mid: Base {}
         pub type Leaf: Mid { pub line: u32 }",
    );
    f.write(
        "src/main.mb",
        "use origin::make;
         use origin::read;
         fn main() -> u32 { read(make()) }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(11)\n");

    for (body, expected) in [
        (
            "let value := Leaf { code: 2, secret: 3, line: 5 };",
            "cannot construct struct 'Leaf' outside module 'origin'",
        ),
        (
            "let value := origin::make(); let n := value.secret;",
            "field 'secret' of struct 'Leaf' is private to module 'origin'",
        ),
        (
            "var value := origin::make(); value.secret = 6;",
            "field 'secret' of struct 'Leaf' is private to module 'origin'",
        ),
        (
            "let Leaf { code, secret, line } := origin::make();",
            "cannot destructure struct 'Leaf' outside module 'origin'",
        ),
    ] {
        // The descendant's own module has no extra access to inherited private fields.
        f.write(
            "src/model.mb",
            &format!(
                "use origin::Base;
                 pub type Mid: Base {{}}
                 pub type Leaf: Mid {{ pub line: u32 }}
                 fn invalid() {{ {body} }}"
            ),
        );
        let message = err(f.run(&["analyze-project"]), "TE025");
        assert!(message.contains(expected), "{message}");
        assert!(message.contains("model.mb:"), "{message}");
    }
}

#[test]
fn project_error_derivation_checks_base_visibility_and_cross_module_cycles() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='errors'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use origin::Base;
         pub type Derived: Base {}
         fn main() {}",
    );
    f.write("src/origin.mb", "type Base: Error {}");
    let message = err(f.run(&["analyze-project"]), "ME007");
    assert!(message.contains("'origin::Base' is private"), "{message}");

    f.write("src/origin.mb", "pub type Base: main::Derived {}");
    let message = err(f.run(&["analyze-project"]), "TE026");
    assert!(message.contains("error derivation cycle"), "{message}");

    f.write(
        "src/main.mb",
        "type Base: Error {}
         pub type Derived: Base {}
         fn main() {}",
    );
    let message = err(f.run(&["analyze-project"]), "ME010");
    assert!(message.contains("exposes private type 'Base'"), "{message}");
}

#[test]
fn outcome_entries_report_every_variant_from_source_and_standalone_artifacts() {
    let f = Fixture::new();
    let bare = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='outcomes'\nentry='main::main'\n[build]\nstack_size=65520\n",
    );
    for (source, expected) in [
        (
            "fn main() -> u64 ! Error { Ok(18446744073709551615) }",
            "Ok(u64(18446744073709551615))",
        ),
        ("fn main() -> i8 ! Error { Ok(-20) }", "Ok(i8(-20))"),
        (
            "fn main() -> i32 ! Error { Err(Error { code: 4294967295 }) }",
            "Err(Error, code=4294967295)",
        ),
        (
            "fn main() -> bool ?! Error { Ok(Some(true)) }",
            "Ok(Some(bool(true)))",
        ),
        (
            "fn main() -> f64 ?! Error { Ok(Some(2.5)) }",
            "Ok(Some(f64(2.5)))",
        ),
        (
            "fn main() -> u64?! Error { Ok(Some(18446744073709551615)) }",
            "Ok(Some(u64(18446744073709551615)))",
        ),
        ("fn main() -> i32 ?! Error { Ok(None) }", "Ok(None)"),
        ("fn main() -> i8 ?! Error { Ok(None) }", "Ok(None)"),
        (
            "type ParseError: Error {} fn main() -> i32 ?! ParseError { Err(ParseError { code: 5 }) }",
            "Err(outcomes::main::ParseError, code=5)",
        ),
        (
            "fn main() -> u8 ?! Error { Err(Error { code: 9 }) }",
            "Err(Error, code=9)",
        ),
    ] {
        f.write("src/main.mb", source);
        let output = f.run(&["run"]);
        assert!(output.status.success(), "{source}: {output:?}");
        assert_eq!(output.stdout, format!("Result: {expected}\n").as_bytes());
        let build = f.run(&["build", "--output", "entry.wasm"]);
        assert!(build.status.success(), "{source}: {build:?}");
        fs::copy(f.0.join("entry.wasm"), bare.0.join("entry.wasm")).unwrap();
        let artifact = bare.run(&["run", "entry.wasm", "--entry", "main"]);
        assert!(artifact.status.success(), "{source}: {artifact:?}");
        assert_eq!(output.stdout, artifact.stdout, "{source}");
    }
}

#[test]
fn whole_ancestor_share_stores_keep_the_leaf_identity_and_fields() {
    let f = Fixture::new();
    let bare = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='outcomes'\nentry='main::main'\n",
    );
    f.write(
        "src/errors.mb",
        "pub type Base: Error { pub stage: u8 }
         pub type Leaf: Base { pub line: u16 }
         pub type Failure = i32 ! Leaf;
         fn reset(e: share Error) { e = Error { code: 17 }; }
         pub fn replace(e: share Base) {
             e = Base { code: 11, stage: 3 };
             reset(e.share());
         }
         pub fn report(e: Leaf) -> Failure { Err(e) }",
    );
    f.write(
        "src/main.mb",
        "use errors::Leaf;
         use errors::Failure;
         type Cell { leaf: Leaf }
         fn main() -> Failure {
             var cell := Cell { leaf: Leaf { code: 1, stage: 2, line: 500 } };
             errors::replace(cell.leaf.share());
             let Cell { leaf } := cell;
             if leaf.line == 500 && leaf.stage == 3 {
                 errors::report(leaf)
             } else {
                 Ok(0)
             }
         }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(
        source.stdout,
        b"Result: Err(outcomes::errors::Leaf, code=17)\n"
    );
    let build = f.run(&["build", "--output", "entry.wasm"]);
    assert!(build.status.success(), "{build:?}");
    fs::copy(f.0.join("entry.wasm"), bare.0.join("entry.wasm")).unwrap();
    let artifact = bare.run(&["run", "entry.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(source.stdout, artifact.stdout);
}

#[test]
fn outcome_entry_traps_keep_runtime_diagnostics() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='outcomes'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn divide(n: i32) -> i32 { 1 / n }
         fn consume(text: string, value: i32) -> i32 { value }
         fn main() -> i32 ! Error {
             let text := \"a\".concat(\"b\");
             Ok(consume(text, divide(0)))
         }",
    );
    let source = err(f.run(&["run"]), "RE007");
    assert!(
        source.contains("division by zero") && source.contains("main.mb"),
        "{source}"
    );
    let build = f.run(&["build", "--output", "entry.wasm"]);
    assert!(build.status.success(), "{build:?}");
    assert_eq!(source, err(f.run(&["run", "entry.wasm"]), "RE007"));
}

#[test]
fn outcome_entry_stack_overflow_is_a_trap() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='outcomes'\nentry='main::main'\n[build]\nstack_size=4096\n",
    );
    f.write(
        "src/main.mb",
        "fn dive(n: i32) -> i32 ! Error {
             if n == 0 { Ok(1) } else { dive(n - 1) }
         }
         fn main() -> i32 ! Error { dive(10000) }",
    );
    let source = err(f.run(&["run"]), "RE008");
    let build = f.run(&["build", "--output", "entry.wasm"]);
    assert!(build.status.success(), "{build:?}");
    assert_eq!(source, err(f.run(&["run", "entry.wasm"]), "RE008"));
}

#[test]
fn outcome_entries_gate_aggregate_successes_parameters_and_library_exports() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='outcomes'\nentry='main::main'\n[export]\nwork='main::work'\n",
    );
    for (source, expected) in [
        (
            "fn main() -> array<i32, 1> ! Error { Ok([7]) }",
            "primitive success payload",
        ),
        (
            "fn main(n: i32) -> i32 ?! Error { Ok(Some(n)) }",
            "must take no parameters",
        ),
        (
            "type Lookalike [ Ok(i32), Err(Error) ] fn main() -> Lookalike { Lookalike::Ok(7) }",
            "cannot return enums",
        ),
        ("fn main() -> i32? { Some(7) }", "cannot return enums"),
    ] {
        f.write("src/main.mb", source);
        let message = err(f.run(&["build"]), "LE900");
        assert!(message.contains(expected), "{source}: {message}");
    }
    f.write(
        "src/main.mb",
        "pub fn work() -> i32 ! Error { Ok(7) } fn main() {}",
    );
    let message = err(f.run(&["build", "--lib"]), "LE900");
    assert!(message.contains("cannot return enums"), "{message}");
}

#[test]
fn explicit_interface_selector_resolves_a_unique_candidate() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='interface-selector-gate'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "type Point { x: i32 }\ninterface Draw { fn draw(borrow self) -> i32; }\nextend Point of Draw { fn draw(borrow self) -> i32 { self.x } }\nfn main() -> i32 { let point := Point { x: 42 }; point.draw() of Draw }\n",
    );
    let analysis = f.run(&["analyze-project"]);
    assert!(analysis.status.success(), "{analysis:?}");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "interface.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "interface.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn explicit_interface_selection_reports_all_ambiguous_candidates() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='interface-ambiguity'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "type Point { x: i32 }\ninterface Draw { fn draw(borrow self) -> i32; }\nextend Point of Draw { fn draw(borrow self) -> i32 { 1 } }\nextend Point of Draw { fn draw(borrow self) -> i32 { 2 } }\nfn main() -> i32 { let point := Point { x: 42 }; point.draw() of Draw }\n",
    );
    let diagnostic = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        diagnostic.contains("ambiguous extension selection"),
        "{diagnostic}"
    );
    assert!(diagnostic.contains("main:70..128"), "{diagnostic}");
    assert!(diagnostic.contains("main:129..187"), "{diagnostic}");
    assert!(diagnostic.matches("main:").count() >= 2, "{diagnostic}");
}

#[test]
fn imported_extensions_from_two_modules_are_ambiguous() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='interface-two-imports'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use left; use right; pub type Point { pub x: i32 }\npub interface Draw { fn draw(borrow self) -> i32; }\nfn main() -> i32 { let point := Point { x: 42 }; point.draw() of Draw }",
    );
    f.write(
        "src/left.mb",
        "use self::main::{Point, Draw}; pub extend Point of Draw { fn draw(borrow self) -> i32 { 1 } }",
    );
    f.write(
        "src/right.mb",
        "use self::main::{Point, Draw}; pub extend Point of Draw { fn draw(borrow self) -> i32 { 2 } }",
    );
    let diagnostic = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        diagnostic.contains("ambiguous extension selection"),
        "{diagnostic}"
    );
    assert!(diagnostic.contains("left:"), "{diagnostic}");
    assert!(diagnostic.contains("right:"), "{diagnostic}");
}

#[test]
fn explicit_interface_selection_reports_private_imported_extension() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='interface-private'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use graphics; pub type Point { pub x: i32 }\npub interface Draw { fn draw(borrow self) -> i32; }\nfn main() -> i32 { let point := Point { x: 42 }; point.draw() of Draw }",
    );
    f.write(
        "src/graphics.mb",
        "use self::main::Point; use self::main::Draw; extend Point of Draw { fn draw(borrow self) -> i32 { self.x } }",
    );
    let diagnostic = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        diagnostic.contains("matching extension is private or inactive: graphics:"),
        "{diagnostic}"
    );
}

#[test]
fn explicit_interface_selection_reports_missing_implementation() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='interface-missing'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "type Point { x: i32 }\ninterface Draw { fn draw(borrow self) -> i32; }\nfn main() -> i32 { let point := Point { x: 42 }; point.draw() of Draw }",
    );
    let diagnostic = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        diagnostic.contains("no visible extension implements 'main::Draw::draw' for Point"),
        "{diagnostic}"
    );
}

#[test]
fn symbol_import_loads_but_does_not_activate_an_extension() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='interface-symbol-import'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use self::graphics::ping; pub type Point { pub x: i32 }\npub interface Draw { fn draw(borrow self) -> i32; }\nfn main() -> i32 { let point := Point { x: 42 }; point.draw() of Draw }",
    );
    f.write(
        "src/graphics.mb",
        "use self::main::{Point, Draw}; pub fn ping() -> i32 { 0 } pub extend Point of Draw { fn draw(borrow self) -> i32 { self.x } }",
    );
    let diagnostic = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        diagnostic.contains("no visible extension implements 'main::Draw::draw' for Point"),
        "{diagnostic}"
    );
}

#[test]
fn interface_selection_requires_a_receiver_method_call() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='interface-receiver-required'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "interface Draw { fn draw(borrow self) -> i32; }\nfn draw() -> i32 { 42 }\nfn main() -> i32 { draw() of Draw }",
    );
    let diagnostic = err(f.run(&["analyze-project"]), "TE007");
    assert!(
        diagnostic.contains("interface selection requires a receiver method call"),
        "{diagnostic}"
    );
}

#[test]
fn extension_method_bodies_are_typechecked() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='interface-body-check'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "type Point { x: i32 }\ninterface Draw { fn draw(borrow self) -> i32; }\nextend Point of Draw { fn draw(borrow self) -> i32 { true } }\nfn main() -> i32 { 0 }",
    );
    let diagnostic = err(f.run(&["analyze-project"]), "TE");
    assert!(diagnostic.contains("expected i32"), "{diagnostic}");
}

#[test]
fn selected_extension_calls_preserve_receiver_access_modes() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='interface-receivers'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "type Point { x: i32 }\ninterface BorrowValue { fn value(borrow self) -> i32; }\ninterface ShareValue { fn value(share self) -> i32; }\ninterface TakeValue { fn value(self) -> i32; }\nextend Point of BorrowValue { fn value(borrow self) -> i32 { self.x } }\nextend Point of ShareValue { fn value(share self) -> i32 { self.x } }\nextend Point of TakeValue { fn value(self) -> i32 { self.x } }\nfn main() -> i32 { var point := Point { x: 42 }; point.value() of BorrowValue + point.value() of ShareValue + point.value() of TakeValue }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(126)\n");
    let build = f.run(&["build", "--output", "receivers.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "receivers.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn borrowed_extension_receiver_remains_live_through_later_arguments() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='interface-receiver-loan'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "type Point { x: i32 }\ninterface Check { fn check(borrow self, value: i32) -> i32; }\nextend Point of Check { fn check(borrow self, value: i32) -> i32 { self.x + value } }\nfn consume(point: Point) -> i32 { point.x }\nfn main() -> i32 { var point := Point { x: 42 }; point.check(consume(point)) of Check }",
    );
    let diagnostic = err(f.run(&["ownership-project"]), "BE");
    assert!(
        diagnostic.contains("borrow") || diagnostic.contains("loan"),
        "{diagnostic}"
    );
}

#[test]
fn extension_receiver_loans_reject_conflicting_later_argument_access() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='interface-later-argument-loans'\nentry='main::main'\n",
    );

    for (interface, receiver, later_access) in [
        ("BorrowCheck", "borrow", "point.x = 7; 1"),
        ("ShareCheck", "share", "point.x = 7; 1"),
    ] {
        let source = format!(
            "type Point {{ x: i32 }} interface {interface} {{ fn check({receiver} self, value: i32) -> i32; }} extend Point of {interface} {{ fn check({receiver} self, value: i32) -> i32 {{ self.x + value }} }} fn main() -> i32 {{ var point := Point {{ x: 42 }}; point.check({{ {later_access} }}) of {interface} }}"
        );
        f.write("src/main.mb", &source);
        let diagnostic = err(f.run(&["ownership-project"]), "BE");
        assert!(
            diagnostic.contains("loan")
                || diagnostic.contains("borrow")
                || diagnostic.contains("shared"),
            "{interface}: {diagnostic}"
        );
    }
}

#[test]
fn directly_imported_public_extension_runs_from_another_module() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='interface-module-edge'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use graphics; pub type Point { pub x: i32 }\npub interface Draw { fn draw(borrow self) -> i32; }\nfn main() -> i32 { let point := Point { x: 42 }; point.draw() of Draw }",
    );
    f.write(
        "src/graphics.mb",
        "use self::main::{Point, Draw}; pub extend Point of Draw { fn draw(borrow self) -> i32 { self.x } }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i32(42)\n");
    let build = f.run(&["build", "--output", "graphics.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "graphics.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-cli-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, name: &str, text: &str) {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_mb"))
            .current_dir(&self.0)
            .args(args)
            .output()
            .unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn err(output: Output, code: &str) -> String {
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let text = String::from_utf8(output.stderr).unwrap();
    assert!(text.contains(code), "{text}");
    text
}

fn wasm_exports(bytes: &[u8]) -> Vec<String> {
    wasmparser::Validator::new().validate_all(bytes).unwrap();
    let mut names = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::ExportSection(exports) = payload.unwrap() {
            for export in exports {
                names.push(export.unwrap().name.to_owned());
            }
        }
    }
    names
}

#[test]
fn inventory_is_sorted_and_does_not_compile_sources() {
    let f = Fixture::new();
    f.write("project.toml", "[package]\nname='demo'\nversion='1.2'\nentry='main::run'\n[export]\nZed='z::Zed'\nAlpha='a::Alpha'\n");
    f.write("src/z.mb", "not valid source syntax");
    f.write("src/a/b.mb", "");
    f.write("src/ignored.txt", "");
    let output = f.run(&["project"]);
    assert!(output.status.success(), "{:?}", output);
    assert!(output.stderr.is_empty());
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("Package: demo\nVersion: 1.2\nEntry: main::run\n"));
    assert!(text.contains("Exports (2):\n  Alpha -> a::Alpha\n  Zed -> z::Zed\n"));
    assert!(text.contains(&format!(
        "Modules (2):\n  a::b -> {}\n  z -> z.mb\n",
        PathBuf::from("a").join("b.mb").display()
    )));
    assert_eq!(text.as_bytes(), f.run(&["project"]).stdout);
}

#[test]
fn override_uses_manifest_parent_for_sources() {
    let f = Fixture::new();
    f.write(
        "nested/custom.toml",
        "[package]\nname='override'\nentry='main::run'\nsrc='code'\n",
    );
    f.write("nested/code/main.mb", "");
    let output = f.run(&["project", "--project", "nested/custom.toml"]);
    assert!(output.status.success());
    assert!(String::from_utf8(output.stdout)
        .unwrap()
        .contains("Modules (1):\n  main -> main.mb\n"));
    let path = f.0.join("nested/custom.toml");
    assert!(f
        .run(&["project", "--project", path.to_str().unwrap()])
        .status
        .success());
}

#[test]
fn typed_project_failures_have_stable_codes() {
    let f = Fixture::new();
    err(f.run(&["project"]), "PE001");
    f.write("project.toml", "this is not TOML");
    err(f.run(&["project"]), "PE002");
    f.write("project.toml", "[package]\nname=''\nentry='main::run'\n");
    err(f.run(&["project"]), "PE003");
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='main::run'\n",
    );
    err(f.run(&["project"]), "PE001");
    f.write("src/not-valid.mb", "");
    err(f.run(&["project"]), "PE003");
}

#[test]
fn cli_host_profile_is_validated_before_import_free_execution() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='host-profile'\nentry='main::main'\n\n[host]\nprofile = \"cli\"\n",
    );
    f.write("src/main.mb", "fn main() -> i32 { 42 }");
    let project = f.run(&["project"]);
    assert!(project.status.success(), "{project:?}");
    assert!(String::from_utf8_lossy(&project.stdout).contains("Host profile: cli (import-free)"));
    let output = f.run(&["run"]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(output.stdout, b"Result: i32(42)\n");

    for (manifest, code, expected) in [
        (
            "[package]\nname='missing-profile'\nentry='main::main'\n[host]\n",
            "PE003",
            "host.profile is required",
        ),
        (
            "[package]\nname='unknown-profile'\nentry='main::main'\n[host]\nprofile = \"browser\"\n",
            "PE003",
            "unknown host profile",
        ),
        (
            "[package]\nname='host-capability'\nentry='main::main'\n[host]\nprofile = \"cli\"\ncapability = \"clock\"\n",
            "PE002",
            "invalid project manifest",
        ),
        (
            "[package]\nname='host-import'\nentry='main::main'\n[host]\nprofile = \"cli\"\n[host.imports]\nclock = \"clock.now\"\n",
            "PE002",
            "invalid project manifest",
        ),
    ] {
        f.write("project.toml", manifest);
        let output = err(f.run(&["run"]), code);
        assert!(output.contains(expected), "{output}");
    }
}

#[test]
fn help_usage_and_unsupported_commands_are_truthful() {
    let f = Fixture::new();
    for args in [&["--help"][..], &["-h"], &["project", "--help"]] {
        let output = f.run(args);
        assert!(output.status.success());
        assert!(output.stderr.is_empty());
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(text.contains("Usage: mb project [--project PATH]"));
        assert!(text.contains("mb resolve [--project PATH] [--lib]"));
        assert!(text.contains("mb ownership-project [--project PATH] [--lib]"));
        assert!(text.contains("one typed source-declared Wasm import"));
        assert!(text.contains("memobits:console.write_i32(i32) -> unit"));
        assert!(!text.contains("source-declared imports remain unsupported"));
        assert!(text.contains("mb check [--project PATH] [--lib]"));
        assert!(!text.contains("not supported yet"));
    }
    for args in [
        &[][..],
        &["unknown"],
        &["project", "--project"],
        &["project", "--project", "--help"],
        &["project", "extra"],
        &["project", "--project", "a", "--project", "b"],
        &["--help", "extra"],
        &["project", "--lib"],
        &["resolve", "--project"],
        &["resolve", "--lib", "--lib"],
        &["resolve", "--project", "a", "--project", "b"],
        &["build", "--output"],
        &["build", "--output", "a", "--output", "b"],
        &["build", "--lib", "--lib"],
        &["run", "app.wasm", "--entry"],
        &["run", "app.wasm", "--entry", "a", "--entry", "b"],
        &["run", "app.wasm", "--unexpected"],
        &["run", "--project", "project.toml", "--entry", "main"],
    ] {
        err(f.run(args), "PE004");
    }
    err(f.run(&["check"]), "PE001");
}

#[test]
fn build_writes_valid_application_and_library_wasm_exports() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='app::main'\n",
    );
    f.write("src/app.mb", "fn main() -> i32 { 42 }");
    let output = f.run(&["build", "--output", "app.wasm"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(wasm_exports(&fs::read(f.0.join("app.wasm")).unwrap()).contains(&"main".into()));
    let output = f.run(&["build"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(f.0.join("target/memobits/app.wasm").is_file());

    f.write(
        "library/project.toml",
        "[package]\nname='lib'\n[export]\nplus='math::add'\n",
    );
    f.write(
        "library/src/math.mb",
        "pub fn add(value: i32) -> i32 { value }",
    );
    let output = f.run(&[
        "build",
        "--lib",
        "--project",
        "library/project.toml",
        "--output",
        "library.wasm",
    ]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let names = wasm_exports(&fs::read(f.0.join("library.wasm")).unwrap());
    assert!(names.contains(&"plus".into()), "{names:?}");
    assert!(!names.contains(&"main".into()), "{names:?}");
}

#[test]
fn failed_build_preserves_existing_artifact_and_rejects_type_exports() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='app::main'\n",
    );
    f.write(
        "src/app.mb",
        "fn main() { let x := [1]; let y := x; let z := x; }",
    );
    f.write("previous.wasm", "previous artifact");
    let message = err(f.run(&["build", "--output", "previous.wasm"]), "BE001");
    assert!(message.contains("app.mb:1:"), "{message}");
    assert_eq!(
        fs::read(f.0.join("previous.wasm")).unwrap(),
        b"previous artifact"
    );

    f.write(
        "library/project.toml",
        "[package]\nname='lib'\n[export]\nNumber='math::Number'\n",
    );
    f.write("library/src/math.mb", "pub type Number = i32;");
    let message = err(
        f.run(&[
            "build",
            "--lib",
            "--project",
            "library/project.toml",
            "--output",
            "type.wasm",
        ]),
        "PE006",
    );
    assert!(
        message.contains("type export 'Number' is unsupported"),
        "{message}"
    );
    assert!(!f.0.join("type.wasm").exists());
}

#[test]
fn source_and_artifact_run_use_the_same_wasm_runtime() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='app::main'\n",
    );
    f.write("src/app.mb", "fn main() -> i32 { 42 }");
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert_eq!(
        String::from_utf8(source.stdout).unwrap(),
        "Result: i32(42)\n"
    );

    let build = f.run(&["build", "--output", "app.wasm"]);
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let artifact = f.run(&["run", "app.wasm"]);
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(
        String::from_utf8(artifact.stdout).unwrap(),
        "Result: i32(42)\n"
    );
    let bare = Fixture::new();
    fs::copy(f.0.join("app.wasm"), bare.0.join("app.wasm")).unwrap();
    let without_project = bare.run(&["run", "app.wasm"]);
    assert!(
        without_project.status.success(),
        "{}",
        String::from_utf8_lossy(&without_project.stderr)
    );
    assert_eq!(
        String::from_utf8(without_project.stdout).unwrap(),
        "Result: i32(42)\n"
    );

    f.write("src/app.mb", "fn main() {}");
    let unit_source = f.run(&["run"]);
    assert!(unit_source.status.success());
    assert_eq!(
        String::from_utf8(unit_source.stdout).unwrap(),
        "Result: Unit\n"
    );
    let unit_build = f.run(&["build", "--output", "unit.wasm"]);
    assert!(unit_build.status.success());
    let unit_artifact = f.run(&["run", "unit.wasm"]);
    assert!(unit_artifact.status.success());
    assert_eq!(
        String::from_utf8(unit_artifact.stdout).unwrap(),
        "Result: Unit\n"
    );
}

#[test]
fn run_reports_runtime_and_compile_failures_with_nonzero_status() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='app::main'\n",
    );
    f.write(
        "src/app.mb",
        "fn main() -> i32 { let value := 2147483647; value + 1 }",
    );
    let output = f.run(&["run"]);
    assert_eq!(output.status.code(), Some(1));
    let message = String::from_utf8(output.stderr).unwrap();
    assert!(message.contains("RE007"), "{message}");
    assert!(
        message.contains("integer overflow in addition"),
        "{message}"
    );
    assert!(message.contains("app.mb:1:"), "{message}");

    f.write("bad.wasm", "not a wasm module");
    assert!(err(f.run(&["run", "bad.wasm"]), "RE001").contains("invalid WebAssembly"));
    let build = f.run(&["build", "--output", "app.wasm"]);
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    assert!(
        err(f.run(&["run", "app.wasm", "--entry", "missing"]), "RE004")
            .contains("missing function export")
    );

    f.write(
        "src/app.mb",
        "fn main() { let value := [1]; let moved := value; let again := value; }",
    );
    let message = err(f.run(&["run"]), "BE001");
    assert!(message.contains("app.mb:1:"), "{message}");

    f.write("src/app.mb", "fn main(value: i32) -> i32 { value }");
    assert!(err(f.run(&["run"]), "RE005").contains("takes 1 parameter"));
}

#[test]
fn ownership_project_checks_resolved_roots_and_imported_moves() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='main::main'\n[export]\nconsume='api::consume'\n",
    );
    f.write("src/api.mb", "pub fn consume(value: array<i32, 1>) {}");
    f.write(
        "src/main.mb",
        "use api::consume; fn main() { let value := [1]; consume(value); consume(value); }",
    );
    let message = err(f.run(&["ownership-project"]), "BE001");
    assert!(message.contains("main.mb:1:"), "{message}");
    assert!(message.contains("value"));

    // Library mode follows exports and must not load the application's entry.
    f.write("src/main.mb", "not valid source syntax");
    let output = f.run(&["ownership-project", "--lib"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("library exports"));
    assert!(text.contains("supported moves, loans and aggregate access checked"));
    assert!(text.contains("complete language safety not established"));
}

#[test]
fn ownership_project_accepts_supported_imported_calls() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='main::main'\n[export]\nadd='math::add'\n[prelude]\nother_add='math::add'\n",
    );
    f.write("src/math.mb", "pub fn add(a: i32, b: i32) -> i32 { a + b }");
    f.write(
        "src/main.mb",
        "use self::math::add as math_add; fn main() -> i32 { math_add(1, 2) + other_add(3, 4) + self::math::add(5, 6) }",
    );
    let output = f.run(&["ownership-project"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    f.write(
        "src/main.mb",
        "use absent::consume; fn main() { consume(1); }",
    );
    assert!(err(f.run(&["ownership-project"]), "ME003").contains("unavailable"));
}

#[test]
fn resolve_uses_target_roots_and_ignores_unreachable_sources() {
    let f = Fixture::new();
    f.write(
        "nested/project.toml",
        "[package]\nname='demo'\nentry='main::main'\n[export]\nadd='math::add'\n",
    );
    f.write(
        "nested/src/main.mb",
        "use self::math::add; fn main() -> i32 { add(1, 2) }",
    );
    f.write(
        "nested/src/math.mb",
        "pub fn add(a: i32, b: i32) -> i32 { a + b }",
    );
    f.write("nested/src/unreachable.mb", "not valid source syntax");
    let app = f.run(&["resolve", "--project", "nested/project.toml"]);
    assert!(app.status.success(), "{:?}", app);
    assert!(app.stderr.is_empty());
    let text = String::from_utf8(app.stdout).unwrap();
    assert!(
        text.contains("Resolved application entry: 2 reachable module(s)"),
        "{text}"
    );
    assert!(text.contains("names checked; further semantics, types, and ownership not checked"));
    assert!(text.contains("  main -> main.mb\n  math -> math.mb\n"));
    assert!(!text.contains("unreachable"));
    let lib = f.run(&["resolve", "--lib", "--project", "nested/project.toml"]);
    assert!(lib.status.success(), "{:?}", lib);
    let text = String::from_utf8(lib.stdout).unwrap();
    assert!(text.contains("Resolved library exports: 1 reachable module(s)"));
    assert!(text.contains("  math -> math.mb\n"));
    assert!(!text.contains("  main ->"));
}

#[test]
fn resolve_renders_source_diagnostics_and_root_errors() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='main::main'\n[export]\nadd='math::add'\n",
    );
    f.write("src/main.mb", "fn main() { unknown_name; }");
    f.write("src/math.mb", "fn add() {}");
    let message = err(f.run(&["resolve"]), "NE001");
    assert!(message.contains("main.mb:1:"), "{message}");
    assert!(message.contains("unknown_name"));
    let message = err(f.run(&["resolve", "--lib"]), "ME007");
    assert!(message.contains("private"));
    f.write("src/main.mb", "fn main() { let x = 1; }");
    let message = err(f.run(&["resolve"]), "SE002");
    assert!(message.contains("main.mb:1:"), "{message}");
    f.write(
        "project.toml",
        "[package]\nname='demo'\n[export]\nadd='math::add'\n",
    );
    err(f.run(&["resolve"]), "ME001");
}

#[test]
fn syntax_reports_source_diagnostics_without_claiming_semantic_validation() {
    let f = Fixture::new();
    f.write("valid.mb", "fn main() -> i32 { unknown_name }");
    let output = f.run(&["syntax", "valid.mb"]);
    assert!(output.status.success());
    assert!(String::from_utf8(output.stdout)
        .unwrap()
        .contains("semantics not checked"));
    f.write("broken.mb", "fn main() { let x = 1; }");
    let message = err(f.run(&["syntax", "broken.mb"]), "SE002");
    assert!(message.contains("broken.mb:1:"));
    assert!(message.contains("let x = 1"));
    err(f.run(&["syntax"]), "PE004");
    err(f.run(&["syntax", "missing.mb"]), "PE001");
    err(f.run(&["syntax", "valid.mb", "extra.mb"]), "PE004");
}

#[test]
fn standalone_analysis_checks_types_and_loop_control() {
    let f = Fixture::new();
    f.write("valid.mb", "fn main() -> i32 { let value := 2; value + 3 }");
    let output = f.run(&["analyze", "valid.mb"]);
    assert!(output.status.success());
    assert!(String::from_utf8_lossy(&output.stdout).contains("ownership not checked"));
    f.write("invalid.mb", "fn main() { break; let value: bool = 1; }");
    let output = f.run(&["analyze", "invalid.mb"]);
    let message = err(output, "TE020");
    assert!(message.contains("TE002"));
    assert!(message.contains("invalid.mb:1:"));
    f.write("syntax.mb", "fn main( {");
    let message = err(f.run(&["analyze", "syntax.mb"]), "SE002");
    assert!(!message.contains("TE"));
}

#[test]
fn standalone_ownership_checks_moves_and_renders_source_errors() {
    let f = Fixture::new();
    f.write(
        "moves.mb",
        "fn main() { let x := [1]; let y := x; let z := x; }",
    );
    let message = err(f.run(&["ownership", "moves.mb"]), "BE001");
    assert!(message.contains("moves.mb:1:"), "{message}");
    assert!(message.contains("x"));

    f.write("reads.mb", "fn main() { let x := 1; x + x; }");
    let output = f.run(&["ownership", "reads.mb"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout)
        .contains("supported moves, loans and aggregate access checked"));

    f.write(
        "reinit.mb",
        "fn g(a: i32, b: i32) {} fn main() { var x := 1; g(x, { x = 2; 0 }); x + 1; }",
    );
    let output = f.run(&["ownership", "reinit.mb"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    f.write("types.mb", "fn main() { let x: bool = 1; }");
    assert!(err(f.run(&["ownership", "types.mb"]), "TE002").contains("types.mb:1:"));
    f.write("syntax.mb", "fn main( {");
    assert!(err(f.run(&["ownership", "syntax.mb"]), "SE002").contains("syntax.mb:1:"));
    for access in ["borrow", "share"] {
        f.write("access.mb", &format!("fn main(x: {access} i32) {{}}"));
        let output = f.run(&["ownership", "access.mb"]);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn project_analysis_checks_imported_call_types() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='test'\nentry='main::main'\n[export]\nadd='math::add'\n",
    );
    f.write("src/math.mb", "pub fn add(x: i32) -> i32 { x + 1 }");
    f.write("src/main.mb", "use math::add; fn main() -> i32 { add(2) }");
    assert!(f.run(&["analyze-project"]).status.success());
    assert!(f.run(&["analyze-project", "--lib"]).status.success());
    f.write(
        "src/main.mb",
        "use math::add; fn main() -> i32 { add(false) }",
    );
    let message = err(f.run(&["analyze-project"]), "TE002");
    assert!(message.contains("main.mb:1:"));
    assert!(f.run(&["analyze-project", "--lib"]).status.success());
}

#[test]
fn u8_to_u32_cast_and_method_run_from_source_and_standalone_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='u8-widening'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn main() -> u32 ! Error {
            let bytes: array<u8, 4> = [0, 127, 128, 255];
            let value := bytes[0] as u32 + bytes[1].to_u32()
                + bytes[2] as u32 + bytes[3].to_u32();
            let precedence := bytes[2] as u32 * 2 + 1;
            Ok(value + precedence - 257)
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(u32(510))\n");
    let build = f.run(&["build", "--output", "widen.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "widen.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn numeric_casts_reject_nonnumeric_types_and_to_u32_stays_u8_only() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='u8-widening-errors'\nentry='main::main'\n",
    );
    for (source, code, message) in [
        (
            "fn main() -> u32 { let bytes: array<u8, 1> = [42]; let value: u32 = bytes[0]; value }",
            "TE002",
            "expected u32, found u8",
        ),
        (
            "fn main() -> u32 { true as u32 }",
            "TE007",
            "integer or floating-point source and target",
        ),
        (
            "fn main() -> u32 { let value: u16 = 255; value.to_u32() }",
            "TE007",
            "requires a u8 value",
        ),
        (
            "fn main() -> u32 { let bytes: array<u8, 1> = [42]; bytes[0].to_u32(1) }",
            "TE007",
            "takes no arguments",
        ),
    ] {
        f.write("src/main.mb", source);
        let diagnostic = err(f.run(&["build"]), code);
        assert!(diagnostic.contains(message), "{source}: {diagnostic}");
    }
}

#[test]
fn numeric_casts_participate_in_constant_checks() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='u8-widening-constants'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn main() -> u32 { let byte: u8 = 255; byte as u32 + 1 }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(256)\n");

    f.write(
        "src/main.mb",
        "fn main() -> i8 { let value: u32 = 255; value as i8 }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: i8(-1)\n");

    f.write("src/main.mb", "fn main() -> i8 { 255 as u8 as i8 + 1 }");
    let static_cast = f.run(&["run"]);
    assert!(static_cast.status.success(), "{static_cast:?}");
    assert_eq!(static_cast.stdout, b"Result: i8(0)\n");
    let static_build = f.run(&["build", "--output", "constant-cast.wasm"]);
    assert!(static_build.status.success(), "{static_build:?}");
    let static_artifact = f.run(&["run", "constant-cast.wasm"]);
    assert_eq!(static_artifact.stdout, b"Result: i32(0)\n");

    f.write(
        "src/main.mb",
        "fn increment(value: i8) -> i8 { value + 1 } fn main() -> i8 { increment(-1) }",
    );
    let dynamic_cast = f.run(&["run"]);
    assert!(dynamic_cast.status.success(), "{dynamic_cast:?}");
    assert_eq!(dynamic_cast.stdout, static_cast.stdout);
    let dynamic_build = f.run(&["build", "--output", "dynamic-cast.wasm"]);
    assert!(dynamic_build.status.success(), "{dynamic_build:?}");
    let dynamic_artifact = f.run(&["run", "dynamic-cast.wasm"]);
    assert_eq!(dynamic_artifact.stdout, b"Result: i32(0)\n");

    f.write("src/main.mb", "fn main() -> i8 { 127 as i8 + 1 }");
    let overflow = err(f.run(&["build"]), "LE001");
    assert!(
        overflow.contains("integer overflow in statically known expression"),
        "{overflow}"
    );

    f.write(
        "src/main.mb",
        "fn increment(value: i8) -> i8 { value + 1 } fn main() -> i8 { increment(127) }",
    );
    let dynamic_overflow = err(f.run(&["run"]), "RE007");
    assert!(
        dynamic_overflow.contains("integer overflow in addition"),
        "{dynamic_overflow}"
    );
}

#[test]
fn numeric_cast_matrix_and_rust_boundaries_match_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='cast-matrix'\nentry='main::main'\n",
    );
    let types = [
        "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f32", "f64",
    ];
    let boundaries: [(&str, &[&str]); 10] = [
        ("i8", &["-128", "-1", "0", "127"]),
        ("i16", &["-32768", "-1", "0", "32767"]),
        ("i32", &["-2147483647", "-1", "0", "2147483647"]),
        (
            "i64",
            &["-9223372036854775807", "-1", "0", "9223372036854775807"],
        ),
        ("u8", &["0", "1", "255"]),
        ("u16", &["0", "1", "65535"]),
        ("u32", &["0", "1", "4294967295"]),
        ("u64", &["0", "1", "18446744073709551615"]),
        ("f32", &["-3.4e38", "-1.9", "0.9", "1.9", "3.4e38"]),
        ("f64", &["-1e300", "-1.9", "0.9", "1.9", "1e300"]),
    ];
    let format_float = |value: f64| {
        if value.is_infinite() {
            if value.is_sign_negative() {
                "(-1.0 / 0.0)".to_owned()
            } else {
                "(1.0 / 0.0)".to_owned()
            }
        } else {
            format!("{value:?}")
        }
    };
    let mut source = String::new();
    let mut calls = String::new();
    let mut call_index = 0;
    for (from, values) in boundaries {
        let source_is_float = from.starts_with('f');
        for (sample_index, literal) in values.iter().enumerate() {
            let integer = (!source_is_float).then(|| literal.parse::<i128>().unwrap());
            let mut float = source_is_float.then(|| literal.parse::<f64>().unwrap());
            if from == "f32" {
                float = float.map(|value| (value as f32) as f64);
            }
            let function = format!("check_{from}_{sample_index}");
            source.push_str(&format!("fn {function}(value: {from}) -> bool {{\n"));
            for to in types {
                let expected = match to {
                    "i8" => integer
                        .map(|v| format!("{}", v as i8))
                        .or_else(|| float.map(|v| format!("{}", v as i8)))
                        .unwrap(),
                    "i16" => integer
                        .map(|v| format!("{}", v as i16))
                        .or_else(|| float.map(|v| format!("{}", v as i16)))
                        .unwrap(),
                    "i32" => integer
                        .map(|v| format!("{}", v as i32))
                        .or_else(|| float.map(|v| format!("{}", v as i32)))
                        .unwrap(),
                    "i64" => integer
                        .map(|v| format!("{}", v as i64))
                        .or_else(|| float.map(|v| format!("{}", v as i64)))
                        .unwrap(),
                    "u8" => integer
                        .map(|v| format!("{}", v as u8))
                        .or_else(|| float.map(|v| format!("{}", v as u8)))
                        .unwrap(),
                    "u16" => integer
                        .map(|v| format!("{}", v as u16))
                        .or_else(|| float.map(|v| format!("{}", v as u16)))
                        .unwrap(),
                    "u32" => integer
                        .map(|v| format!("{}", v as u32))
                        .or_else(|| float.map(|v| format!("{}", v as u32)))
                        .unwrap(),
                    "u64" => integer
                        .map(|v| format!("{}", v as u64))
                        .or_else(|| float.map(|v| format!("{}", v as u64)))
                        .unwrap(),
                    "f32" => integer
                        .map(|v| format_float(v as f32 as f64))
                        .or_else(|| float.map(|v| format_float(v as f32 as f64)))
                        .unwrap(),
                    "f64" => integer
                        .map(|v| format_float(v as f64))
                        .or_else(|| float.map(format_float))
                        .unwrap(),
                    _ => unreachable!(),
                };
                source.push_str(&format!("    value as {to} == {expected} &&\n"));
            }
            source.push_str("    true\n}\n");
            calls.push_str(&format!(
                "    if !{function}({literal}) {{ return Err(Error {{ code: {} }}); }}\n",
                call_index + 1
            ));
            call_index += 1;
        }
    }
    source.push_str("fn main() -> bool ! Error {\n");
    source.push_str(&calls);
    for ty in types {
        let one = if ty.starts_with('f') { "1.0" } else { "1" };
        source.push_str(&format!("    let source_{ty}: {ty} = {one};\n"));
    }
    for from in types {
        for to in types {
            let expected = if to.starts_with('f') { "1.0" } else { "1" };
            source.push_str(&format!("    if source_{from} as {to} != {expected} {{ return Err(Error {{ code: 1 }}); }}\n"));
        }
    }
    source.push_str(
        r#"
    let left: i32 = 4;
    let right: u32 = 5;
    let mixed_add: u32 = left as u32 + right;
    let mixed_mul: u32 = left as u32 * right;
    let byte: i8 = 255 as i8;
    let all_bits: u32 = 4294967295;
    let signed: i32 = all_bits as i32;
    let unsigned: u64 = (-1 as i32) as u64;
    let fraction: i32 = (-1.9) as i32;
    let nan: u32 = (0.0 / 0.0) as u32;
    let saturated: u64 = 1e300 as u64;
    let rounded: u64 = 16777217 as f32 as u64;
    let narrowed: f32 = 16777217 as f32;
    let positive_infinity: u64 = (1.0 / 0.0) as u64;
    let negative_infinity: u64 = (-1.0 / 0.0) as u64;
    let high_saturated: i8 = 1e300 as i8;
    let low_saturated: i8 = (-1e300) as i8;
    let float_overflow: f32 = 1e300 as f32;
    Ok(byte == -1 && signed == -1 && unsigned == 18446744073709551615
        && mixed_add == 9 && mixed_mul == 20
        && fraction == -1 && nan == 0 && saturated == 18446744073709551615
        && rounded == 16777216 && narrowed == 16777216.0
        && positive_infinity == 18446744073709551615 && negative_infinity == 0
        && high_saturated == 127 && low_saturated == -128
        && float_overflow == (1.0 / 0.0))
}
"#,
    );
    f.write("src/main.mb", &source);
    let run = f.run(&["run"]);
    assert!(run.status.success(), "{run:?}");
    assert_eq!(run.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "casts.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "casts.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, run.stdout);
}

#[test]
fn u32_wrapping_add_and_mul_match_source_and_standalone_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='u32-wrapping'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn main() -> u32 ! Error {
            let constant: u32 = 4294967295.wrapping_add(1);
            if constant != 0 { return Err(Error { code: 1 }); }
            let max: u32 = 4294967295;
            Ok(max.wrapping_add(1).wrapping_add(max.wrapping_mul(2)).wrapping_add(2))
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(u32(0))\n");
    let build = f.run(&["build", "--output", "wrapping.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "wrapping.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);

    f.write("src/main.mb", "fn main() -> u32 { 4294967295 + 1 }");
    let static_overflow = err(f.run(&["build"]), "LE001");
    assert!(
        static_overflow.contains("integer overflow in statically known expression"),
        "{static_overflow}"
    );

    f.write(
        "src/main.mb",
        "fn add(left: u32, right: u32) -> u32 { left + right } fn main() -> u32 { add(4294967295, 1) }",
    );
    let dynamic_overflow = err(f.run(&["run"]), "RE007");
    assert!(
        dynamic_overflow.contains("integer overflow in addition"),
        "{dynamic_overflow}"
    );
}

#[test]
fn u32_wrapping_methods_reject_wrong_types_and_arity() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='u32-wrapping-errors'\nentry='main::main'\n",
    );
    for source in [
        "fn main() -> u32 { let value: i32 = 1; value.wrapping_add(1) }",
        "fn main() -> u32 { let value: u32 = 1; value.wrapping_mul(1, 2) }",
    ] {
        f.write("src/main.mb", source);
        let diagnostic = err(f.run(&["build"]), "TE007");
        assert!(diagnostic.contains("wrapping"), "{diagnostic}");
    }
}

#[test]
fn u32_bitwise_and_shifts_match_source_and_standalone_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='u32-bit-ops'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        fn shift_left(value: u32, count: u32) -> u32 { value << count }
        fn shift_right(value: u32, count: u32) -> u32 { value >> count }
        fn main() -> u32 ! Error {
            let high: u32 = 2147483648;
            let pattern: u32 = 2863311530;
            let method_constant: u32 = 4294967295.bit_xor(0);
            let parity := 1 | 2 ^ 3 & 7;
            if method_constant != 4294967295 || parity != 1 || (12 ^ 10) != 6
                || pattern.bit_xor(1431655765) != 4294967295
                || pattern.bit_and(15) != 10 || pattern.bit_or(5) != 2863311535
                || 1 << 31 != high || high >> 31 != 1 || 1 << 0 != 1
                || shift_left(1, 0) != 1 || shift_left(1, 31) != high
                || shift_right(high, 31) != 1
                || 4294967295 << 1 != 4294967294 {
                return Err(Error { code: 1 });
            }
            Ok(42)
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(u32(42))\n");
    let build = f.run(&["build", "--output", "bits.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bits.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);

    for count in [32, 33] {
        f.write(
            "src/main.mb",
            &format!("fn main() -> u32 {{ 1 << {count} }}"),
        );
        let static_shift = err(f.run(&["build"]), "LE003");
        assert!(
            static_shift.contains("shift count must be less than 32"),
            "{static_shift}"
        );

        f.write(
            "src/main.mb",
            &format!("fn shift(value: u32, count: u32) -> u32 {{ value >> count }} fn main() -> u32 ! Error {{ Ok(shift(1, {count})) }}"),
        );
        let dynamic_shift = err(f.run(&["run"]), "RE007");
        assert!(
            dynamic_shift.contains("shift count must be less than 32"),
            "{dynamic_shift}"
        );
    }

    for (source, diagnostic_code, message) in [
        (
            "fn main() -> u32 { let value: i32 = 1; value.bit_and(1) }",
            "TE007",
            "bitwise methods require u32 operands",
        ),
        (
            "fn main() -> u32 { let value: u32 = 1; value.bit_xor(1, 2) }",
            "TE007",
            "bitwise methods take one u32 argument",
        ),
        (
            "fn main() -> u32 { let count: i32 = 1; let value: u32 = 1; value << count }",
            "TE002",
            "expected u32",
        ),
    ] {
        f.write("src/main.mb", source);
        let diagnostic = err(f.run(&["build"]), diagnostic_code);
        assert!(diagnostic.contains(message), "{source}: {diagnostic}");
    }
}

#[test]
fn published_numeric_analysis_example_remains_valid() {
    let f = Fixture::new();
    f.write(
        "numeric.mb",
        include_str!("../../../examples/analysis/numeric.mb"),
    );
    let output = f.run(&["analyze", "numeric.mb"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn library_build_excludes_same_module_entry_and_unrelated_bodies() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='main::main'\n[export]\nanswer='main::answer'\n",
    );
    f.write("src/main.mb", "fn main() -> i32 { 99 } fn helper() -> i32 { 42 } fn unused() -> i32 { 7 } pub fn answer() -> i32 { helper() }");
    let output = f.run(&["build", "--lib", "--output", "library.wasm"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let bytes = fs::read(f.0.join("library.wasm")).unwrap();
    wasmparser::validate(&bytes).unwrap();
    let count = wasmparser::Parser::new(0)
        .parse_all(&bytes)
        .find_map(|payload| match payload.unwrap() {
            wasmparser::Payload::FunctionSection(section) => Some(section.count()),
            _ => None,
        })
        .unwrap();
    assert_eq!(count, 2);
    assert_eq!(wasm_exports(&bytes), vec!["answer".to_string()]);
}

#[test]
fn primitive_reference_checks_and_execution_work_in_cli() {
    let f = Fixture::new();
    f.write(
        "access.mb",
        "fn update(x: share i32) { x += 1; } fn main() { var x := 1; update(x.share()); x + 1; }",
    );
    let output = f.run(&["ownership", "access.mb"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    f.write(
        "conflict.mb",
        "fn main() { var x := 1; let r := x.borrow(); x = 2; r + 1; }",
    );
    assert!(err(f.run(&["ownership", "conflict.mb"]), "BE005").contains("conflict.mb:1:"));
    f.write(
        "project.toml",
        r#"[package]
name = "references"
entry = "main::main"
"#,
    );
    f.write(
        "src/main.mb",
        "fn update(x: share i32) { x += 1; } fn main() { var x := 1; update(x.share()); }",
    );
    let output = f.run(&["ownership-project"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = f.run(&["build"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(source.stdout, artifact.stdout);
}

#[test]
fn share_writes_are_visible_across_modules_in_source_and_artifact_runs() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        r#"[package]
name = "reference-result"
entry = "main::main"
"#,
    );
    f.write(
        "src/math.mb",
        "pub fn update(value: share i32) { value += 2; }",
    );
    f.write("src/main.mb", "use self::math::update; fn main() -> i32 { var value := 40; update(value.share()); value }");
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert!(String::from_utf8_lossy(&source.stdout).contains("42"));
    let built = f.run(&["build"]);
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(source.stdout, artifact.stdout);
}

#[test]
fn fixed_array_syntax_is_inspectable_and_read_only_arrays_are_executable() {
    let f = Fixture::new();
    f.write(
        "arrays.mb",
        "fn main() { let values: array<i32, 3> = [1, 2, 3]; values[0]; }",
    );
    let parsed = f.run(&["syntax", "arrays.mb"]);
    assert!(
        parsed.status.success(),
        "{}",
        String::from_utf8_lossy(&parsed.stderr)
    );
    let analyzed = f.run(&["analyze", "arrays.mb"]);
    assert!(
        analyzed.status.success(),
        "{}",
        String::from_utf8_lossy(&analyzed.stderr)
    );
    let owned = f.run(&["ownership", "arrays.mb"]);
    assert!(
        owned.status.success(),
        "{}",
        String::from_utf8_lossy(&owned.stderr)
    );
    // Repetition executes; repeating an owned binding is a repeated move.
    f.write("repeat.mb", "fn main() { let values := [1; 3]; }");
    let repeated = f.run(&["ownership", "repeat.mb"]);
    assert!(
        repeated.status.success(),
        "{}",
        String::from_utf8_lossy(&repeated.stderr)
    );
    f.write(
        "moved.mb",
        "fn main() { let x := [1, 2]; let values := [x; 3]; }",
    );
    assert!(err(f.run(&["ownership", "moved.mb"]), "BE001").contains("'x'"));
    f.write("nested.mb", "fn main() { let values := [[1; 2]; 3]; }");
    assert!(f.run(&["ownership", "nested.mb"]).status.success());
    // Reference-typed elements stay gated.
    f.write(
        "refs.mb",
        "fn main() { var x := 1; let values := [x.borrow()]; }",
    );
    err(f.run(&["ownership", "refs.mb"]), "TE017");
}

fn run_both(f: &Fixture, source: &str) -> String {
    f.write("src/app.mb", source);
    let direct = f.run(&["run"]);
    assert!(
        direct.status.success(),
        "{}",
        String::from_utf8_lossy(&direct.stderr)
    );
    let built = f.run(&["build"]);
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(direct.stdout, artifact.stdout);
    String::from_utf8_lossy(&direct.stdout).into_owned()
}

#[test]
fn array_mutation_repetition_and_moves_run_from_source_and_artifact() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='arrays'\nentry='app::main'\n",
    );
    // The element expression runs once per slot, in order: elements are 1, 2, 3.
    let out = run_both(
        &f,
        "fn next(c: share i32) -> i32 { c += 1; c + 0 } fn main() -> i32 { var n := 0; let a := [next(n.share()); 3]; a[0] * 100 + a[1] * 10 + a[2] }",
    );
    assert!(out.contains("123"), "{out}");
    let out = run_both(
        &f,
        "fn main() -> i32 { var a := [0; 8]; var i := 0; loop { if i >= 8 { break; } a[i] = i * i; i += 1; } a[3] += 1; let b := a; b[3] + b[7] }",
    );
    assert!(out.contains("59"), "{out}");
    // Element writes trap out of range from both runs.
    f.write(
        "src/app.mb",
        "fn put(n: i32) -> i32 { var a := [1, 2]; a[n] = 3; a[0] + 0 } fn main() -> i32 { let n := 1; put(n + 1) }",
    );
    let source = f.run(&["run"]);
    assert_eq!(source.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&source.stderr).contains("RE007"));
    assert!(f.run(&["build"]).status.success());
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert_eq!(artifact.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&artifact.stderr).contains("RE007"));
    // Compile-time rejections.
    f.write(
        "src/app.mb",
        "fn main() -> i32 { let a := [1]; a[0] = 2; 0 }",
    );
    err(f.run(&["run"]), "TE004");
    f.write(
        "src/app.mb",
        "fn main() -> i32 { let a := [1, 2]; let b := a; a[0] + b[0] }",
    );
    err(f.run(&["run"]), "BE001");
    f.write(
        "src/app.mb",
        "fn main() -> i32 { var a := [1]; a[1] = 2; 0 }",
    );
    err(f.run(&["run"]), "TE008");
    f.write(
        "src/app.mb",
        "fn main() -> i32 { let a: array<i64, 65537> = [0; 65537]; 0 }",
    );
    assert!(err(f.run(&["run"]), "LE900").contains("configured stack size"));
}

#[test]
fn array_programs_run_from_source_and_artifact_with_dynamic_bounds_traps() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='arrays'\nentry='app::main'\n",
    );
    f.write(
        "src/app.mb",
        "fn main() -> i32 { let a := [1, 2, 3]; a[0] + a[2] }",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert!(String::from_utf8_lossy(&source.stdout).contains('4'));
    let built = f.run(&["build"]);
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(source.stdout, artifact.stdout);

    // A dynamic out-of-range index traps from both source and artifact runs.
    f.write(
        "src/app.mb",
        "fn pick(n: i32) -> i32 { let a := [1, 2, 3]; a[n] + 0 } fn main() -> i32 { let n := 2; pick(n + 1) }",
    );
    let source = f.run(&["run"]);
    assert_eq!(source.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&source.stderr).contains("RE007"));
    let built = f.run(&["build"]);
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert_eq!(artifact.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&artifact.stderr).contains("RE007"));

    // Extracting an aggregate element into a binding is a compile-time error.
    f.write(
        "src/app.mb",
        "fn main() -> i32 { let a := [[1, 2], [3, 4]]; let x := a[1]; 0 }",
    );
    err(f.run(&["run"]), "TE022");
}

#[test]
fn fixed_array_types_are_checked_without_enabling_execution() {
    let f = Fixture::new();
    f.write(
        "arrays.mb",
        "fn main() { let values: array<i8, 3> = [1, 2, 3]; let nested := [[1, 2], [3, 4]]; }",
    );
    let checked = f.run(&["analyze", "arrays.mb"]);
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stderr)
    );
    // Nested arrays are executable too.
    let owned = f.run(&["ownership", "arrays.mb"]);
    assert!(
        owned.status.success(),
        "{}",
        String::from_utf8_lossy(&owned.stderr)
    );
    f.write(
        "invalid.mb",
        "fn main() { let values: array<i32, 3> = [1, 2]; }",
    );
    let invalid = f.run(&["analyze", "invalid.mb"]);
    assert!(!invalid.status.success());
    assert!(String::from_utf8_lossy(&invalid.stderr).contains("invalid.mb:1:"));
}

#[test]
fn array_parameters_run_from_source_and_artifact() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='arrays'\nentry='app::main'\n",
    );
    let sum = "fn sum(a: borrow array<i32, 3>) -> i32 { var i := 0; var t := 0; loop { if i >= 3 { break; } t += a[i]; i += 1; } t } ";
    let fill = "fn fill(a: share array<i32, 4>, v: i32) { var i := 0; loop { if i >= 4 { break; } a[i] = v + i; i += 1; } } ";
    // A borrow parameter called twice on the same array.
    let out = run_both(
        &f,
        &format!(
            "{sum} fn main() -> i32 {{ let a := [1, 2, 3]; sum(a.borrow()) * 10 + sum(a.borrow()) }}"
        ),
    );
    assert!(out.contains("66"), "{out}");
    // The caller observes writes made through a share parameter.
    let out = run_both(
        &f,
        &format!("{fill} fn main() -> i32 {{ var a := [0; 4]; fill(a.share(), 10); a[0] + a[3] }}"),
    );
    assert!(out.contains("23"), "{out}");
    // An owned parameter moves the source and the callee sees the contents.
    let out = run_both(
        &f,
        "fn f(a: array<i32, 3>) -> i32 { a[0] + a[2] } fn main() -> i32 { let a := [1, 2, 3]; f(a) + f([10, 20, 30]) }",
    );
    assert!(out.contains("44"), "{out}");
    // Recursion with an array borrow parameter.
    let out = run_both(
        &f,
        "fn rec(a: borrow array<i32, 3>, n: i32) -> i32 { let m := n + 0; var l := [m + 0, m * 2, m * 3]; if m + 0 == 0 { a[0] + 0 } else { let r := rec(a, m - 1); r + l[2] } } fn main() -> i32 { let a := [100, 2, 3]; rec(a.borrow(), 3) }",
    );
    assert!(out.contains("118"), "{out}");

    // A dynamic out-of-range index inside the callee traps in both runs.
    f.write(
        "src/app.mb",
        "fn get(a: borrow array<i32, 3>, n: i32) -> i32 { a[n] + 0 } fn main() -> i32 { let a := [1, 2, 3]; let n := 2; get(a.borrow(), n + 1) }",
    );
    let source = f.run(&["run"]);
    assert_eq!(source.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&source.stderr).contains("RE007"));
    assert!(f.run(&["build"]).status.success());
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert_eq!(artifact.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&artifact.stderr).contains("RE007"));

    // Compile-time diagnostics.
    f.write(
        "src/app.mb",
        "fn get(a: borrow array<i32, 3>) -> i32 { a[3] + 0 } fn main() -> i32 { 0 }",
    );
    err(f.run(&["run"]), "TE008");
    f.write(
        "src/app.mb",
        "fn get(a: borrow array<i32, 3>) -> i32 { a[0] + 0 } fn main() -> i32 { let a := [1, 2]; get(a.borrow()) }",
    );
    err(f.run(&["run"]), "TE002");
    f.write(
        "src/app.mb",
        "fn own(a: array<i32, 2>) -> i32 { a[0] + 0 } fn main() -> i32 { let a := [1, 2]; let r := own(a); a[0] + r }",
    );
    err(f.run(&["run"]), "BE001");
    f.write(
        "src/app.mb",
        "fn put(a: borrow array<i32, 2>) { a[0] = 1; } fn main() -> i32 { 0 }",
    );
    err(f.run(&["run"]), "TE004");
    f.write(
        "src/app.mb",
        "fn two(a: share array<i32, 2>, b: share array<i32, 2>) {} fn main() -> i32 { var a := [1, 2]; two(a.share(), a.share()); 0 }",
    );
    err(f.run(&["run"]), "BE005");
}

#[test]
fn array_results_if_values_and_nested_arrays_run_from_source_and_artifact() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='arrays'\nentry='app::main'\n",
    );
    let sum = "fn sum(a: borrow array<i32, 3>) -> i32 { var i := 0; var t := 0; loop { if i >= 3 { break; } t += a[i]; i += 1; } t } ";
    // A repetition-built result consumed by a borrow-taking sum and an owned call.
    let out = run_both(
        &f,
        &format!(
            "{sum} fn make(v: i32) -> array<i32, 3> {{ [v + 0; 3] }} fn own(a: array<i32, 3>) -> i32 {{ a[0] + a[2] }} fn main() -> i32 {{ let a := make(4); sum(a.borrow()) * 100 + own(make(5)) }}"
        ),
    );
    assert!(out.contains("1210"), "{out}");
    // An if-value chosen dynamically and recursion returning arrays.
    let out = run_both(
        &f,
        "fn pick(c: bool) -> array<i32, 2> { if c { [1, 2] } else { [3, 4] } } fn fib(n: i32) -> array<i32, 2> { if n <= 0 { return [0, 1]; } let p := fib(n - 1); [p[1] + 0, p[0] + p[1]] } fn main() -> i32 { let a := pick(true); let b := pick(false); let c := fib(10); a[1] * 1000 + b[0] * 100 + c[0] }",
    );
    assert!(out.contains("2355"), "{out}");
    // A 3x3 matrix filled by nested loops, then traced and summed.
    let out = run_both(
        &f,
        "fn main() -> i32 { var m := [[0; 3]; 3]; var i := 0; loop { if i >= 3 { break; } var j := 0; loop { if j >= 3 { break; } m[i][j] = i * 3 + j; j += 1; } i += 1; } var tr := 0; var total := 0; var k := 0; loop { if k >= 3 { break; } tr += m[k][k]; var l := 0; loop { if l >= 3 { break; } total += m[k][l]; l += 1; } k += 1; } tr * 100 + total }",
    );
    assert!(out.contains("1236"), "{out}");
    // Rows by borrow/share and a whole-row replacement.
    let out = run_both(
        &f,
        &format!(
            "{sum} fn zero(a: share array<i32, 3>) {{ a[0] = 0; a[1] = 0; a[2] = 0; }} fn main() -> i32 {{ var m := [[1, 2, 3], [4, 5, 6]]; zero(m[0].share()); m[1] = [7, 8, 9]; sum(m[0].borrow()) * 100 + sum(m[1].borrow()) }}"
        ),
    );
    assert!(out.contains("24"), "{out}");
    // Evaluation order of nested assignment: index, index, right-hand side.
    let out = run_both(
        &f,
        "fn d(log: share i32, k: i32) -> i32 { log = log * 10 + k; 0 } fn main() -> i32 { var log := 0; var m := [[0; 2]; 2]; m[d(log.share(), 1)][d(log.share(), 2)] = d(log.share(), 3); log }",
    );
    assert!(out.contains("123"), "{out}");

    // Either index of a nested read traps in both runs.
    for body in [
        "let m := [[1, 2], [3, 4]]; let i := 1; m[i + 1][0] + 0",
        "let m := [[1, 2], [3, 4]]; let i := 1; m[0][i + 1] + 0",
    ] {
        f.write("src/app.mb", &format!("fn main() -> i32 {{ {body} }}"));
        let source = f.run(&["run"]);
        assert_eq!(source.status.code(), Some(1));
        assert!(String::from_utf8_lossy(&source.stderr).contains("RE007"));
        assert!(f.run(&["build"]).status.success());
        let artifact = f.run(&["run", "target/memobits/app.wasm"]);
        assert_eq!(artifact.status.code(), Some(1));
        assert!(String::from_utf8_lossy(&artifact.stderr).contains("RE007"));
    }

    // Compile-time diagnostics.
    for (source, code) in [
        (
            "fn main() -> i32 { let m := [[1, 2], [3, 4]]; let r := m[0]; 0 }",
            "TE022",
        ),
        (
            "fn main() -> i32 { let m := [[1, 2], [3, 4]]; m[0][2] + 0 }",
            "TE008",
        ),
        (
            "fn main() -> i32 { let m := [[1, 2], [3, 4]]; m[2][0] + 0 }",
            "TE008",
        ),
        (
            "fn main() -> i32 { var m := [[1, 2], [3, 4]]; let r := m.borrow(); m[0][0] = 1; r[0][0] + 0 }",
            "BE005",
        ),
        (
            "fn make() -> array<i32, 2> { [1, 2] } fn main() -> i32 { let a := make(); let b := a; a[0] + 0 }",
            "BE001",
        ),
        (
            "fn make() -> array<i32, 2> { [1, 2] } fn main() -> i32 { make()[0] + 0 }",
            "TE017",
        ),
        ("fn main() -> array<i32, 2> { [1, 2] }", "LE900"),
        (
            "fn main() -> i32 { let m: array<array<i32, 4000>, 4000> = [[0; 4000]; 4000]; 0 }",
            "LE900",
        ),
    ] {
        f.write("src/app.mb", source);
        err(f.run(&["run"]), code);
    }
}

#[test]
fn primitive_copy_runs_from_source_and_artifact_and_is_checked() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='copies'\nentry='app::main'\n",
    );
    let out = run_both(
        &f,
        "fn mk(v: i32) -> array<i32, 3> { [v.copy(), v.copy() + 1, v + 2] } \
         fn swap(a: share array<i32, 3>, i: i32, j: i32) { let t := a[i].copy(); a[i] = a[j].copy(); a[j] = t; } \
         fn main() -> i32 { var a := mk(1); swap(a.share(), 0, 2); a[0] * 100 + a[1] * 10 + a[2] }",
    );
    assert!(out.contains("321"), "{out}");
    let out = run_both(
        &f,
        "fn pick(flags: borrow array<bool, 2>, i: i32) -> bool { flags[i].copy() } \
         fn main() -> i32 { let flags := [false, true]; let on := pick(flags.borrow(), 1); if on { 7 } else { 0 } }",
    );
    assert!(out.contains('7'), "{out}");
    // Compile-time rejections.
    for (source, code) in [
        (
            "fn main() -> i32 { let a := [1, 2]; let b := a.copy(); 0 }",
            "TE017",
        ),
        (
            "fn main() -> i32 { let a := [1, 2]; let b := a; a[0] + b[0] }",
            "BE001",
        ),
        (
            "fn main() -> i32 { let a := [[1, 2], [3, 4]]; let x := a[1]; 0 }",
            "TE022",
        ),
    ] {
        f.write("src/app.mb", source);
        err(f.run(&["run"]), code);
    }
}

#[test]
fn implicit_primitive_copies_run_from_source_and_artifact() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='implicit'\nentry='app::main'\n",
    );
    let out = run_both(
        &f,
        "type P { x: i32, y: i32 } \
         fn bump(n: i32) -> i32 { n + 1 } \
         fn mk(v: i32) -> array<i32, 3> { [v, v + 1, v + 2] } \
         fn get(r: borrow i32) -> i32 { r } \
         fn swap(a: share array<i32, 3>) { let t := a[0]; a[0] = a[2]; a[2] = t; } \
         fn main() -> i32 { \
           let x := 4; let y := x; \
           var i := 0; var acc := 0; loop { if i >= 3 { break; } acc += bump(i); i += 1; } \
           var a := mk(1); swap(a.share()); \
           let rep := [x; 3]; let p := P { x: 5, y: 6 }; let flags := [false, true]; let on := flags[1]; \
           let g := get(x.borrow()); \
           if on { x + y + acc + a[0] * 100 + rep[2] + bump(p.x) + g } else { 0 } }",
    );
    // 4 + 4 + 6 + 300 + 4 + 6 + 4
    assert!(out.contains("328"), "{out}");
    // Implicit copies are reads: a live share still conflicts.
    f.write(
        "src/app.mb",
        "fn main() -> i32 { var x := 1; var s := x.share(); let y := x; s += 1; y }",
    );
    err(f.run(&["run"]), "BE005");
}

#[test]
fn array_parameters_cross_modules_and_stay_out_of_exported_signatures() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='arrays'\nentry='main::main'\n",
    );
    f.write(
        "src/vec.mb",
        "pub fn total(a: borrow array<i32, 3>) -> i32 { var i := 0; var t := 0; loop { if i >= 3 { break; } t += a[i]; i += 1; } t }\n\
         pub fn scale(a: share array<i32, 3>, k: i32) { var i := 0; loop { if i >= 3 { break; } a[i] *= k; i += 1; } }\n\
         pub fn first(a: array<i32, 3>) -> i32 { a[0] + 0 }\n",
    );
    f.write(
        "src/main.mb",
        "use vec::total; use vec::scale; use vec::first;\n\
         fn main() -> i32 { var a := [1, 2, 3]; scale(a.share(), 10); let t := total(a.borrow()); t + first(a) }\n",
    );
    assert!(f.run(&["analyze-project"]).status.success());
    assert!(f.run(&["ownership-project"]).status.success());
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert!(String::from_utf8_lossy(&source.stdout).contains("70"));
    assert!(f.run(&["build"]).status.success());
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert_eq!(source.stdout, artifact.stdout);

    // Mismatched array types across a module boundary are type errors.
    f.write(
        "src/main.mb",
        "use vec::total; fn main() -> i32 { let a := [1, 2]; total(a.borrow()) }",
    );
    err(f.run(&["run"]), "TE002");

    // Arrays and array references are rejected in exported signatures.
    f.write("src/main.mb", "fn main() -> i32 { 0 }\n");
    f.write(
        "project.toml",
        "[package]\nname='arrays'\nentry='main::main'\n[export]\ntotal='vec::total'\nfirst='vec::first'\n",
    );
    let message = err(f.run(&["build", "--lib"]), "LE900");
    assert!(message.contains("arrays or array references"), "{message}");
    f.write(
        "project.toml",
        "[package]\nname='arrays'\nentry='main::main'\n[export]\nfirst='vec::first'\n",
    );
    err(f.run(&["build", "--lib"]), "LE900");
    f.write("src/main.mb", "fn main(a: array<i32, 2>) -> i32 { 0 }\n");
    err(f.run(&["run"]), "LE900");
}

#[test]
fn structs_run_from_source_and_artifact() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='structs'\nentry='app::main'\n",
    );
    let out = run_both(
        &f,
        "type P { x: i32, y: i32 } fn main() -> i32 { let p := P { x: 3, y: 4 }; p.x * p.y }",
    );
    assert!(out.contains("Result: i32(12)"), "{out}");
    // Mixed widths: every field reads back, `.copy()` yields an owned value.
    let out = run_both(
        &f,
        "type M { a: u8, b: i64, c: bool, d: f32, e: i16 } \
         fn main() -> i64 { let m := M { e: -7, a: 200, d: 1.5, c: true, b: 5000000000 }; \
             let b := m.b.copy(); if m.c { b + 1 } else { 0 } }",
    );
    assert!(out.contains("5000000001"), "{out}");
    // Initialisers run in source order, not declaration order.
    let out = run_both(
        &f,
        "type P { a: i32, b: i32, c: i32 } \
         fn next(c: share i32) -> i32 { c += 1; c.copy() } \
         fn main() -> i32 { var n := 0; \
             let p := P { c: next(n.share()), a: next(n.share()), b: next(n.share()) }; \
             p.a * 100 + p.b * 10 + p.c }",
    );
    assert!(out.contains("Result: i32(231)"), "{out}");
    // Bool field as a condition; alias to a struct; a parenthesised literal.
    let out = run_both(
        &f,
        "type Flags { on: bool, n: i32 } type F = Flags; \
         fn main() -> i32 { let f: F = F { n: 9, on: true }; if f.on { f.n + 1 } else { 0 } }",
    );
    assert!(out.contains("Result: i32(10)"), "{out}");
}

#[test]
fn struct_diagnostics_are_rendered_with_stable_codes() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='structs'\nentry='app::main'\n",
    );
    let head = "type P { x: i32, y: i32 } ";
    for (body, code, text) in [
        (
            "let p := P { x: 1 }; 0",
            "TE023",
            "missing field(s) in 'P' literal: y",
        ),
        (
            "let p := P { x: 1, y: 2, z: 3 }; 0",
            "TE023",
            "has no field 'z'",
        ),
        (
            "let p := P { x: 1, x: 2, y: 3 }; 0",
            "TE023",
            "more than once",
        ),
        (
            "let p := P { x: 1, y: true }; 0",
            "TE002",
            "expected i32, found bool",
        ),
        ("let p := Q { x: 1 }; 0", "NE003", "unknown type 'Q'"),
        ("let n := 1; n.x + 1", "TE024", "requires a struct value"),
        (
            "let p := P { x: 1, y: 2 }; p.z + 1",
            "TE024",
            "has no field 'z'",
        ),
        ("let p := P { x: 1, y: 2 }; p.x = 3; 0", "TE004", ""),
        (
            "if 1 == P { x: 1, y: 2 } { 1 } else { 2 }",
            "SE002",
            "wrap it in parentheses",
        ),
        (
            "let P { x, y: Q { z } } := P { x: 1, y: 2 }; 0",
            "SE002",
            "nested destructuring",
        ),
    ] {
        f.write(
            "src/app.mb",
            &format!("{head} fn main() -> i32 {{ {body} }}"),
        );
        let message = err(f.run(&["run"]), code);
        assert!(message.contains(text), "{body}: {message}");
        assert!(message.contains("app.mb:1:"), "{message}");
    }
    for (source, code, text) in [
        (
            "type A { a: A } fn main() -> i32 { 0 }",
            "TE026",
            "recursive struct",
        ),
        (
            "type A = B; type B = A; fn main() -> i32 { 0 }",
            "TE026",
            "alias cycle",
        ),
        (
            "type A { xs: array<A, 2> } fn main() -> i32 { 0 }",
            "TE026",
            "recursive struct",
        ),
        (
            "type E [ A, B ] fn main() -> i32 { let e: E = 1; 0 }",
            "TE002",
            "E",
        ),
    ] {
        f.write("src/app.mb", source);
        let message = err(f.run(&["run"]), code);
        assert!(message.contains(text), "{source}: {message}");
    }
    // Library exports with struct signatures are rejected too.
    f.write(
        "project.toml",
        "[package]\nname='structs'\nentry='app::main'\n[export]\nf='app::f'\n",
    );
    f.write(
        "src/app.mb",
        "pub type P { pub x: i32 } pub fn f(p: P) -> i32 { 0 } fn main() -> i32 { 0 }",
    );
    err(f.run(&["build", "--lib"]), "LE900");
}

#[test]
fn cross_module_extension_accepts_lowercase_string_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='string-spellings'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "use text_ops;\n\
         pub type Point { pub marker: i32 }\n\
         pub interface Echo { fn echo(borrow self, input: string) -> string; }\n\
         fn main() -> i32 { let point := Point { marker: 0 }; let output := (point.echo(\"hello\") of Echo); output.len() as i32 }",
    );
    f.write(
        "src/text_ops.mb",
        "use self::main::{Point, Echo};\n\
         pub extend Point of Echo { fn echo(borrow self, input: string) -> string { input } }",
    );
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert!(String::from_utf8_lossy(&source.stdout).contains("Result: i32(5)"));
    assert!(f.run(&["build"]).status.success());
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(source.stdout, artifact.stdout);
}

#[test]
fn structs_cross_module_boundaries_by_visibility() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='structs'\nentry='main::main'\n",
    );
    f.write(
        "src/geom.mb",
        "pub type Point { pub x: i32, pub y: i32 }\n\
         pub type Account { pub id: i32, balance: i32 }\n\
         pub type Meters = Point;\n\
         pub fn opening() -> i32 { let a := Account { id: 1, balance: 40 }; a.balance + a.id }\n",
    );
    f.write(
        "src/main.mb",
        "use geom::Point; use geom::Meters; use geom::opening;\n\
         fn main() -> i32 { let p := Point { y: 4, x: 3 }; let m := geom::Point { x: 5, y: 6 }; \
             let q := Meters { x: 7, y: 8 }; p.x * p.y + m.x + q.y + opening() }\n",
    );
    assert!(f.run(&["analyze-project"]).status.success());
    assert!(f.run(&["ownership-project"]).status.success());
    let source = f.run(&["run"]);
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    assert!(String::from_utf8_lossy(&source.stdout).contains("Result: i32(66)"));
    assert!(f.run(&["build"]).status.success());
    let artifact = f.run(&["run", "target/memobits/app.wasm"]);
    assert_eq!(source.stdout, artifact.stdout);

    // A struct with a private field cannot be built from another module, and
    // its private field is not readable there either.
    f.write(
        "src/main.mb",
        "use geom::Account;\n\
         fn main() -> i32 { let a := Account { id: 1, balance: 2 }; a.balance + 0 }\n",
    );
    let message = err(f.run(&["run"]), "TE025");
    assert!(
        message.contains("cannot construct struct 'Account' outside module 'geom'"),
        "{message}"
    );
    assert!(
        message.contains("field 'balance' of struct 'Account' is private to module 'geom'"),
        "{message}"
    );

    // A private type cannot be named from another module, an unknown one is a name error.
    f.write("src/geom.mb", "type Hidden { x: i32 } pub fn f() {}\n");
    f.write(
        "src/main.mb",
        "fn main() -> i32 { let h := geom::Hidden { x: 1 }; 0 }\n",
    );
    err(f.run(&["run"]), "ME007");
    f.write(
        "src/main.mb",
        "fn main() -> i32 { let h := Nope { x: 1 }; 0 }\n",
    );
    err(f.run(&["run"]), "NE003");
}

fn stack_project(f: &Fixture, build: &str, source: &str) {
    f.write(
        "project.toml",
        &format!("[package]\nname='demo'\nentry='app::main'\n{build}"),
    );
    f.write("src/app.mb", source);
}

#[test]
fn build_stack_size_controls_frame_limits() {
    let f = Fixture::new();
    let big = "pub fn main() -> i32 { let a: array<i32, 524288> = [1; 524288]; a[524287] }";
    stack_project(&f, "", big);
    let text = err(f.run(&["run"]), "LE900");
    assert!(
        text.contains("1048576") && text.contains("[build].stack_size"),
        "{text}"
    );
    stack_project(&f, "[build]\nstack_size = 4194304\n", big);
    let out = f.run(&["build"]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let grid = "pub fn main() -> i32 { var g: array<array<i32, 100>, 100> = [[0; 100]; 100]; g[99][99] = 4; g[99][99] }";
    stack_project(&f, "", grid);
    assert!(f.run(&["build"]).status.success());
}

#[test]
fn stack_exhaustion_is_a_distinct_runtime_error() {
    let f = Fixture::new();
    let source = "fn rec(n: i32) -> i32 { let a: array<i32, 1024> = [n; 1024]; \
        if n == 0 { 0 } else { rec(n - 1) + a[1023] } } \
        pub fn main() -> i32 { rec(100000) }";
    stack_project(&f, "[build]\nstack_size = 65536\n", source);
    let text = err(f.run(&["run"]), "RE008");
    assert!(text.contains("stack overflow"), "{text}");
    // A subsequent run of shallower work is unaffected.
    stack_project(
        &f,
        "[build]\nstack_size = 65536\n",
        &source.replace("rec(100000)", "rec(3)"),
    );
    let out = f.run(&["run"]);
    assert!(
        String::from_utf8_lossy(&out.stdout).contains("Result: i32(6)"),
        "{out:?}"
    );
}

#[test]
fn invalid_build_settings_have_stable_codes() {
    let f = Fixture::new();
    for value in ["0", "-16", "100", "4100", "999999999999"] {
        stack_project(
            &f,
            &format!("[build]\nstack_size = {value}\n"),
            "pub fn main() {}",
        );
        err(f.run(&["project"]), "PE007");
    }
    stack_project(&f, "[build]\nstack_size = 'big'\n", "pub fn main() {}");
    err(f.run(&["project"]), "PE002");
    stack_project(&f, "[build]\nstack = 4096\n", "pub fn main() {}");
    err(f.run(&["project"]), "PE002");
}

#[test]
fn run_fuel_options_control_the_execution_budget() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='app::main'\n",
    );
    f.write(
        "src/app.mb",
        "fn main() -> i32 { var i := 0; var s := 0; loop { if i == 100000 { break; } s = s + 1; i += 1; } s }",
    );
    let default = f.run(&["run"]);
    assert!(default.status.success(), "{default:?}");
    assert_eq!(
        String::from_utf8(default.stdout).unwrap(),
        "Result: i32(100000)\n"
    );
    let build = f.run(&["build", "--output", "app.wasm"]);
    assert!(build.status.success(), "{build:?}");
    assert_eq!(
        String::from_utf8(f.run(&["run", "app.wasm"]).stdout).unwrap(),
        "Result: i32(100000)\n"
    );

    for args in [
        &["run", "--fuel", "1000"][..],
        &["run", "app.wasm", "--fuel", "1000"],
    ] {
        let text = err(f.run(args), "RE006");
        assert!(text.contains("--fuel"), "{text}");
    }
    for args in [
        &["run", "--fuel", "100000000"][..],
        &["run", "--no-fuel-limit"],
        &["run", "app.wasm", "--fuel", "100000000"],
        &["run", "app.wasm", "--no-fuel-limit"],
    ] {
        let out = f.run(args);
        assert_eq!(
            String::from_utf8(out.stdout).unwrap(),
            "Result: i32(100000)\n",
            "{args:?}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }

    for args in [
        &["run", "--fuel"][..],
        &["run", "--fuel", "0"],
        &["run", "--fuel", "-5"],
        &["run", "--fuel", "1.5"],
        &["run", "--fuel", "abc"],
        &["run", "--fuel", "1", "--fuel", "2"],
        &["run", "--fuel", "1", "--no-fuel-limit"],
        &["run", "--no-fuel-limit", "--no-fuel-limit"],
        &["run", "app.wasm", "--fuel", "0"],
        &["run", "app.wasm", "--fuel"],
        &["run", "app.wasm", "--no-fuel-limit", "--fuel", "5"],
    ] {
        err(f.run(args), "PE004");
    }
}

#[test]
fn deep_recursion_with_frame_arrays_reports_stack_overflow_not_fuel() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='demo'\nentry='app::main'\n",
    );
    f.write(
        "src/app.mb",
        "fn r(n: i32) -> i32 { let a := [n; 1000]; if n == 0 { 0 } else { r(n - 1) + a[0] } } \
         fn main() -> i32 { r(100000) }",
    );
    let text = err(f.run(&["run"]), "RE008");
    assert!(!text.contains("RE006"), "{text}");
    assert!(text.contains("stack overflow"), "{text}");
}

#[test]
fn list_iteration_runs_from_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='list-iteration'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn bytes(calls: share u32, empty: bool) -> List<u8> {
            calls += 1;
            var items: List<u8> = [];
            if !empty {
                items.push(255);
                items.push(2);
                items.push(3);
                items.push(4);
            }
            items
        }
        fn first(items: borrow List<u32>) -> u32 {
            loop value in items { return value; }
            0
        }
        fn from_temporary(calls: share u32) -> u8 {
            loop value in bytes(calls, false) { return value; }
            0
        }
        fn main() -> bool ! Error {
            var calls: u32 = 0;
            loop value in bytes(calls.share(), true) { return Ok(false); }
            var order: u32 = 0;
            loop value in bytes(calls.share(), false) {
                if value == 255 { order = 1; continue; }
                if value == 4 { return Ok(false); }
                if value == 2 { order = order * 10 + 2; }
                if value == 3 { order = order * 10 + 3; break; }
            }
            var words: List<u32> = [];
            words.push(4_294_967_295);
            var handle := words.share();
            if first(handle.borrow()) != 4_294_967_295 { return Ok(false); }
            loop value in handle {
                if value != 4_294_967_295 { return Ok(false); }
            }
            handle.clear();
            var count: u32 = 0;
            loop value in bytes(calls.share(), false) { count += 1; }
            let first_byte := from_temporary(calls.share());
            Ok(order == 123 && count == 4 && first_byte == 255 && calls == 4)
        }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "list-iteration.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let wasm = f.run(&["run", "list-iteration.wasm"]);
    assert!(wasm.status.success(), "{wasm:?}");
    assert_eq!(wasm.stdout, source.stdout);
}

#[test]
fn explicit_drop_releases_owners_and_allows_reinitialization() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='explicit-drop'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        r#"
        use alloc::List; fn consume(value: List<u32>) { drop(value); }
        fn check(drop_first: bool) -> bool {
            var text := "old".concat("!");
            var bytes: List<u8> = [];
            bytes.push(42);
            if drop_first {
                let loan := text.borrow();
                if loan.len() != 4 { return false; }
                drop(text);
                drop(bytes);
            }
            text = "new".concat("!");
            bytes = [];
            bytes.push(7);
            {
                let scoped := "temp".concat("!");
                drop(scoped);
                text = "kept".concat("!");
            }
            let other := "next".concat("!");
            var words: List<u32> = [];
            words.push(1024);
            consume(words);
            let literal := "static";
            drop(literal);
            text.len() == 5 && other.len() == 5 && bytes.contains(7)
                && match text.byte_at(0) { Some(byte) => byte == 107, None => false }
        }
        fn main() -> bool ! Error { Ok(check(true) && check(false)) }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(bool(true))\n");
    let build = f.run(&["build", "--output", "drop.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "drop.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, source.stdout);
}

#[test]
fn explicit_drop_checks_availability_loans_and_operand_shape() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='explicit-drop'\nentry='main::main'\n",
    );
    for (body, code, message) in [
        (
            "drop(text); text.len();",
            "BE001",
            "unavailable after a move",
        ),
        (
            "drop(words); drop(words);",
            "BE001",
            "unavailable after a move",
        ),
        (
            "if flag { drop(text); } text.len();",
            "BE001",
            "on some paths",
        ),
        (
            "let r := text.borrow(); drop(text); r.len();",
            "BE005",
            "cannot drop",
        ),
        (
            "let r := words.share(); drop(words); r.len();",
            "BE005",
            "cannot drop",
        ),
        (
            "loop word in words { drop(words); }",
            "BE005",
            "cannot drop",
        ),
        ("drop(text.borrow());", "TE017", "whole named owned"),
        ("drop(\"literal\");", "TE017", "whole named owned"),
        ("drop(flag);", "TE017", "whole named owned"),
        ("drop();", "TE010", "expects one argument"),
    ] {
        f.write(
            "src/main.mb",
            &format!(
                "use alloc::List; fn check(flag: bool) {{ let text := \"hi\".concat(\"!\"); var words: List<u32> = []; {body} }} fn main() {{ check(true); }}"
            ),
        );
        let diagnostic = err(f.run(&["build"]), code);
        assert!(diagnostic.contains(message), "{body}: {diagnostic}");
    }
}

#[test]
fn user_drop_function_takes_precedence() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='user-drop'\nentry='main::main'\n",
    );
    f.write(
        "src/main.mb",
        "fn drop(n: u32) -> u32 { n + 1 } fn main() -> u32 ! Error { Ok(drop(41)) }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(u32(42))\n");
}

#[test]
fn user_defined_bitand_assign_mutates_nominal_target_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitand-assign'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::BitAndAssign; type Bits { value: u32 } type Mask { value: u32 } type Wrapper { item: Bits } extend Bits of BitAndAssign { type Rhs = Mask; fn bitand_assign(share self, rhs: Mask) { self.value &= rhs.value; } } fn index(calls: share u32) -> u32 { calls += 1; 0 } fn main() -> u32 { var bits := Bits { value: 15 }; let m1 := Mask { value: 6 }; bits &= m1; var wrapper := Wrapper { item: Bits { value: 11 } }; let m2 := Mask { value: 3 }; wrapper.item &= m2; var calls: u32 = 0; var items := [Bits { value: 13 }]; let m3 := Mask { value: 5 }; items[index(calls.share())] &= m3; if calls == 1 { bits.value + wrapper.item.value + items[0].value } else { 0 } }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(14)\n");
    let build = f.run(&["build", "--output", "bitand-assign.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitand-assign.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(14)\n");

    for (name, source, value) in [
        ("local", "var bits := Bits { value: 4 }; bits &= { return 21; Mask { value: 1 } }; 0", 21),
        ("field", "var wrapper := Wrapper { item: Bits { value: 4 } }; wrapper.item &= { return 22; Mask { value: 1 } }; 0", 22),
        ("index", "var calls: u32 = 0; var items := [Bits { value: 4 }]; items[index(calls.share())] &= { return 23; Mask { value: 1 } }; 0", 23),
    ] {
        let generated = format!("use core::ops::BitAndAssign; type Bits {{ value: u32 }} type Mask {{ value: u32 }} type Wrapper {{ item: Bits }} extend Bits of BitAndAssign {{ type Rhs = Mask; fn bitand_assign(share self, rhs: Mask) {{ self.value &= rhs.value; }} }} fn index(calls: share u32) -> u32 {{ calls += 1; 0 }} fn main() -> u32 {{ {source} }}");
        f.write("src/main.mb", &generated);
        let result = f.run(&["run"]);
        assert!(result.status.success(), "{name}: {result:?}");
        assert_eq!(result.stdout, format!("Result: u32({value})\n").as_bytes());
        let artifact_name = format!("bitand-assign-{name}.wasm");
        let build = f.run(&["build", "--output", &artifact_name]);
        assert!(build.status.success(), "{name}: {build:?}");
        let artifact = f.run(&["run", &artifact_name]);
        assert!(artifact.status.success(), "{name}: {artifact:?}");
        assert_eq!(artifact.stdout, format!("Result: i32({value})\n").as_bytes());
    }

    f.write("src/main.mb", "use core::ops::BitAndAssign; type Bits { value: u32 } type Mask { value: u32 } extend Bits of BitAndAssign { type Rhs = Mask; fn bitand_assign(share self, rhs: Mask) { self.value &= rhs.value; } } fn read(bits: borrow Bits) -> Mask { Mask { value: bits.value } } fn main() -> u32 { var bits := Bits { value: 3 }; bits &= read(bits.borrow()); bits.value }");
    // The owner loan survives the RHS, but checked element-address formation is
    // delayed until the RHS completes, so an early return skips bounds checking.
    f.write("src/main.mb", "use core::ops::BitAndAssign; type Bits { value: u32 } type Mask { value: u32 } extend Bits of BitAndAssign { type Rhs = Mask; fn bitand_assign(share self, rhs: Mask) { self.value &= rhs.value; } } fn main() -> u32 { var items := [Bits { value: 1 }]; var index: u32 = 0; index += 1; items[index] &= { return 24; Mask { value: 1 } }; 0 }");
    let out_of_bounds = f.run(&["run"]);
    assert!(out_of_bounds.status.success(), "{out_of_bounds:?}");
    assert_eq!(out_of_bounds.stdout, b"Result: u32(24)\n");
    let oob_build = f.run(&["build", "--output", "bitand-assign-oob.wasm"]);
    assert!(oob_build.status.success(), "{oob_build:?}");
    let oob_artifact = f.run(&["run", "bitand-assign-oob.wasm"]);
    assert!(oob_artifact.status.success(), "{oob_artifact:?}");
    assert_eq!(oob_artifact.stdout, b"Result: i32(24)\n");

    for (interface, method, operator) in [
        ("AddAssign", "add_assign", "+="),
        ("SubAssign", "sub_assign", "-="),
        ("MulAssign", "mul_assign", "*="),
        ("DivAssign", "div_assign", "/="),
        ("RemAssign", "rem_assign", "%="),
    ] {
        let source_text = format!("use core::ops::{interface}; type Counter {{ value: u32 }} extend Counter of {interface} {{ type Rhs = u32; fn {method}(share self, rhs: u32) {{ self.value += rhs; }} }} fn main() -> u32 {{ var items := [Counter {{ value: 1 }}]; var index: u32 = 0; index += 1; items[index] {operator} {{ return 25; 0 }}; 0 }}");
        f.write("src/main.mb", &source_text);
        let source = f.run(&["run"]);
        assert!(source.status.success(), "{interface}: {source:?}");
        assert_eq!(source.stdout, b"Result: u32(25)\n");
        let artifact_name = format!("{interface}-oob.wasm");
        let build = f.run(&["build", "--output", &artifact_name]);
        assert!(build.status.success(), "{interface}: {build:?}");
        let artifact = f.run(&["run", &artifact_name]);
        assert!(artifact.status.success(), "{interface}: {artifact:?}");
        assert_eq!(artifact.stdout, b"Result: i32(25)\n");
    }

    f.write("src/main.mb", "use core::ops::BitAndAssign; type Bits { value: u32 } type Mask { value: u32 } extend Bits of BitAndAssign { type Rhs = Mask; fn bitand_assign(share self, rhs: Mask) { self.value &= rhs.value; } } fn read(bits: borrow Bits) -> Mask { Mask { value: bits.value } } fn main() -> u32 { var bits := Bits { value: 3 }; bits &= read(bits.borrow()); bits.value }");
    let alias = f.run(&["ownership-project"]);
    assert!(!alias.status.success(), "{alias:?}");
    assert!(
        String::from_utf8_lossy(&alias.stderr).contains("while it is shared"),
        "{alias:?}"
    );

    f.write("src/main.mb", "use core::ops::BitAndAssign; type Bits { value: u32 } extend Bits of BitAndAssign { type Rhs = u32; fn bitand_assign(share self, rhs: u32) { self.value &= rhs; } } fn rhs(item: share Bits) -> u32 { item.value = 5; 7 } fn main() -> u32 { var items := [Bits { value: 15 }, Bits { value: 9 }]; items[0] &= rhs(items[1].share()); items[0].value + items[1].value }");
    let disjoint = f.run(&["run"]);
    assert!(disjoint.status.success(), "{disjoint:?}");
    assert_eq!(disjoint.stdout, b"Result: u32(12)\n");
    let disjoint_build = f.run(&["build", "--output", "bitand-assign-disjoint.wasm"]);
    assert!(disjoint_build.status.success(), "{disjoint_build:?}");
    let disjoint_artifact = f.run(&["run", "bitand-assign-disjoint.wasm"]);
    assert!(disjoint_artifact.status.success(), "{disjoint_artifact:?}");
    assert_eq!(disjoint_artifact.stdout, b"Result: i32(12)\n");

    f.write("src/main.mb", "use core::ops::BitAndAssign; type Bits { value: u32 } type Mask { value: u32 } fn main() -> u32 { var bits := Bits { value: 3 }; bits &= Mask { value: 1 }; bits.value }");
    let missing = f.run(&["analyze-project"]);
    assert!(!missing.status.success(), "{missing:?}");
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("no visible BitAndAssign implementation"),
        "{missing:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::BitAndAssign; pub type Bits { value: u32 } fn main() -> u32 { var bits := Bits { value: 3 }; bits &= 1; bits.value }");
    f.write("src/other.mb", "use self::main::Bits; pub fn marker() {} pub extend Bits of core::ops::BitAndAssign { type Rhs = u32; fn bitand_assign(share self, rhs: u32) { self.value &= rhs; } }");
    let inactive = f.run(&["analyze-project"]);
    assert!(!inactive.status.success(), "{inactive:?}");
    assert!(
        String::from_utf8_lossy(&inactive.stderr)
            .contains("no visible BitAndAssign implementation"),
        "{inactive:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::BitAndAssign; pub type Bits { value: u32 } fn main() -> u32 { var bits := Bits { value: 3 }; bits &= 1; bits.value }");
    f.write("src/other.mb", "use self::main::Bits; pub fn marker() {} extend Bits of core::ops::BitAndAssign { type Rhs = u32; fn bitand_assign(share self, rhs: u32) { self.value &= rhs; } }");
    let private = f.run(&["analyze-project"]);
    assert!(!private.status.success(), "{private:?}");

    f.write("src/main.mb", "use core::ops::BitAndAssign; type Bits { value: u32 } extend Bits of BitAndAssign { type Rhs = u32; fn bitand_assign(share self, rhs: u32) { self.value &= rhs; } } fn main() -> u32 { var bits := Bits { value: 3 }; bits &= true; bits.value }");
    let malformed = f.run(&["analyze-project"]);
    assert!(!malformed.status.success(), "{malformed:?}");

    f.write("src/main.mb", "use core::ops::BitAndAssign; fn mask<T>(initial: T, rhs: T::Rhs) where T: BitAndAssign { var value := initial; value &= rhs; } fn main() -> u32 { 0 }");
    let generic = f.run(&["analyze-project"]);
    assert!(
        !generic.status.success(),
        "generic constrained BitAndAssign remains gated: {generic:?}"
    );

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var bits: u32 = 15; bits &= 6; bits }",
    );
    let primitive = f.run(&["run"]);
    assert!(primitive.status.success(), "{primitive:?}");
    assert_eq!(primitive.stdout, b"Result: u32(6)\n");
    let primitive_build = f.run(&["build", "--output", "primitive-bitand-assign.wasm"]);
    assert!(primitive_build.status.success(), "{primitive_build:?}");
    let primitive_artifact = f.run(&["run", "primitive-bitand-assign.wasm"]);
    assert!(
        primitive_artifact.status.success(),
        "{primitive_artifact:?}"
    );
    assert_eq!(primitive_artifact.stdout, b"Result: i32(6)\n");
}

#[test]
fn user_defined_bitor_assign_mutates_nominal_target_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitor-assign'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::BitOrAssign; type Flags { value: u32 } type Mask { value: u32 } type Boxed { item: Flags } extend Flags of BitOrAssign { type Rhs = Mask; fn bitor_assign(share self, rhs: Mask) { self.value |= rhs.value; } } fn index(calls: share u32) -> u32 { calls += 1; 0 } fn main() -> u32 { var flags := Flags { value: 8 }; let m1 := Mask { value: 3 }; flags |= m1; var boxed := Boxed { item: Flags { value: 4 } }; let m2 := Mask { value: 1 }; boxed.item |= m2; var calls: u32 = 0; var items := [Flags { value: 16 }]; let m3 := Mask { value: 2 }; items[index(calls.share())] |= m3; if calls == 1 { flags.value + boxed.item.value + items[0].value } else { 0 } }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(34)\n");
    let build = f.run(&["build", "--output", "bitor-assign.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitor-assign.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(34)\n");

    f.write("src/main.mb", "use core::ops::BitOrAssign; type Flags { value: u32 } type Mask { value: u32 } extend Flags of BitOrAssign { type Rhs = Mask; fn bitor_assign(share self, rhs: Mask) { self.value |= rhs.value; } } fn main() -> u32 { var items := [Flags { value: 1 }]; var index: u32 = 0; index += 1; items[index] |= { return 29; Mask { value: 1 } }; 0 }");
    let early = f.run(&["run"]);
    assert!(early.status.success(), "{early:?}");
    assert_eq!(early.stdout, b"Result: u32(29)\n");
    let build = f.run(&["build", "--output", "bitor-assign-early.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitor-assign-early.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(29)\n");

    f.write("src/main.mb", "use core::ops::BitOrAssign; type Flags { value: u32 } type Mask { value: u32 } extend Flags of BitOrAssign { type Rhs = Mask; fn bitor_assign(share self, rhs: Mask) { self.value |= rhs.value; } } fn read(flags: borrow Flags) -> Mask { Mask { value: flags.value } } fn main() -> u32 { var flags := Flags { value: 1 }; flags |= read(flags.borrow()); flags.value }");
    let alias = f.run(&["ownership-project"]);
    assert!(!alias.status.success(), "{alias:?}");
    assert!(
        String::from_utf8_lossy(&alias.stderr).contains("while it is shared"),
        "{alias:?}"
    );

    f.write("src/main.mb", "use core::ops::BitOrAssign; type Flags { value: u32 } extend Flags of BitOrAssign { type Rhs = u32; fn bitor_assign(share self, rhs: u32) { self.value |= rhs; } } fn change(other: share Flags) -> u32 { other.value = 4; 2 } fn main() -> u32 { var items := [Flags { value: 1 }, Flags { value: 8 }]; items[0] |= change(items[1].share()); items[0].value + items[1].value }");
    let disjoint = f.run(&["run"]);
    assert!(disjoint.status.success(), "{disjoint:?}");
    assert_eq!(disjoint.stdout, b"Result: u32(7)\n");
    let build = f.run(&["build", "--output", "bitor-assign-disjoint.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitor-assign-disjoint.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(7)\n");

    f.write("src/main.mb", "use core::ops::BitOrAssign; type Flags { value: u32 } type Mask { value: u32 } extend Flags of BitOrAssign { type Rhs = Mask; fn bitor_assign(share self, rhs: Mask) { self.value |= rhs.value; } } fn main() -> u32 { var items := [Flags { value: 1 }]; var index: u32 = 0; index += 1; items[index] |= { index = 0; Mask { value: 1 } }; 0 }");
    let out_of_bounds = f.run(&["run"]);
    assert!(!out_of_bounds.status.success(), "{out_of_bounds:?}");
    assert!(
        String::from_utf8_lossy(&out_of_bounds.stderr).contains("RE007"),
        "{out_of_bounds:?}"
    );
    let build = f.run(&["build", "--output", "bitor-assign-oob.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitor-assign-oob.wasm"]);
    assert!(!artifact.status.success(), "{artifact:?}");
    assert!(
        String::from_utf8_lossy(&artifact.stderr).contains("RE007"),
        "{artifact:?}"
    );

    f.write("src/main.mb", "use core::ops::BitOrAssign; type Flags { value: u32 } type Mask { value: u32 } fn main() -> u32 { var flags := Flags { value: 1 }; flags |= Mask { value: 2 }; flags.value }");
    let missing = f.run(&["analyze-project"]);
    assert!(!missing.status.success(), "{missing:?}");
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("no visible BitOrAssign implementation"),
        "{missing:?}"
    );

    f.write("src/main.mb", "use core::ops::BitOrAssign; type Flags { value: u32 } extend Flags of BitOrAssign { type Rhs = u32; fn bitor_assign(share self, rhs: u32) { self.value |= rhs; } } fn main() -> u32 { var flags := Flags { value: 1 }; flags |= true; flags.value }");
    let wrong_rhs = f.run(&["analyze-project"]);
    assert!(!wrong_rhs.status.success(), "{wrong_rhs:?}");

    f.write("src/main.mb", "use core::ops::BitOrAssign; fn update<T>(target: T, rhs: T::Rhs) where T: BitOrAssign { var value := target; value |= rhs; } fn main() -> u32 { 0 }");
    let generic = f.run(&["analyze-project"]);
    assert!(
        !generic.status.success(),
        "generic constrained BitOrAssign remains gated: {generic:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::BitOrAssign; pub type Flags { pub value: u32 } fn main() -> u32 { var flags := Flags { value: 1 }; flags |= 2; flags.value }");
    f.write("src/other.mb", "use self::main::Flags; pub fn marker() {} pub extend Flags of core::ops::BitOrAssign { type Rhs = u32; fn bitor_assign(share self, rhs: u32) { self.value |= rhs; } }");
    let inactive = f.run(&["analyze-project"]);
    assert!(!inactive.status.success(), "{inactive:?}");
    assert!(
        String::from_utf8_lossy(&inactive.stderr).contains("no visible BitOrAssign implementation"),
        "{inactive:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::BitOrAssign; pub type Flags { pub value: u32 } fn main() -> u32 { var flags := Flags { value: 1 }; flags |= 2; flags.value }");
    f.write("src/other.mb", "use self::main::Flags; pub fn marker() {} extend Flags of core::ops::BitOrAssign { type Rhs = u32; fn bitor_assign(share self, rhs: u32) { self.value |= rhs; } }");
    let private = f.run(&["analyze-project"]);
    assert!(!private.status.success(), "{private:?}");
    assert!(
        String::from_utf8_lossy(&private.stderr).contains("BitOrAssign"),
        "{private:?}"
    );

    f.write("src/main.mb", "use core::ops::BitOrAssign; type Flags { value: u32 } extend Flags of BitOrAssign { type Rhs = u32; fn bitor_assign(share self, rhs: u32) { self.value |= rhs; } } extend Flags of BitOrAssign { type Rhs = u32; fn bitor_assign(share self, rhs: u32) { self.value |= rhs; } } fn main() -> u32 { var flags := Flags { value: 1 }; flags |= 2; flags.value }");
    let ambiguous = f.run(&["analyze-project"]);
    assert!(!ambiguous.status.success(), "{ambiguous:?}");
    assert!(
        String::from_utf8_lossy(&ambiguous.stderr).contains("ambiguous"),
        "{ambiguous:?}"
    );

    f.write("src/main.mb", "use core::ops::BitOrAssign; type Flags { value: u32 } extend Flags of BitOrAssign { type Rhs = u32; fn bitor_assign(borrow self, rhs: u32) { self.value |= rhs; } } fn main() -> u32 { var flags := Flags { value: 1 }; flags |= 2; flags.value }");
    let malformed = f.run(&["analyze-project"]);
    assert!(!malformed.status.success(), "{malformed:?}");

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var bits: u32 = 8; bits |= 3; bits }",
    );
    let primitive = f.run(&["run"]);
    assert!(primitive.status.success(), "{primitive:?}");
    assert_eq!(primitive.stdout, b"Result: u32(11)\n");
    let build = f.run(&["build", "--output", "primitive-bitor-assign.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "primitive-bitor-assign.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(11)\n");
}
#[test]
fn user_defined_bitxor_assign_mutates_nominal_target_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bitxor-assign'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::BitXorAssign; type Flags { value: u32 } type Mask { value: u32 } type Boxed { item: Flags } extend Flags of BitXorAssign { type Rhs = Mask; fn bitxor_assign(share self, rhs: Mask) { self.value ^= rhs.value; } } fn index(calls: share u32) -> u32 { calls += 1; 0 } fn main() -> u32 { var flags := Flags { value: 10 }; let m1 := Mask { value: 3 }; flags ^= m1; var boxed := Boxed { item: Flags { value: 4 } }; let m2 := Mask { value: 1 }; boxed.item ^= m2; var calls: u32 = 0; var items := [Flags { value: 16 }]; let m3 := Mask { value: 2 }; items[index(calls.share())] ^= m3; if calls == 1 { flags.value + boxed.item.value + items[0].value } else { 0 } }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(32)\n");
    let build = f.run(&["build", "--output", "bitxor-assign.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitxor-assign.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(32)\n");

    f.write("src/main.mb", "use core::ops::BitXorAssign; type Flags { value: u32 } type Mask { value: u32 } extend Flags of BitXorAssign { type Rhs = Mask; fn bitxor_assign(share self, rhs: Mask) { self.value ^= rhs.value; } } fn main() -> u32 { var items := [Flags { value: 1 }]; var index: u32 = 0; index += 1; items[index] ^= { return 29; Mask { value: 1 } }; 0 }");
    let early = f.run(&["run"]);
    assert!(early.status.success(), "{early:?}");
    assert_eq!(early.stdout, b"Result: u32(29)\n");
    let build = f.run(&["build", "--output", "bitxor-assign-early.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitxor-assign-early.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(29)\n");

    f.write("src/main.mb", "use core::ops::BitXorAssign; type Flags { value: u32 } type Mask { value: u32 } extend Flags of BitXorAssign { type Rhs = Mask; fn bitxor_assign(share self, rhs: Mask) { self.value ^= rhs.value; } } fn read(flags: borrow Flags) -> Mask { Mask { value: flags.value } } fn main() -> u32 { var flags := Flags { value: 1 }; flags ^= read(flags.borrow()); flags.value }");
    let alias = f.run(&["ownership-project"]);
    assert!(!alias.status.success(), "{alias:?}");
    assert!(
        String::from_utf8_lossy(&alias.stderr).contains("while it is shared"),
        "{alias:?}"
    );

    f.write("src/main.mb", "use core::ops::BitXorAssign; type Flags { value: u32 } extend Flags of BitXorAssign { type Rhs = u32; fn bitxor_assign(share self, rhs: u32) { self.value ^= rhs; } } fn change(other: share Flags) -> u32 { other.value = 4; 2 } fn main() -> u32 { var items := [Flags { value: 1 }, Flags { value: 8 }]; items[0] ^= change(items[1].share()); items[0].value + items[1].value }");
    let disjoint = f.run(&["run"]);
    assert!(disjoint.status.success(), "{disjoint:?}");
    assert_eq!(disjoint.stdout, b"Result: u32(7)\n");
    let build = f.run(&["build", "--output", "bitxor-assign-disjoint.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitxor-assign-disjoint.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(7)\n");

    f.write("src/main.mb", "use core::ops::BitXorAssign; type Flags { value: u32 } type Mask { value: u32 } extend Flags of BitXorAssign { type Rhs = Mask; fn bitxor_assign(share self, rhs: Mask) { self.value ^= rhs.value; } } fn main() -> u32 { var items := [Flags { value: 1 }]; var index: u32 = 0; index += 1; items[index] ^= { index = 0; Mask { value: 1 } }; 0 }");
    let out_of_bounds = f.run(&["run"]);
    assert!(!out_of_bounds.status.success(), "{out_of_bounds:?}");
    assert!(
        String::from_utf8_lossy(&out_of_bounds.stderr).contains("RE007"),
        "{out_of_bounds:?}"
    );
    let build = f.run(&["build", "--output", "bitxor-assign-oob.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "bitxor-assign-oob.wasm"]);
    assert!(!artifact.status.success(), "{artifact:?}");
    assert!(
        String::from_utf8_lossy(&artifact.stderr).contains("RE007"),
        "{artifact:?}"
    );

    f.write("src/main.mb", "use core::ops::BitXorAssign; type Flags { value: u32 } type Mask { value: u32 } fn main() -> u32 { var flags := Flags { value: 1 }; flags ^= Mask { value: 2 }; flags.value }");
    let missing = f.run(&["analyze-project"]);
    assert!(!missing.status.success(), "{missing:?}");
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("no visible BitXorAssign implementation"),
        "{missing:?}"
    );

    f.write("src/main.mb", "use core::ops::BitXorAssign; type Flags { value: u32 } extend Flags of BitXorAssign { type Rhs = u32; fn bitxor_assign(share self, rhs: u32) { self.value ^= rhs; } } fn main() -> u32 { var flags := Flags { value: 1 }; flags ^= true; flags.value }");
    let wrong_rhs = f.run(&["analyze-project"]);
    assert!(!wrong_rhs.status.success(), "{wrong_rhs:?}");

    f.write("src/main.mb", "use core::ops::BitXorAssign; fn update<T>(target: T, rhs: T::Rhs) where T: BitXorAssign { var value := target; value ^= rhs; } fn main() -> u32 { 0 }");
    let generic = f.run(&["analyze-project"]);
    assert!(
        !generic.status.success(),
        "generic constrained BitXorAssign remains gated: {generic:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::BitXorAssign; pub type Flags { pub value: u32 } fn main() -> u32 { var flags := Flags { value: 1 }; flags ^= 2; flags.value }");
    f.write("src/other.mb", "use self::main::Flags; pub fn marker() {} pub extend Flags of core::ops::BitXorAssign { type Rhs = u32; fn bitxor_assign(share self, rhs: u32) { self.value ^= rhs; } }");
    let inactive = f.run(&["analyze-project"]);
    assert!(!inactive.status.success(), "{inactive:?}");
    assert!(
        String::from_utf8_lossy(&inactive.stderr)
            .contains("no visible BitXorAssign implementation"),
        "{inactive:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::BitXorAssign; pub type Flags { pub value: u32 } fn main() -> u32 { var flags := Flags { value: 1 }; flags ^= 2; flags.value }");
    f.write("src/other.mb", "use self::main::Flags; pub fn marker() {} extend Flags of core::ops::BitXorAssign { type Rhs = u32; fn bitxor_assign(share self, rhs: u32) { self.value ^= rhs; } }");
    let private = f.run(&["analyze-project"]);
    assert!(!private.status.success(), "{private:?}");
    assert!(
        String::from_utf8_lossy(&private.stderr).contains("BitXorAssign"),
        "{private:?}"
    );

    f.write("src/main.mb", "use core::ops::BitXorAssign; type Flags { value: u32 } extend Flags of BitXorAssign { type Rhs = u32; fn bitxor_assign(share self, rhs: u32) { self.value ^= rhs; } } extend Flags of BitXorAssign { type Rhs = u32; fn bitxor_assign(share self, rhs: u32) { self.value ^= rhs; } } fn main() -> u32 { var flags := Flags { value: 1 }; flags ^= 2; flags.value }");
    let ambiguous = f.run(&["analyze-project"]);
    assert!(!ambiguous.status.success(), "{ambiguous:?}");
    assert!(
        String::from_utf8_lossy(&ambiguous.stderr).contains("ambiguous"),
        "{ambiguous:?}"
    );

    f.write("src/main.mb", "use core::ops::BitXorAssign; type Flags { value: u32 } extend Flags of BitXorAssign { type Rhs = u32; fn bitxor_assign(borrow self, rhs: u32) { self.value ^= rhs; } } fn main() -> u32 { var flags := Flags { value: 1 }; flags ^= 2; flags.value }");
    let malformed = f.run(&["analyze-project"]);
    assert!(!malformed.status.success(), "{malformed:?}");

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var bits: u32 = 10; bits ^= 3; bits }",
    );
    let primitive = f.run(&["run"]);
    assert!(primitive.status.success(), "{primitive:?}");
    assert_eq!(primitive.stdout, b"Result: u32(9)\n");
    let build = f.run(&["build", "--output", "primitive-bitxor-assign.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "primitive-bitxor-assign.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(9)\n");
}
#[test]
fn user_defined_shl_assign_mutates_nominal_target_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='shl-assign'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::ShlAssign; type Flags { value: u32 } type Mask { value: u32 } type Boxed { item: Flags } extend Flags of ShlAssign { type Rhs = Mask; fn shl_assign(share self, rhs: Mask) { self.value <<= rhs.value; } } fn index(calls: share u32) -> u32 { calls += 1; 0 } fn main() -> u32 { var flags := Flags { value: 10 }; let m1 := Mask { value: 3 }; flags <<= m1; var boxed := Boxed { item: Flags { value: 4 } }; let m2 := Mask { value: 1 }; boxed.item <<= m2; var calls: u32 = 0; var items := [Flags { value: 16 }]; let m3 := Mask { value: 2 }; items[index(calls.share())] <<= m3; if calls == 1 { flags.value + boxed.item.value + items[0].value } else { 0 } }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(152)\n");
    let build = f.run(&["build", "--output", "shl-assign.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shl-assign.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(152)\n");

    f.write("src/main.mb", "use core::ops::ShlAssign; type Flags { value: u32 } type Mask { value: u32 } extend Flags of ShlAssign { type Rhs = Mask; fn shl_assign(share self, rhs: Mask) { self.value <<= rhs.value; } } fn main() -> u32 { var items := [Flags { value: 1 }]; var index: u32 = 0; index += 1; items[index] <<= { return 29; Mask { value: 1 } }; 0 }");
    let early = f.run(&["run"]);
    assert!(early.status.success(), "{early:?}");
    assert_eq!(early.stdout, b"Result: u32(29)\n");
    let build = f.run(&["build", "--output", "shl-assign-early.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shl-assign-early.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(29)\n");

    f.write("src/main.mb", "use core::ops::ShlAssign; type Flags { value: u32 } type Mask { value: u32 } extend Flags of ShlAssign { type Rhs = Mask; fn shl_assign(share self, rhs: Mask) { self.value <<= rhs.value; } } fn read(flags: borrow Flags) -> Mask { Mask { value: flags.value } } fn main() -> u32 { var flags := Flags { value: 1 }; flags <<= read(flags.borrow()); flags.value }");
    let alias = f.run(&["ownership-project"]);
    assert!(!alias.status.success(), "{alias:?}");
    assert!(
        String::from_utf8_lossy(&alias.stderr).contains("while it is shared"),
        "{alias:?}"
    );

    f.write("src/main.mb", "use core::ops::ShlAssign; type Flags { value: u32 } extend Flags of ShlAssign { type Rhs = u32; fn shl_assign(share self, rhs: u32) { self.value <<= rhs; } } fn change(other: share Flags) -> u32 { other.value = 4; 2 } fn main() -> u32 { var items := [Flags { value: 1 }, Flags { value: 8 }]; items[0] <<= change(items[1].share()); items[0].value + items[1].value }");
    let disjoint = f.run(&["run"]);
    assert!(disjoint.status.success(), "{disjoint:?}");
    assert_eq!(disjoint.stdout, b"Result: u32(8)\n");
    let build = f.run(&["build", "--output", "shl-assign-disjoint.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shl-assign-disjoint.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(8)\n");

    f.write("src/main.mb", "use core::ops::ShlAssign; type Flags { value: u32 } type Mask { value: u32 } extend Flags of ShlAssign { type Rhs = Mask; fn shl_assign(share self, rhs: Mask) { self.value <<= rhs.value; } } fn main() -> u32 { var items := [Flags { value: 1 }]; var index: u32 = 0; index += 1; items[index] <<= { index = 0; Mask { value: 1 } }; 0 }");
    let out_of_bounds = f.run(&["run"]);
    assert!(!out_of_bounds.status.success(), "{out_of_bounds:?}");
    assert!(
        String::from_utf8_lossy(&out_of_bounds.stderr).contains("RE007"),
        "{out_of_bounds:?}"
    );
    let build = f.run(&["build", "--output", "shl-assign-oob.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shl-assign-oob.wasm"]);
    assert!(!artifact.status.success(), "{artifact:?}");
    assert!(
        String::from_utf8_lossy(&artifact.stderr).contains("RE007"),
        "{artifact:?}"
    );

    f.write("src/main.mb", "use core::ops::ShlAssign; type Flags { value: u32 } type Mask { value: u32 } fn main() -> u32 { var flags := Flags { value: 1 }; flags <<= Mask { value: 2 }; flags.value }");
    let missing = f.run(&["analyze-project"]);
    assert!(!missing.status.success(), "{missing:?}");
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("no visible ShlAssign implementation"),
        "{missing:?}"
    );

    f.write("src/main.mb", "use core::ops::ShlAssign; type Flags { value: u32 } extend Flags of ShlAssign { type Rhs = u32; fn shl_assign(share self, rhs: u32) { self.value <<= rhs; } } fn main() -> u32 { var flags := Flags { value: 1 }; flags <<= true; flags.value }");
    let wrong_rhs = f.run(&["analyze-project"]);
    assert!(!wrong_rhs.status.success(), "{wrong_rhs:?}");

    f.write("src/main.mb", "use core::ops::ShlAssign; fn update<T>(target: T, rhs: T::Rhs) where T: ShlAssign { var value := target; value <<= rhs; } fn main() -> u32 { 0 }");
    let generic = f.run(&["analyze-project"]);
    assert!(
        !generic.status.success(),
        "generic constrained ShlAssign remains gated: {generic:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::ShlAssign; pub type Flags { pub value: u32 } fn main() -> u32 { var flags := Flags { value: 1 }; flags <<= 2; flags.value }");
    f.write("src/other.mb", "use self::main::Flags; pub fn marker() {} pub extend Flags of core::ops::ShlAssign { type Rhs = u32; fn shl_assign(share self, rhs: u32) { self.value <<= rhs; } }");
    let inactive = f.run(&["analyze-project"]);
    assert!(!inactive.status.success(), "{inactive:?}");
    assert!(
        String::from_utf8_lossy(&inactive.stderr).contains("no visible ShlAssign implementation"),
        "{inactive:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::ShlAssign; pub type Flags { pub value: u32 } fn main() -> u32 { var flags := Flags { value: 1 }; flags <<= 2; flags.value }");
    f.write("src/other.mb", "use self::main::Flags; pub fn marker() {} extend Flags of core::ops::ShlAssign { type Rhs = u32; fn shl_assign(share self, rhs: u32) { self.value <<= rhs; } }");
    let private = f.run(&["analyze-project"]);
    assert!(!private.status.success(), "{private:?}");
    assert!(
        String::from_utf8_lossy(&private.stderr).contains("ShlAssign"),
        "{private:?}"
    );

    f.write("src/main.mb", "use core::ops::ShlAssign; type Flags { value: u32 } extend Flags of ShlAssign { type Rhs = u32; fn shl_assign(share self, rhs: u32) { self.value <<= rhs; } } extend Flags of ShlAssign { type Rhs = u32; fn shl_assign(share self, rhs: u32) { self.value <<= rhs; } } fn main() -> u32 { var flags := Flags { value: 1 }; flags <<= 2; flags.value }");
    let ambiguous = f.run(&["analyze-project"]);
    assert!(!ambiguous.status.success(), "{ambiguous:?}");
    assert!(
        String::from_utf8_lossy(&ambiguous.stderr).contains("ambiguous"),
        "{ambiguous:?}"
    );

    f.write("src/main.mb", "use core::ops::ShlAssign; type Flags { value: u32 } extend Flags of ShlAssign { type Rhs = u32; fn shl_assign(borrow self, rhs: u32) { self.value <<= rhs; } } fn main() -> u32 { var flags := Flags { value: 1 }; flags <<= 2; flags.value }");
    let malformed = f.run(&["analyze-project"]);
    assert!(!malformed.status.success(), "{malformed:?}");

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var bits: u32 = 10; bits <<= 3; bits }",
    );
    let primitive = f.run(&["run"]);
    assert!(primitive.status.success(), "{primitive:?}");
    assert_eq!(primitive.stdout, b"Result: u32(80)\n");
    let build = f.run(&["build", "--output", "primitive-shl-assign.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "primitive-shl-assign.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(80)\n");

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var bits: u32 = 1; bits <<= 0; bits <<= 31; bits }",
    );
    let boundaries = f.run(&["run"]);
    assert!(boundaries.status.success(), "{boundaries:?}");
    assert_eq!(boundaries.stdout, b"Result: u32(2147483648)\n");
    let build = f.run(&["build", "--output", "primitive-shl-assign-boundaries.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "primitive-shl-assign-boundaries.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(-2147483648)\n");

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var bits: u32 = 1; bits <<= 32; bits }",
    );
    let static_count = f.run(&["analyze-project"]);
    assert!(!static_count.status.success(), "{static_count:?}");
    assert!(
        String::from_utf8_lossy(&static_count.stderr).contains("LE003"),
        "{static_count:?}"
    );

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var bits: u32 = 1; bits <<= 16 + 16; bits }",
    );
    let static_expression = f.run(&["analyze-project"]);
    assert!(!static_expression.status.success(), "{static_expression:?}");
    assert!(
        String::from_utf8_lossy(&static_expression.stderr).contains("LE003"),
        "{static_expression:?}"
    );

    f.write(
        "src/main.mb",
        "fn count() -> u32 { 32 } fn main() -> u32 { var bits: u32 = 1; bits <<= count(); bits }",
    );
    let dynamic_count = f.run(&["run"]);
    assert!(!dynamic_count.status.success(), "{dynamic_count:?}");
    assert!(
        String::from_utf8_lossy(&dynamic_count.stderr).contains("RE007"),
        "{dynamic_count:?}"
    );
    let build = f.run(&["build", "--output", "primitive-shl-assign-dynamic.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "primitive-shl-assign-dynamic.wasm"]);
    assert!(!artifact.status.success(), "{artifact:?}");
    assert!(
        String::from_utf8_lossy(&artifact.stderr).contains("RE007"),
        "{artifact:?}"
    );

    f.write("src/main.mb", "use core::ops::ShlAssign; type Bits { value: u32 } type Count { value: u32 } extend Bits of ShlAssign { type Rhs = Count; fn shl_assign(share self, rhs: Count) { self.value += 1; } } fn main() -> u32 { var bits := Bits { value: 1 }; let count := Count { value: 32 }; bits <<= count; bits.value }");
    let custom_rhs = f.run(&["run"]);
    assert!(custom_rhs.status.success(), "{custom_rhs:?}");
    assert_eq!(custom_rhs.stdout, b"Result: u32(2)\n");
}

#[test]
fn user_defined_shr_assign_mutates_nominal_target_in_source_and_wasm() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='shr-assign'\nentry='main::main'\n",
    );
    f.write("src/main.mb", "use core::ops::ShrAssign; type Flags { value: u32 } type Mask { value: u32 } type Boxed { item: Flags } extend Flags of ShrAssign { type Rhs = Mask; fn shr_assign(share self, rhs: Mask) { self.value >>= rhs.value; } } fn index(calls: share u32) -> u32 { calls += 1; 0 } fn main() -> u32 { var flags := Flags { value: 10 }; let m1 := Mask { value: 3 }; flags >>= m1; var boxed := Boxed { item: Flags { value: 4 } }; let m2 := Mask { value: 1 }; boxed.item >>= m2; var calls: u32 = 0; var items := [Flags { value: 16 }]; let m3 := Mask { value: 2 }; items[index(calls.share())] >>= m3; if calls == 1 { flags.value + boxed.item.value + items[0].value } else { 0 } }");
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: u32(7)\n");
    let build = f.run(&["build", "--output", "shr-assign.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shr-assign.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(7)\n");

    f.write("src/main.mb", "use core::ops::ShrAssign; type Flags { value: u32 } type Mask { value: u32 } extend Flags of ShrAssign { type Rhs = Mask; fn shr_assign(share self, rhs: Mask) { self.value >>= rhs.value; } } fn main() -> u32 { var items := [Flags { value: 1 }]; var index: u32 = 0; index += 1; items[index] >>= { return 29; Mask { value: 1 } }; 0 }");
    let early = f.run(&["run"]);
    assert!(early.status.success(), "{early:?}");
    assert_eq!(early.stdout, b"Result: u32(29)\n");
    let build = f.run(&["build", "--output", "shr-assign-early.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shr-assign-early.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(29)\n");

    f.write("src/main.mb", "use core::ops::ShrAssign; type Flags { value: u32 } type Mask { value: u32 } extend Flags of ShrAssign { type Rhs = Mask; fn shr_assign(share self, rhs: Mask) { self.value >>= rhs.value; } } fn read(flags: borrow Flags) -> Mask { Mask { value: flags.value } } fn main() -> u32 { var flags := Flags { value: 1 }; flags >>= read(flags.borrow()); flags.value }");
    let alias = f.run(&["ownership-project"]);
    assert!(!alias.status.success(), "{alias:?}");
    assert!(
        String::from_utf8_lossy(&alias.stderr).contains("while it is shared"),
        "{alias:?}"
    );

    f.write("src/main.mb", "use core::ops::ShrAssign; type Flags { value: u32 } extend Flags of ShrAssign { type Rhs = u32; fn shr_assign(share self, rhs: u32) { self.value >>= rhs; } } fn change(other: share Flags) -> u32 { other.value = 4; 2 } fn main() -> u32 { var items := [Flags { value: 1 }, Flags { value: 8 }]; items[0] >>= change(items[1].share()); items[0].value + items[1].value }");
    let disjoint = f.run(&["run"]);
    assert!(disjoint.status.success(), "{disjoint:?}");
    assert_eq!(disjoint.stdout, b"Result: u32(4)\n");
    let build = f.run(&["build", "--output", "shr-assign-disjoint.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shr-assign-disjoint.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(4)\n");

    f.write("src/main.mb", "use core::ops::ShrAssign; type Flags { value: u32 } type Mask { value: u32 } extend Flags of ShrAssign { type Rhs = Mask; fn shr_assign(share self, rhs: Mask) { self.value >>= rhs.value; } } fn main() -> u32 { var items := [Flags { value: 1 }]; var index: u32 = 0; index += 1; items[index] >>= { index = 0; Mask { value: 1 } }; 0 }");
    let out_of_bounds = f.run(&["run"]);
    assert!(!out_of_bounds.status.success(), "{out_of_bounds:?}");
    assert!(
        String::from_utf8_lossy(&out_of_bounds.stderr).contains("RE007"),
        "{out_of_bounds:?}"
    );
    let build = f.run(&["build", "--output", "shr-assign-oob.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shr-assign-oob.wasm"]);
    assert!(!artifact.status.success(), "{artifact:?}");
    assert!(
        String::from_utf8_lossy(&artifact.stderr).contains("RE007"),
        "{artifact:?}"
    );

    f.write("src/main.mb", "use core::ops::ShrAssign; type Flags { value: u32 } type Mask { value: u32 } fn main() -> u32 { var flags := Flags { value: 1 }; flags >>= Mask { value: 2 }; flags.value }");
    let missing = f.run(&["analyze-project"]);
    assert!(!missing.status.success(), "{missing:?}");
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("no visible ShrAssign implementation"),
        "{missing:?}"
    );

    f.write("src/main.mb", "use core::ops::ShrAssign; type Flags { value: u32 } extend Flags of ShrAssign { type Rhs = u32; fn shr_assign(share self, rhs: u32) { self.value >>= rhs; } } fn main() -> u32 { var flags := Flags { value: 1 }; flags >>= true; flags.value }");
    let wrong_rhs = f.run(&["analyze-project"]);
    assert!(!wrong_rhs.status.success(), "{wrong_rhs:?}");

    f.write("src/main.mb", "use core::ops::ShrAssign; type Flags { value: u32 } extend Flags of ShrAssign { type Rhs = u32; fn shr_assign(share self, rhs: u32) { self.value >>= rhs; } } fn update<T>(target: T, rhs: T::Rhs) -> T where T: ShrAssign { var value := target; value >>= rhs; value } fn main() -> u32 { let result := update(Flags { value: 64 }, 3); result.value }");
    let generic = f.run(&["run"]);
    assert!(generic.status.success(), "{generic:?}");
    assert_eq!(generic.stdout, b"Result: u32(8)\n");
    let build = f.run(&["build", "--output", "shr-assign-generic.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "shr-assign-generic.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(8)\n");

    f.write("src/main.mb", "use core::ops::ShrAssign; type Plain { value: u32 } fn update<T>(target: T, rhs: T::Rhs) -> T where T: ShrAssign { var value := target; value >>= rhs; value } fn main() -> u32 { let result := update(Plain { value: 64 }, 3); result.value }");
    let missing_evidence = f.run(&["analyze-project"]);
    assert!(!missing_evidence.status.success(), "{missing_evidence:?}");
    assert!(
        String::from_utf8_lossy(&missing_evidence.stderr)
            .contains("no visible implementation of 'core::ops::ShrAssign'"),
        "{missing_evidence:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::ShrAssign; pub type Flags { pub value: u32 } fn main() -> u32 { var flags := Flags { value: 1 }; flags >>= 2; flags.value }");
    f.write("src/other.mb", "use self::main::Flags; pub fn marker() {} pub extend Flags of core::ops::ShrAssign { type Rhs = u32; fn shr_assign(share self, rhs: u32) { self.value >>= rhs; } }");
    let inactive = f.run(&["analyze-project"]);
    assert!(!inactive.status.success(), "{inactive:?}");
    assert!(
        String::from_utf8_lossy(&inactive.stderr).contains("no visible ShrAssign implementation"),
        "{inactive:?}"
    );

    f.write("src/main.mb", "use other::marker; use core::ops::ShrAssign; pub type Flags { pub value: u32 } fn main() -> u32 { var flags := Flags { value: 1 }; flags >>= 2; flags.value }");
    f.write("src/other.mb", "use self::main::Flags; pub fn marker() {} extend Flags of core::ops::ShrAssign { type Rhs = u32; fn shr_assign(share self, rhs: u32) { self.value >>= rhs; } }");
    let private = f.run(&["analyze-project"]);
    assert!(!private.status.success(), "{private:?}");
    assert!(
        String::from_utf8_lossy(&private.stderr).contains("ShrAssign"),
        "{private:?}"
    );

    f.write("src/main.mb", "use core::ops::ShrAssign; type Flags { value: u32 } extend Flags of ShrAssign { type Rhs = u32; fn shr_assign(share self, rhs: u32) { self.value >>= rhs; } } extend Flags of ShrAssign { type Rhs = u32; fn shr_assign(share self, rhs: u32) { self.value >>= rhs; } } fn main() -> u32 { var flags := Flags { value: 1 }; flags >>= 2; flags.value }");
    let ambiguous = f.run(&["analyze-project"]);
    assert!(!ambiguous.status.success(), "{ambiguous:?}");
    assert!(
        String::from_utf8_lossy(&ambiguous.stderr).contains("ambiguous"),
        "{ambiguous:?}"
    );

    f.write("src/main.mb", "use core::ops::ShrAssign; type Flags { value: u32 } extend Flags of ShrAssign { type Rhs = u32; fn shr_assign(borrow self, rhs: u32) { self.value >>= rhs; } } fn main() -> u32 { var flags := Flags { value: 1 }; flags >>= 2; flags.value }");
    let malformed = f.run(&["analyze-project"]);
    assert!(!malformed.status.success(), "{malformed:?}");

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var bits: u32 = 10; bits >>= 3; bits }",
    );
    let primitive = f.run(&["run"]);
    assert!(primitive.status.success(), "{primitive:?}");
    assert_eq!(primitive.stdout, b"Result: u32(1)\n");
    let build = f.run(&["build", "--output", "primitive-shr-assign.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "primitive-shr-assign.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(1)\n");

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var bits: u32 = 1; bits >>= 0; bits >>= 31; bits }",
    );
    let boundaries = f.run(&["run"]);
    assert!(boundaries.status.success(), "{boundaries:?}");
    assert_eq!(boundaries.stdout, b"Result: u32(0)\n");
    let build = f.run(&["build", "--output", "primitive-shr-assign-boundaries.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "primitive-shr-assign-boundaries.wasm"]);
    assert!(artifact.status.success(), "{artifact:?}");
    assert_eq!(artifact.stdout, b"Result: i32(0)\n");

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var bits: u32 = 1; bits >>= 32; bits }",
    );
    let static_count = f.run(&["analyze-project"]);
    assert!(!static_count.status.success(), "{static_count:?}");
    assert!(
        String::from_utf8_lossy(&static_count.stderr).contains("LE003"),
        "{static_count:?}"
    );

    f.write(
        "src/main.mb",
        "fn main() -> u32 { var bits: u32 = 1; bits >>= 16 + 16; bits }",
    );
    let static_expression = f.run(&["analyze-project"]);
    assert!(!static_expression.status.success(), "{static_expression:?}");
    assert!(
        String::from_utf8_lossy(&static_expression.stderr).contains("LE003"),
        "{static_expression:?}"
    );

    f.write(
        "src/main.mb",
        "fn count() -> u32 { 32 } fn main() -> u32 { var bits: u32 = 1; bits >>= count(); bits }",
    );
    let dynamic_count = f.run(&["run"]);
    assert!(!dynamic_count.status.success(), "{dynamic_count:?}");
    assert!(
        String::from_utf8_lossy(&dynamic_count.stderr).contains("RE007"),
        "{dynamic_count:?}"
    );
    let build = f.run(&["build", "--output", "primitive-shr-assign-dynamic.wasm"]);
    assert!(build.status.success(), "{build:?}");
    let artifact = f.run(&["run", "primitive-shr-assign-dynamic.wasm"]);
    assert!(!artifact.status.success(), "{artifact:?}");
    assert!(
        String::from_utf8_lossy(&artifact.stderr).contains("RE007"),
        "{artifact:?}"
    );

    f.write("src/main.mb", "use core::ops::ShrAssign; type Bits { value: u32 } type Count { value: u32 } extend Bits of ShrAssign { type Rhs = Count; fn shr_assign(share self, rhs: Count) { self.value += 1; } } fn main() -> u32 { var bits := Bits { value: 1 }; let count := Count { value: 32 }; bits >>= count; bits.value }");
    let custom_rhs = f.run(&["run"]);
    assert!(custom_rhs.status.success(), "{custom_rhs:?}");
    assert_eq!(custom_rhs.stdout, b"Result: u32(2)\n");
}
