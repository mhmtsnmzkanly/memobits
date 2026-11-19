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
        fn byte_is(s: borrow String, offset: u32, expected: u8) -> Bool {
            match s.byte_at(offset) { Some(byte) => byte == expected, None => false }
        }
        fn doubled(input: borrow String, descend: Bool) -> Bool {
            let joined := input.concat(input);
            if descend && !doubled(joined.borrow(), false) { return false; }
            // The callee's released region can be reused while joined is live.
            let joined_again := joined.concat("");
            joined.len() == input.len() * 2
                && byte_is(joined.borrow(), input.len(), 195)
                && byte_is(joined_again.borrow(), joined_again.len() - 1, 169)
        }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
                "fn returns(s: String) -> String {{ s }}
                 fn earlier(s: String, size: u32) {{}}
                 fn alias(view: borrow String, s: String) {{ view.len(); }}
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
        fn append(text: share String, suffix: borrow String) {
            text.push_str(suffix)
        }
        fn early(text: share String, stop: Bool) {
            text.push_str({ if stop { return; } "wrong" });
        }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        fn extend(text: share String, early: Bool) {
            text = text.concat({ if early { return; } "😀" });
        }
        fn read_exclusive(text: share String) -> u32 { text.len() }
        fn clear(text: share String) { text = "ok"; }
        fn into_len(text: String) -> u32 { text.len() }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
            "fn forward(text: share String) { replace(text.share()); }"
        } else {
            ""
        };
        f.write(
            "text.mb",
            &format!(
                r#"
            fn replace(text: share String) {{ text = text.concat("!"); }}
            {forwarding}
            fn two(left: share String, right: share String) {{ left.len(); right.len(); }}
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
        fn use_owner(value: String) -> u32 { value.len() }
        fn add(value: borrow String) -> String {
            let result := value.concat("😀");
            result
        }
        fn check(move_first: Bool) -> Bool {
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
        fn use_owner_before_exit(value: borrow String) -> u32 { value.len() }
        fn main() -> Result<Bool, Error> { Ok(check(true) && check(false) && early() == 3) }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        fn select(first: String, order: i32, second: String, last: i32) -> String {
            if first.len() == 3 && order == 1 && last == 2 { return second; }
            first
        }
        fn main() -> Result<u32, Error> {
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
        pub fn choose(early: Bool) -> String {
            let joined := "é".concat("😀");
            if early { return joined; }
            "ok"
        }
        fn identity(owned: String) -> String { owned }
        pub fn forward(early: Bool) -> String {
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
        fn byte_is(s: borrow String, index: u32, expected: u8) -> Bool {
            match s.byte_at(index) { Some(byte) => byte == expected, None => false }
        }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        fn make(text: String, early: Bool) -> String {
            if early { return text; }
            let result := text.concat("!");
            result
        }
        fn early_concat() -> Bool {
            let first := "é".concat("!");
            first.concat({ return first.len() == 3; "unreachable" });
            false
        }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        fn make(text: String, divisor: i32) -> String {
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
        fn make() -> String {
            let text := "é".concat("😀");
            text
        }
        fn byte_is(value: Option<u8>, expected: u8) -> Bool {
            match value { Some(byte) => byte == expected, None => false }
        }
        fn scalar_is(value: Option<u32>, expected: u32) -> Bool {
            match value { Some(scalar) => scalar == expected, None => false }
        }
        fn early() -> Bool {
            make().byte_at({ return true; 0 });
            false
        }
        fn order() -> Bool {
            var step := 0;
            let result := "é".concat({ step = 1; "😀" }).scalar_at({
                if step != 1 { return false; }
                step = 2;
                2
            });
            scalar_is(result, 128_512) && step == 2
        }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        fn make() -> String {
            let result := "a".concat("😀");
            result
        }
        fn inspect(first: borrow String, second: borrow String, order: i32) -> Bool {
            first.len() == 3 && second.len() == 5 && order == 2
        }
        fn early() -> Bool {
            let unused := "unused";
            inspect(make().borrow(), { return true; unused.borrow() }, 0)
        }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
                r#"fn make() -> String {{ let result := "é".concat("!"); result }}
                   fn inspect(value: borrow String) {{ value.len(); }}
                   fn mutate(value: share String) {{ value.len(); }}
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
        fn make(ordered: Bool) -> String {
            let text := "a".concat("😀");
            if ordered { return text; }
            "wrong order"
        }
        fn select(first: String, view: borrow String, second: String, last: i32) -> String {
            if first.len() == 3 && view.len() == 2 && last == 2 { return second; }
            first
        }
        fn early() -> Bool {
            select(make(true), "v".concat("w").borrow(), "a".concat("b"), {
                return true;
                0
            });
            false
        }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
                r#"fn make() -> String {{ let result := "é".concat("!"); result }}
               fn take(value: String) {{ value.len(); }}
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
        pub fn consume(early: Bool, value: String) -> u32 {
            if early { return value.len(); }
            let moved := value;
            moved.len()
        }
        pub fn forward(early: Bool, value: String) -> u32 {
            consume(early, value)
        }
    "#,
    );
    f.write(
        "src/main.mb",
        r#"
        use self::text::forward;
        fn literal_echo(value: String, extra: u32) -> String { value }
        fn main() -> Result<u32, Error> {
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
        fn first_is(value: borrow String, expected: u8) -> Bool {
            match value.byte_at(0) { Some(byte) => byte == expected, None => false }
        }
        fn check(move_inward: Bool) -> Bool {
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
        fn main() -> Result<Bool, Error> {
            Ok(check(true) && check(false) && check(true))
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        r#"fn main(flag: Bool) -> u32 {
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
        fn choose(outer: String, early: Bool) -> String {
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
        fn main() -> Result<u32, Error> {
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
        fn rebuild(old: borrow List<u32>) -> List<u32> {
            var result: List<u32> = [];
            result.push(0);
            let previous := match old.get(0) { Some(value) => value, None => 0 };
            result.push(previous + old.len());
            result
        }
        fn consume(items: List<u32>) -> u32 { items.len() }
        fn pass(items: List<u32>) -> List<u32> { items }
        fn check(move_old: Bool) -> Bool {
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
        fn early() -> Bool {
            var items: List<u8> = [];
            items.push(255);
            items = { return items.len() == 1; [] };
            false
        }
        fn main() -> Result<Bool, Error> { Ok(check(false) && check(true) && early()) }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
            &format!("fn main() {{ var items: List<u8> = []; {body} }}"),
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
        fn bytes(empty: Bool) -> List<u8> {
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
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        fn make_bytes(log: share List<u8>, empty: Bool) -> List<u8> {
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
        fn check_early_exit() -> Bool {
            let staged := make_words();
            var log: List<u8> = [];
            forward(staged, { return log.len() == 0; log.share() });
            false
        }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        type Rows { flags: Array<Bool, 2> }
        fn make(log: share List<u8>) -> List<u32> {
            log.push(1);
            var words: List<u32> = [];
            words.push(4_294_967_295);
            words
        }
        fn reads(bytes: borrow Bytes<2>, words: share List<u32>) -> Bool {
            bytes.contains(bytes[1]) && words.contains(4_294_967_295)
        }
        fn main() -> Result<Bool, Error> {
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
            let bytes: Bytes<2> = [0, 255];
            var words := make(log.share());
            let borrowed := reads(bytes.borrow(), words.share());
            words.clear();
            let rows := Rows { flags: [false, true] };
            let nested: Array<Array<i8, 2>, 1> = [[-2, 3]];
            let no_values: Array<i32, 0> = [];
            let wide: Array<u64, 1> = [4_294_967_296];
            let floats: Array<f32, 2> = [0.0, 1.0];
            let zero: f32 = 0.0;
            let nan := zero / zero;
            let doubles: Array<f64, 1> = [0.0];
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        type Flags { values: Array<Bool, 2> }

        fn at(result: Option<u32>, expected: u32) -> Bool {
            match result { Some(index) => index == expected, None => false }
        }
        fn missing(result: Option<u32>) -> Bool {
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
        fn reads(bytes: borrow Bytes<3>, words: share List<u32>) -> Bool {
            at(bytes.index_of(bytes[2]), 0) && at(words.index_of(4_294_967_295), 1)
        }
        fn main() -> Result<Bool, Error> {
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
            let bytes: Bytes<3> = [255, 0, 255];
            var words := make(log.share());
            let borrowed := reads(bytes.borrow(), words.share());
            let flags := Flags { values: [false, true] };
            let rows: Array<Array<i8, 2>, 1> = [[-2, 3]];
            let empty_array: Array<i32, 0> = [];
            let wide: Array<u64, 2> = [0, 4_294_967_296];
            let floats: Array<f32, 2> = [1.0, 0.0];
            let zero: f32 = 0.0;
            let nan := zero / zero;
            let doubles: Array<f64, 1> = [0.0];
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        ("let a: Bytes<1> = [1]; a.contains(true);", "TE002"),
        ("let a: Bytes<1> = [1]; a.contains();", "TE010"),
        ("let a: Bytes<1> = [1]; a.contains(1, 2);", "TE010"),
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
        fn bytes(log: share List<u8>) -> List<u8> {
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
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        fn bytes(log: share List<u8>) -> List<u8> {
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
        fn inspect(first: borrow List<u8>, second: borrow List<u32>, order: u32) -> Bool {
            let byte_ok := match first.get(0) { Some(value) => value == 255, None => false };
            let word_ok := match second.get(0) { Some(value) => value == 1002, None => false };
            byte_ok && word_ok && order == 3
        }
        fn early() -> Bool {
            var log: List<u8> = [];
            inspect(bytes(log.share()).borrow(), words(log.share()).borrow(), {
                return log.len() == 2;
            })
        }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
                r#"fn make() -> List<u8> {{ let items: List<u8> = []; items }}
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
            "fn make() -> List<u8> {{ let items: List<u8> = []; items }} fn main() {{ {body} }}"
        ),
        );
        let diagnostic = err(f.run(&["ownership", "list.mb"]), code);
        assert!(diagnostic.contains(message), "{body}: {diagnostic}");
    }
    f.write("list.mb", "fn make() -> List<u8> { let items: List<u8> = []; items } fn forward() -> List<u8> { make() }");
    err(f.run(&["ownership", "list.mb"]), "TE018");

    f.write(
        "project.toml",
        "[package]\nname='list-return-abi'\nentry='main::main'\n[export]\nmake='main::make'\n",
    );
    f.write(
        "src/main.mb",
        "pub fn make() -> List<u8> { let items: List<u8> = []; items } fn main() {}",
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
        fn finish(words: List<u32>) -> Bool {
            match words.get(1) { Some(word) => word == 100, None => false }
        }
        fn take(bytes: List<u8>, proceed: Bool, var words: List<u32>) -> Bool {
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
        fn run_temporary(skip: Bool) -> Bool {
            var log: List<u8> = [];
            let check := take(make_bytes(log.share()), {
                if skip { return log.len() == 1; }
                if log.len() != 1 { return false; }
                log.push(2);
                true
            }, make_words(log.borrow()));
            check && log.len() == 2
        }
        fn run(skip: Bool) -> Bool {
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
        fn main() -> Result<Bool, Error> { Ok(run(false) && run(true) && run_temporary(false) && run_temporary(true)) }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
            &format!("fn make() -> List<u8> {{ let items: List<u8> = []; items }} fn make_words() -> List<u32> {{ let items: List<u32> = []; items }} fn take(items: List<u8>, later: u32) {{}} fn main() {{ let items: List<u8> = []; {body} }}"),
        );
        err(f.run(&["ownership", "list.mb"]), code);
    }
    f.write(
        "project.toml",
        "[package]\nname='owned-list-abi'\nentry='main::main'\n[export]\ntake='main::take'\n",
    );
    f.write(
        "src/main.mb",
        "pub fn take(items: List<u8>) { items.len(); } fn main() {}",
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
        fn add(bytes: share List<u8>, words: share List<u32>) {
            bytes.push(255);
            let held := words.borrow();
            let value := held.len() + 1000;
            words.push(value);
        }
        fn last(words: share List<u32>) -> Option<u32> {
            words.get(words.len() - 1)
        }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        fn fresh(previous: borrow List<u32>) -> List<u32> {
            var result: List<u32> = [];
            result.push(0);
            let old := match previous.get(0) { Some(value) => value, None => 0 };
            result.push(old + 1);
            result
        }
        fn rebuild(items: share List<u32>, early: Bool) {
            items = { if early { return; } fresh(items.borrow()) };
        }
        fn install(items: share List<u8>, replacement: List<u8>) { items = replacement; }
        fn clear(items: share List<u8>) { items = []; }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        fn reset(words: share List<u32>) { words.clear() }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
            &format!("fn main() {{ var items: List<u8> = []; {body} }}"),
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
        fn take(items: share List<u32>) -> Option<u32> { items.pop() }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
            &format!("fn main() {{ var items: List<u8> = []; {body} }}"),
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
        fn rebuild(previous: borrow List<u32>) -> List<u32> {
            var next: List<u32> = [];
            next.push(0);
            let old := match previous.get(0) { Some(value) => value, None => 0 };
            next.push(old + 1);
            next
        }
        fn check(early: Bool) -> Bool {
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
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
            r#"fn add(view: share List<u8>) { view.push(1); }
             fn main() { var items: List<u8> = []; let view := items.borrow();
                         add(items.share()); view.len(); }"#,
            "BE005",
        ),
        (
            r#"fn both(left: share List<u8>, right: share List<u8>) {
                  left.push(1); right.push(2);
             }
             fn main() { var items: List<u8> = []; both(items.share(), items.share()); }"#,
            "BE005",
        ),
        (
            r#"fn add(view: share List<u8>) {
                  let held := view.borrow(); view.push(1); held.len();
             }
             fn main() {}"#,
            "BE005",
        ),
        (
            r#"fn reset(view: share List<u8>) {
                  let held := view.borrow(); view = []; held.len();
               } fn main() {}"#,
            "BE005",
        ),
        (
            r#"fn main() { var items: List<u8> = []; var handle := items.share();
                         let held := handle.borrow(); handle = []; held.len(); }"#,
            "BE005",
        ),
        (
            r#"fn reset(view: share List<u8>) { let alias := view; alias = []; } fn main() {}"#,
            "TE004",
        ),
        (
            r#"fn main() { var items: List<u8> = []; var alias := items.share();
                         let held := alias.borrow(); alias.push(1); held.len(); }"#,
            "BE005",
        ),
        (
            r#"fn main() { var items: List<u8> = []; var alias := items.borrow(); alias.push(1); }"#,
            "TE017",
        ),
        (
            r#"fn main() { var items: List<u8> = []; let alias := items.share(); alias.push(1); }"#,
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
        "pub fn add(items: share List<u8>) { items.push(1); } fn main() {}",
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
        fn word_at(items: borrow List<u32>, index: u32) -> Option<u32> {
            if index < items.len() { return items.get(index); }
            None
        }
        fn byte_at(items: borrow List<u8>, index: u32) -> Option<u8> {
            if index < items.len() { return items.get(index); }
            None
        }
        fn word_is(value: Option<u32>, expected: u32) -> Bool {
            match value { Some(word) => word == expected, None => false }
        }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        ("let held := items.borrow(); items.push(1); held.len();", "BE005", "while it is borrowed"),
        ("let held := items.borrow(); held.get({ items.push(1); 0 });", "BE005", "while it is borrowed"),
        ("let held := items.borrow(); let moved := items; held.get(0);", "BE005", "while it is borrowed"),
        ("inspect(items);", "TE017", "explicit .borrow()"),
        ("let indirect := inspect; indirect(items.borrow());", "TE017", "direct internal call"),
        ("let fixed: List<u8> = []; fixed.share();", "TE017", "requires a mutable local owner"),
        ("let view: Option<borrow List<u8>> = Some(items.borrow());", "TE017", "cannot be stored in Option"),
        ("let dangling := { var inner: List<u8> = []; inner.push(5); inner.borrow() }; dangling.len();", "TE017", "reference-valued block results"),
    ] {
        f.write("list.mb", &format!(
            "fn inspect(view: borrow List<u8>) {{ view.len(); }} fn main() {{ var items: List<u8> = []; {body} }}"
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
        "pub fn inspect(view: borrow List<u8>) -> u32 { view.len() } fn main() {}",
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
        fn byte_is(value: Option<u8>, expected: u8) -> Bool {
            match value { Some(byte) => byte == expected, None => false }
        }
        fn word_is(value: Option<u32>, expected: u32) -> Bool {
            match value { Some(word) => word == expected, None => false }
        }
        fn no_word(value: Option<u32>) -> Bool {
            match value { Some(_) => false, None => true }
        }
        fn no_byte(value: Option<u8>) -> Bool {
            match value { Some(_) => false, None => true }
        }
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
            &format!("fn main() {{ let items: List<u32> = []; {body} }}"),
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
        fn check(move_it: Bool) -> Bool {
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
        fn main() -> Result<Bool, Error> { Ok(check(false) && check(true)) }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        type List { count: u32 }
        type Words = List<u32>;
        fn main() -> Result<Bool, Error> {
            let existing: List = List { count: 7 };
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
            "fn main() { let items: List<u8> = []; let moved := items; items.len(); }",
            "BE001",
        ),
        ("fn main() { let items: List<i32> = []; }", "TE017"),
        ("fn main() { let items: List<u8> = [1]; }", "TE017"),
        (
            "fn main() { let items: List<u8> = []; let array := [items]; }",
            "TE017",
        ),
        (
            "fn main() { let items: List<u8> = []; items.share(); }",
            "TE017",
        ),
        ("fn main() -> List<u32> { [] }", "TE018"),
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
        r#"pub type Text = String;
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
           fn main() -> Result<i32, Error> {
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
        fn literal() -> String { "😀" }
        fn make(use_literal: Bool, fail: Bool) -> Result<String, TextError> {
            if fail { return Err(TextError { code: 7, offset: 2 }); }
            if use_literal { return Ok("é"); }
            let text := literal();
            Ok(text)
        }
        fn inspect(result: Result<String, TextError>) -> u32 {
            match result {
                Ok(text) => match text.scalar_at(0) { Some(value) => value, None => 0 },
                Err(error) => {
                    let TextError { code, offset } := error;
                    if offset == 2 { code } else { 0 }
                }
            }
        }
        fn main() -> Result<Bool, Error> {
            let first := make(true, false);
            Ok(inspect(first) == 233 && inspect(make(false, false)) == 128_512
                && inspect(make(false, true)) == 7)
        }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        fn into_len(value: String) -> u32 { value.len() }
        fn check(early: Bool) -> Bool {
            let text := "é".concat("😀");
            let result: Result<String, Error> = Ok(text);
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
        fn main() -> Result<Bool, Error> { Ok(check(false) && check(true)) }
    "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        fn make(mode: i32, text: String) -> Result<String, Error> {
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
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
            "fn forward() -> Result<String, Error> { make() }"
        } else {
            ""
        };
        f.write("text.mb", &format!(r#"
            fn make() -> Result<String, Error> {{
                let text := "é".concat("!");
                return Ok(text);
            }}
            fn take(result: Result<String, Error>) {{}}
            {forward}
            fn main() {{ {body} }}
        "#));
        let diagnostic = err(f.run(&["ownership", "text.mb"]), "TE018");
        assert!(diagnostic.contains("requires an immediate consuming match"), "{body}: {diagnostic}");
    }
}

#[test]
fn heap_string_results_reject_escape_and_ignore_paths() {
    let f = Fixture::new();
    for body in [
        r#"let text := "é".concat("!"); let result: Result<String, Error> = Ok(text); match result { Ok(_) => {}, Err(_) => {} };"#,
        r#"let text := "é".concat("!"); let result: Result<String, Error> = Ok(text); match result { Err(_) => {}, _ => {} };"#,
        r#"let text := "é".concat("!"); let result: Result<String, Error> = Ok(text); 1 + 1; match result { Ok(text) => { text.len(); }, Err(_) => {} };"#,
        r#"let text := "é".concat("!"); let result: Result<String, Error> = Ok(text);"#,
        r#"let result := wrap("é".concat("!"));"#,
        r#"let result: Result<String, Error> = Ok(heap());"#,
        r#"var text := "é"; append(text.share()); let result: Result<String, Error> = Ok(text);"#,
    ] {
        f.write(
            "text.mb",
            &format!(
                r#"
            fn wrap(text: String) -> Result<String, Error> {{ Ok(text) }}
            fn heap() -> String {{ let text := "é".concat("!"); text }}
            fn append(text: share String) {{ text.push_str("!"); }}
            fn main() {{ {body} }}
        "#
            ),
        );
        let diagnostic = err(f.run(&["ownership", "text.mb"]), "TE018");
        assert!(
            diagnostic.contains("heap String") || diagnostic.contains("heap Result<String, E>"),
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
            let result: Result<String, Error> = Ok("é");
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
            r#"pub fn main() -> String { "é" }"#,
            &["build"][..],
            "exported signatures cannot use String",
        ),
        (
            "pub fn main(s: borrow String) {}",
            &["build", "--lib"][..],
            "exported signatures cannot use String",
        ),
        (
            r#"fn main() { let values := ["é"]; }"#,
            &["build"][..],
            "String array elements",
        ),
        (
            "type Box { text: String } fn main() {}",
            &["build"][..],
            "String fields or enum payloads",
        ),
        (
            r#"pub fn main() -> Result<String, Error> { Ok("é") }"#,
            &["build"][..],
            "primitive success payload",
        ),
        (
            r#"pub fn main() -> Result<String, Error> { Ok("é") }"#,
            &["build", "--lib"][..],
            "exported signatures cannot return enums",
        ),
        (
            r#"pub fn main() -> Result<String, Error> { let text := "é".concat("!"); Ok(text) }"#,
            &["build"][..],
            "primitive success payload",
        ),
        (
            r#"pub fn main() -> Result<String, Error> { let text := "é".concat("!"); Ok(text) }"#,
            &["build", "--lib"][..],
            "exported signatures cannot return enums",
        ),
        (
            "type Box { text: Result<String, Error> } fn main() {}",
            &["build"][..],
            "nested Result<String, E> storage",
        ),
        (
            r#"pub fn main() -> Result<String, Utf8Error> { let input: Bytes<1> = [65]; input.to_utf8_string(1) }"#,
            &["build"][..],
            "primitive success payload",
        ),
        (
            r#"fn main() { let result: Result<String, Error> = Ok("é"); let items := [result]; }"#,
            &["build"][..],
            "nested Result<String, E> storage",
        ),
    ] {
        f.write("src/main.mb", source);
        let diagnostic = err(f.run(args), "LE900");
        assert!(diagnostic.contains(message), "{diagnostic}");
        assert!(!f.0.join("target/memobits/app.wasm").exists());
    }
}

#[test]
fn string_ownership_uses_last_borrow_use_and_rejects_moves_and_reads() {
    let f = Fixture::new();
    let helpers = "fn inspect(s: borrow String) {} fn consume(s: String) {}";
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
    assert_example_runs_in_both_modes("astar", b"Result: Ok(i32(12))\n");
}

#[test]
fn enf_lexer_example_checks_byte_fixtures_in_source_and_wasm() {
    assert_example_runs_in_both_modes("enf-lexer", b"Result: Ok(i32(0))\n");
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
        fn convert(input: borrow Bytes<4>, length: i32) -> Result<String, Utf8Error> {
            input.to_utf8_string(length)
        }
        fn byte_is(text: borrow String, offset: u32, expected: u8) -> Bool {
            match text.byte_at(offset) { Some(byte) => byte == expected, None => false }
        }
        fn error_is(input: borrow Bytes<4>, length: i32, code: u32, offset: i32) -> Bool {
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
        fn main() -> Result<Bool, Error> {
            let input: Bytes<4> = [195, 169, 0, 255];
            let result := convert(input.borrow(), 3);
            let exact := match result {
                Ok(text) => text.len() == 3 && byte_is(text.borrow(), 0, 195)
                    && byte_is(text.borrow(), 1, 169) && byte_is(text.borrow(), 2, 0),
                Err(_) => false
            };
            let empty_input: Bytes<2> = [255, 255];
            let empty := match empty_input.to_utf8_string(0) {
                Ok(text) => text.len() == 0, Err(_) => false
            };
            let malformed: Bytes<4> = [65, 237, 160, 128];
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
            &format!("fn main() {{ let input: Bytes<1> = [65]; {body} }}"),
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
            "fn main() { var bytes: Bytes<2> = [1, 2]; bytes.validate_utf8({ bytes[0] = 0; 1 }); }",
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
    assert_example_runs_in_both_modes("utf8-validator", b"Result: Ok(i32(0))\n");
}

#[test]
fn language_guide_checks_bytes_array_equivalence_in_source_and_wasm() {
    assert_example_runs_in_both_modes("language-guide", b"Result: Ok(i32(42))\n");
}

#[test]
fn applied_bytes_coexists_with_a_bare_bytes_import_and_moves_like_an_array() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='bytes'\nentry='main::main'\n",
    );
    f.write("src/model.mb", "pub type Bytes = u8;");
    let source = "use self::model::Bytes;
        fn consume(data: Array<u8, 1>) -> u8 { data[0] }
        fn main() -> u8 {
            let value: Bytes = 42;
            let data: Bytes<1> = [value];
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

    f.write(
        "src/main.mb",
        "type Bytes [ Tag ]
         type Buffer = Bytes<1>;
         fn main() -> u8 { Buffer::Tag; 0 }",
    );
    err(f.run(&["resolve"]), "NE004");
}

fn assert_example_runs_in_both_modes(project: &str, expected: &[u8]) {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/projects")
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
            let empty: Option<i32> = None;
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
    assert!(message.contains("Option<T> annotation"), "{message}");
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
        "pub type Maybe = Option<u32>;
         pub type Failure = Error;
         pub type Read = Result<u32, Failure>;
         pub type Work = Attempt<Read, Failure>;
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
         use model::zero as Skipped;
         fn read(value: Work) -> u32 {
             match value {
                 Work::Done(r) => match r { Ok(n) => n, R::Err(e) => e.code },
                 Work::Skipped => Skipped(),
                 Failed(e) => e.code
             }
         }
         fn main() -> i32 {
             var count: u32 = 0;
             let value := Work::Done(Ok(bump(count.share())));
             let failure: Work = Failed(fail(count.share()));
             let miss := model::Work::Skipped;
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
        (
            "fn main() { let value := Ok(7); }",
            "Result<T, E> annotation",
        ),
        (
            "fn main() { let value: Attempt<i32, u32> = Done(7); }",
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
         pub type Read = Result<u32, ParseError>;
         pub type Work = Attempt<Read, ParseError>;
         pub fn wrap(e: ParseError) -> Work { Done(Err(e)) }",
    );
    f.write(
        "src/main.mb",
        "use model::ParseError;
         use model::Work;
         use model::wrap;
         fn inspect(work: Work) -> u32 {
             match work {
                 Done(read) => match read { Err(e) => e.code + 10 * e.stage + 100 * e.line, Ok(n) => n },
                 Failed(e) => e.code,
                 Skipped => 0
             }
         }
         fn main() -> i32 {
             var err := ParseError { line: 3, code: 1, stage: 2 };
             origin::bump(err.share());
             let n := origin::code(err.borrow());
             let failed: Work = Failed(ParseError { stage: 9, code: 7, line: 8 });
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
            "fn main() -> Result<u64, Error> { Ok(18446744073709551615) }",
            "Ok(u64(18446744073709551615))",
        ),
        (
            "fn main() -> Result<i8, Error> { Ok(-20) }",
            "Ok(i8(-20))",
        ),
        (
            "fn main() -> Result<i32, Error> { Err(Error { code: 4294967295 }) }",
            "Err(Error, code=4294967295)",
        ),
        (
            "fn main() -> Attempt<Bool, Error> { Done(true) }",
            "Done(Bool(true))",
        ),
        (
            "fn main() -> Attempt<f64, Error> { Done(2.5) }",
            "Done(f64(2.5))",
        ),
        (
            "fn main() -> Attempt<i32, Error> { Skipped }",
            "Skipped",
        ),
        (
            "type ParseError: Error {} fn main() -> Attempt<i32, ParseError> { Failed(ParseError { code: 5 }) }",
            "Failed(outcomes::main::ParseError, code=5)",
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
         pub type Failure = Result<i32, Leaf>;
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
         fn consume(text: String, value: i32) -> i32 { value }
         fn main() -> Result<i32, Error> {
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
        "fn dive(n: i32) -> Result<i32, Error> {
             if n == 0 { Ok(1) } else { dive(n - 1) }
         }
         fn main() -> Result<i32, Error> { dive(10000) }",
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
            "fn main() -> Result<Array<i32, 1>, Error> { Ok([7]) }",
            "primitive success payload",
        ),
        (
            "fn main(n: i32) -> Attempt<i32, Error> { Done(n) }",
            "must take no parameters",
        ),
        (
            "type Lookalike [ Ok(i32), Err(Error) ] fn main() -> Lookalike { Lookalike::Ok(7) }",
            "cannot return enums",
        ),
        (
            "fn main() -> Option<i32> { Some(7) }",
            "cannot return enums",
        ),
    ] {
        f.write("src/main.mb", source);
        let message = err(f.run(&["build"]), "LE900");
        assert!(message.contains(expected), "{source}: {message}");
    }
    f.write(
        "src/main.mb",
        "pub fn work() -> Result<i32, Error> { Ok(7) } fn main() {}",
    );
    let message = err(f.run(&["build", "--lib"]), "LE900");
    assert!(message.contains("cannot return enums"), "{message}");
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
        assert!(text.contains("not supported yet"));
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
        &["run", "app.wasm", "--project", "project.toml"],
        &["run", "--project", "project.toml", "--entry", "main"],
    ] {
        err(f.run(args), "PE004");
    }
    assert!(err(f.run(&["check"]), "PE005").contains("unsupported"));
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
    f.write("src/api.mb", "pub fn consume(value: Array<i32, 1>) {}");
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
    f.write("invalid.mb", "fn main() { break; let value: Bool = 1; }");
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

    f.write("types.mb", "fn main() { let x: Bool = 1; }");
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
        "fn main() { let values: Array<i32, 3> = [1, 2, 3]; values[0]; }",
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
        "fn main() -> i32 { let a: Array<i64, 65537> = [0; 65537]; 0 }",
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
        "fn main() { let values: Array<i8, 3> = [1, 2, 3]; let nested := [[1, 2], [3, 4]]; }",
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
        "fn main() { let values: Array<i32, 3> = [1, 2]; }",
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
    let sum = "fn sum(a: borrow Array<i32, 3>) -> i32 { var i := 0; var t := 0; loop { if i >= 3 { break; } t += a[i]; i += 1; } t } ";
    let fill = "fn fill(a: share Array<i32, 4>, v: i32) { var i := 0; loop { if i >= 4 { break; } a[i] = v + i; i += 1; } } ";
    // A borrow parameter called twice on the same array.
    let out = run_both(
        &f,
        &format!("{sum} fn main() -> i32 {{ let a := [1, 2, 3]; sum(a.borrow()) * 10 + sum(a.borrow()) }}"),
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
        "fn f(a: Array<i32, 3>) -> i32 { a[0] + a[2] } fn main() -> i32 { let a := [1, 2, 3]; f(a) + f([10, 20, 30]) }",
    );
    assert!(out.contains("44"), "{out}");
    // Recursion with an array borrow parameter.
    let out = run_both(
        &f,
        "fn rec(a: borrow Array<i32, 3>, n: i32) -> i32 { let m := n + 0; var l := [m + 0, m * 2, m * 3]; if m + 0 == 0 { a[0] + 0 } else { let r := rec(a, m - 1); r + l[2] } } fn main() -> i32 { let a := [100, 2, 3]; rec(a.borrow(), 3) }",
    );
    assert!(out.contains("118"), "{out}");

    // A dynamic out-of-range index inside the callee traps in both runs.
    f.write(
        "src/app.mb",
        "fn get(a: borrow Array<i32, 3>, n: i32) -> i32 { a[n] + 0 } fn main() -> i32 { let a := [1, 2, 3]; let n := 2; get(a.borrow(), n + 1) }",
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
        "fn get(a: borrow Array<i32, 3>) -> i32 { a[3] + 0 } fn main() -> i32 { 0 }",
    );
    err(f.run(&["run"]), "TE008");
    f.write(
        "src/app.mb",
        "fn get(a: borrow Array<i32, 3>) -> i32 { a[0] + 0 } fn main() -> i32 { let a := [1, 2]; get(a.borrow()) }",
    );
    err(f.run(&["run"]), "TE002");
    f.write(
        "src/app.mb",
        "fn own(a: Array<i32, 2>) -> i32 { a[0] + 0 } fn main() -> i32 { let a := [1, 2]; let r := own(a); a[0] + r }",
    );
    err(f.run(&["run"]), "BE001");
    f.write(
        "src/app.mb",
        "fn put(a: borrow Array<i32, 2>) { a[0] = 1; } fn main() -> i32 { 0 }",
    );
    err(f.run(&["run"]), "TE004");
    f.write(
        "src/app.mb",
        "fn two(a: share Array<i32, 2>, b: share Array<i32, 2>) {} fn main() -> i32 { var a := [1, 2]; two(a.share(), a.share()); 0 }",
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
    let sum = "fn sum(a: borrow Array<i32, 3>) -> i32 { var i := 0; var t := 0; loop { if i >= 3 { break; } t += a[i]; i += 1; } t } ";
    // A repetition-built result consumed by a borrow-taking sum and an owned call.
    let out = run_both(
        &f,
        &format!("{sum} fn make(v: i32) -> Array<i32, 3> {{ [v + 0; 3] }} fn own(a: Array<i32, 3>) -> i32 {{ a[0] + a[2] }} fn main() -> i32 {{ let a := make(4); sum(a.borrow()) * 100 + own(make(5)) }}"),
    );
    assert!(out.contains("1210"), "{out}");
    // An if-value chosen dynamically and recursion returning arrays.
    let out = run_both(
        &f,
        "fn pick(c: Bool) -> Array<i32, 2> { if c { [1, 2] } else { [3, 4] } } fn fib(n: i32) -> Array<i32, 2> { if n <= 0 { return [0, 1]; } let p := fib(n - 1); [p[1] + 0, p[0] + p[1]] } fn main() -> i32 { let a := pick(true); let b := pick(false); let c := fib(10); a[1] * 1000 + b[0] * 100 + c[0] }",
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
        &format!("{sum} fn zero(a: share Array<i32, 3>) {{ a[0] = 0; a[1] = 0; a[2] = 0; }} fn main() -> i32 {{ var m := [[1, 2, 3], [4, 5, 6]]; zero(m[0].share()); m[1] = [7, 8, 9]; sum(m[0].borrow()) * 100 + sum(m[1].borrow()) }}"),
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
        ("fn main() -> i32 { let m := [[1, 2], [3, 4]]; let r := m[0]; 0 }", "TE022"),
        ("fn main() -> i32 { let m := [[1, 2], [3, 4]]; m[0][2] + 0 }", "TE008"),
        ("fn main() -> i32 { let m := [[1, 2], [3, 4]]; m[2][0] + 0 }", "TE008"),
        ("fn main() -> i32 { var m := [[1, 2], [3, 4]]; let r := m.borrow(); m[0][0] = 1; r[0][0] + 0 }", "BE005"),
        ("fn make() -> Array<i32, 2> { [1, 2] } fn main() -> i32 { let a := make(); let b := a; a[0] + 0 }", "BE001"),
        ("fn make() -> Array<i32, 2> { [1, 2] } fn main() -> i32 { make()[0] + 0 }", "TE017"),
        ("fn main() -> Array<i32, 2> { [1, 2] }", "LE900"),
        ("fn main() -> i32 { let m: Array<Array<i32, 4000>, 4000> = [[0; 4000]; 4000]; 0 }", "LE900"),
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
        "fn mk(v: i32) -> Array<i32, 3> { [v.copy(), v.copy() + 1, v + 2] } \
         fn swap(a: share Array<i32, 3>, i: i32, j: i32) { let t := a[i].copy(); a[i] = a[j].copy(); a[j] = t; } \
         fn main() -> i32 { var a := mk(1); swap(a.share(), 0, 2); a[0] * 100 + a[1] * 10 + a[2] }",
    );
    assert!(out.contains("321"), "{out}");
    let out = run_both(
        &f,
        "fn pick(flags: borrow Array<Bool, 2>, i: i32) -> Bool { flags[i].copy() } \
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
         fn mk(v: i32) -> Array<i32, 3> { [v, v + 1, v + 2] } \
         fn get(r: borrow i32) -> i32 { r } \
         fn swap(a: share Array<i32, 3>) { let t := a[0]; a[0] = a[2]; a[2] = t; } \
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
        "pub fn total(a: borrow Array<i32, 3>) -> i32 { var i := 0; var t := 0; loop { if i >= 3 { break; } t += a[i]; i += 1; } t }\n\
         pub fn scale(a: share Array<i32, 3>, k: i32) { var i := 0; loop { if i >= 3 { break; } a[i] *= k; i += 1; } }\n\
         pub fn first(a: Array<i32, 3>) -> i32 { a[0] + 0 }\n",
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
    f.write("src/main.mb", "fn main(a: Array<i32, 2>) -> i32 { 0 }\n");
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
        "type M { a: u8, b: i64, c: Bool, d: f32, e: i16 } \
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
        "type Flags { on: Bool, n: i32 } type F = Flags; \
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
            "expected i32, found Bool",
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
            "type A { xs: Array<A, 2> } fn main() -> i32 { 0 }",
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
    let big = "pub fn main() -> i32 { let a: Array<i32, 524288> = [1; 524288]; a[524287] }";
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
    let grid = "pub fn main() -> i32 { var g: Array<Array<i32, 100>, 100> = [[0; 100]; 100]; g[99][99] = 4; g[99][99] }";
    stack_project(&f, "", grid);
    assert!(f.run(&["build"]).status.success());
}

#[test]
fn stack_exhaustion_is_a_distinct_runtime_error() {
    let f = Fixture::new();
    let source = "fn rec(n: i32) -> i32 { let a: Array<i32, 1024> = [n; 1024]; \
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
        fn bytes(calls: share u32, empty: Bool) -> List<u8> {
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
        fn main() -> Result<Bool, Error> {
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
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
        fn consume(value: List<u32>) { drop(value); }
        fn check(drop_first: Bool) -> Bool {
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
        fn main() -> Result<Bool, Error> { Ok(check(true) && check(false)) }
        "#,
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(Bool(true))\n");
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
                "fn check(flag: Bool) {{ let text := \"hi\".concat(\"!\"); var words: List<u32> = []; {body} }} fn main() {{ check(true); }}"
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
        "fn drop(n: u32) -> u32 { n + 1 } fn main() -> Result<u32, Error> { Ok(drop(41)) }",
    );
    let source = f.run(&["run"]);
    assert!(source.status.success(), "{source:?}");
    assert_eq!(source.stdout, b"Result: Ok(u32(42))\n");
}
