# Source formatting (`mb fmt`)

`mb fmt` rewrites Memobits sources to one canonical style. The style is the one
the runnable guide already uses, made precise; the binding decision is in
[decisions.md](decisions.md#source-formatting-2026-11-25-architect-default-stage-5-step-1).
Usage and exit codes are in the [CLI README](../../crates/memobits-cli/README.md#formatting).

## Guarantees

1. **Meaning-preserving.** The formatter only chooses white space between
   tokens. It never rewrites, adds, removes or reorders a token except
   optional trailing commas, the optional comma after a `match` arm, and the
   commas it adds or drops according to the layout rules below (all of which
   the grammar treats as optional). The syntax tree of the output equals the
   syntax tree of the input modulo positions
   ([`same_syntax`](../../crates/memobits-syntax/src/format.rs)).
   Numeric literals keep their written spelling (`0xFF_FF`, `0b1010`,
   `1_000.5e-3`), string and character literals are copied byte for byte
   (including `{name}` placeholders and `{{`/`}}`), and parentheses written by
   the user are kept: `(a + b) + c` and `((a))` stay as written.
2. **Comments are never lost or reordered.** Line, nested block and `///` doc
   comments are all ordinary comments. A comment stays attached to the token it
   was next to (see [Comments](#comments)).
3. **Idempotent.** Formatting formatted source changes nothing.
4. **Self-checking.** `format_source` re-parses its output and verifies the
   syntax tree, the comment sequence and idempotence before returning. A
   failure is an internal error (PE008 in the CLI) and the file is left
   untouched, so `mb fmt` cannot write a result that changes meaning.

## Layout rules

| Aspect | Rule |
| --- | --- |
| Indentation | 4 spaces; tabs never emitted. |
| Width | Lines are at most 100 characters where a break is possible. A line holding a single unbreakable token (a long string) may exceed it. |
| Braces | The opening brace stays on the line of its header. |
| Spacing | One space around binary operators, `=`, `:=`, `=>`, `->`, after `,` `:` `;`; none before `,` `;` `:` or around `.` `::` `..` `..=`; none after a unary operator or inside brackets; `T?` and `T ! E` as in the guide; `<<` and `>>` as one operator. |
| Generics | `Name<A, B>` with no inner spaces. A `<` that begins a generic argument list is told apart from a comparison using the syntax tree. |
| Top-level items | One blank line between items. Consecutive items that are each written on one line and had no blank line between them stay adjacent (runs of `use` lines, one-line functions and types). Leading comments belong to the item below them. |
| Blank lines in bodies | Preserved, collapsed to at most one, and removed at the start and end of a body. |
| Lists | `(...)`, `[...]` and `{...}` lists are kept on one line when they fit, otherwise one item per line, indented, with a trailing comma. A trailing comma is dropped when the list fits on one line, except in a one-element tuple, which keeps `(x,)`. A parenthesized single expression never gains a comma. Indexing `a[i]` and repeat arrays `[x; n]` never take a comma. |
| Source-chosen expansion | A body, `match`, struct literal, struct type, record or array written over several lines (a newline right after its opening bracket) stays expanded; one written on a single line stays on one line when it fits and breaks otherwise. |
| Blocks | `{ a; b }` stays inline when written inline and it fits (`fn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }`); otherwise one statement per line. An `if`/`else` chain written inline is kept inline only if the whole chain fits, otherwise every block of the chain is expanded and each `}` is followed by ` else`. |
| `match` | One arm per line when expanded. A comma follows every expression arm (including the last); no comma follows an arm whose body starts with `{`, `if` or `match`. |
| Long expressions | Break before `&&` and `||` (or before `+`/`-` when there is no `&&`/`||`) with one extra indent. Call arguments and parameters break one per line. A closure or block as the last argument stays on the call line. |
| `where` | Stays where the source put it: on the header line, or on its own indented line. |
| `type` with `extend` | `type Name { ... } extend {` and `type Name [ ... ] extend {` stay on one line. Enum variant lists have no inner spaces: `[A, B(i32)]`. |

### Before and after

```text
fn  main( )->i32{let a:=1+2*3;  // keep me
    Ok( a )}
```

```text
fn main() -> i32 {
    let a := 1 + 2 * 3; // keep me
    Ok(a)
}
```

Long calls and conditions break by the rules above:

```text
fn f() -> i32 {
    let total := combine(first_value_long_name, second_value_long_name, third_value_long_name, 4, 5);
    if first_condition_is_long(a) && second_condition_is_long(b) && third_condition_is_long(c) && fourth(d) { 1 } else { 0 }
}
```

```text
fn f() -> i32 {
    let total := combine(
        first_value_long_name,
        second_value_long_name,
        third_value_long_name,
        4,
        5,
    );
    if first_condition_is_long(a)
        && second_condition_is_long(b)
        && third_condition_is_long(c)
        && fourth(d) {
        1
    } else {
        0
    }
}
```

`match` arms, block arms and trailing commas:

```text
fn arms(x: i32?) -> i32 {
    match x {
        Some(n) if n > 0 => n,
        Some(_) => {
            1
        },
        None => 2
    }
}
```

```text
fn arms(x: i32?) -> i32 {
    match x {
        Some(n) if n > 0 => n,
        Some(_) => {
            1
        }
        None => 2,
    }
}
```

Closures hug the call they end:

```text
apply(fn(value: i32) -> i32 {
    let doubled := value * 2;
    doubled + 1
}, 3);
```

Literals, parentheses and strings are untouched:

```text
let a := (0xFF_FF + 0b1010) * (1_000.5e-3 as i64);
let f := "{{literal}} {name}  é  ";
```

## Comments

The formatter reads comments from the text between tokens and attaches each to
a token:

- A comment on the same line after code is a *trailing* comment of the token
  before it and is printed at the end of the output line that holds that
  token. Several trailing comments on one output line keep their order; a line
  comment ends the line, so later comments move to the following lines at the
  next token's indentation (where a second pass finds them again).
- A comment on its own line is a *leading* comment of the next token and is
  printed on its own lines before it, at the indentation of that token.
  Comments before a closing bracket stay inside it.
- A block comment with code on both sides stays between those tokens.
- Blank lines between comments (and between a comment and the next item) are
  kept, collapsed to one.
- A comment forces the enclosing list to break only when it follows a `,` or an
  opening bracket (so `a, // note` keeps `a` on its own line) or sits on its own
  line.

Comment text is never changed except for trailing white space on each line.

## Implementation

[`crates/memobits-syntax/src/format.rs`](../../crates/memobits-syntax/src/format.rs)
is a token-driven layout engine (a Wadler/Prettier-style document printer with
groups, indentation and line suffixes). It uses the lexer's tokens and the
text between them, and the parsed syntax tree only for two facts that tokens
cannot decide: which `<`/`>` delimit generic arguments, and where each
top-level item starts. Because it never rebuilds source from the (lowered)
syntax tree, `try`, `T?`, `Self`-resolved types and grouped `use` lists print
exactly as written.

Evidence (tests, all run in the workspace suite):

- `crates/memobits-syntax/tests/format_corpus.rs`: every `.mb` file in the
  repository, every Memobits program embedded in a Rust test (string literals
  that parse), each re-flowed to one line, one token per line and three random
  layouts, and each with comments sprinkled between arbitrary tokens twelve
  ways, formats, keeps its syntax tree and comments, and is idempotent.
- `crates/memobits-syntax/tests/format_cases.rs`: targeted cases.
- `crates/memobits-cli/tests/s5_fmt.rs` and `examples_documented.rs`: CLI
  behavior, exit codes, and that every example stays formatted and behaves
  identically after formatting.

Memobits sources embedded in Rust test files are test inputs and are not
reformatted.

## Known limits

- `docs/design/proposed-language-guide.mb` is a historical proposal that does
  not parse; `mb fmt` reports its syntax errors and leaves it alone.
- Dense block comments inside an expression can move a line across the
  100-column limit between the first and second formatting pass; the
  self-check then reports PE008 instead of writing the file.
- Method chains and string concatenations are not broken at `.`; only the
  operators and lists above are break points.
