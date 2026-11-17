# memobits-syntax

Source-spanned lexer and parser for the initial numeric language subset.
`parse(SourceId, text)` returns a module and diagnostics. A nonempty diagnostic
list means the recovered AST must not be treated as successfully compiled code.

Implemented syntax: functions, parameter access modes, basic named types,
field/enum/alias declarations, path imports with aliases, explicit and inferred
bindings, assignments, numeric/boolean expressions, calls, field access, blocks,
if/else, return, loop, break, and continue. Nested block comments are supported.
A block-like statement (`if`, `loop`, or a bare block) at the start of a statement
ends at its closing `}`: following `[`, `(`, `.`, or binary operators start a new
statement or tail instead of continuing it. In other positions these forms are full expressions.
The parser accepts member-call spellings such as `value.borrow()`,
`value.share()`, and `value.copy()` as ordinary call and field syntax; it does
not assign access or copying semantics to them.

Struct literals `Name { field: expression, ... }` (path names such as
`geom::Point { .. }` are allowed) keep their initialisers in source order; every
field needs an explicit `name: value` (shorthand `Name { x }` is rejected) and a
trailing comma is accepted. A literal is **not** parsed where a `{` would start a
block right after an expression: directly in an `if` condition
(`if p == P { x: 1 } { .. }`) the parser reports SE002 and asks for parentheses,
as in Rust. Parenthesised (`if (P { x: 1 }).x == 1 { .. }`) or otherwise
delimited literals (call arguments, indices, array elements) are fine, and the
restriction ends inside any nested block. Whole-value destructuring
`let Type { f, g: alias } := v;` (and `var`) parses to `StatementKind::Destructure`
with a path-qualified type name and one `FieldPattern` per entry. Nested patterns
(`g: Inner { .. }`), `..` omission and a missing `:=` are SE002 with a message that
says what is gated; checking the fields against the declaration is left to analysis.

SE001 reports lexical errors; SE002 reports unexpected or missing syntax.
Locations are UTF-8 byte offsets. Name resolution, type checking, ownership,
visibility, exhaustive matching, and control-flow legality are not performed.

Strings, general generic types, match patterns, defaults and try are still pending. The design guide covers the target language, not this crate's
current accepted subset. The parser is handwritten and uses Pratt precedence.

Fixed-array syntax includes structured `Array<T, N>` (including nested element
types), element literals, repetitions, and postfix indexing. Counts are
source-located nonnegative integer literals. Other generic constructors are
rejected. This crate only parses arrays; typing, ownership and execution live in
the later pipeline crates, which gate unsupported array forms with diagnostics.
