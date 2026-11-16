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

SE001 reports lexical errors; SE002 reports unexpected or missing syntax.
Locations are UTF-8 byte offsets. Name resolution, type checking, ownership,
visibility, exhaustive matching, and control-flow legality are not performed.

Strings, general generic types, match patterns, defaults, try, and destructuring
are still pending. The design guide covers the target language, not this crate's
current accepted subset. The parser is handwritten and uses Pratt precedence.

Fixed-array syntax includes structured `Array<T, N>` (including nested element
types), element literals, repetitions, and postfix indexing. Counts are
source-located nonnegative integer literals. Other generic constructors are
rejected. This crate only parses arrays; typing, ownership and execution live in
the later pipeline crates, which gate unsupported array forms with diagnostics.
