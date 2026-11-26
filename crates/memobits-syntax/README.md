# memobits-syntax

Source-spanned lexer and parser for the initial numeric language subset.
`parse(SourceId, text)` returns a module and diagnostics. A nonempty diagnostic
list means the recovered AST must not be treated as successfully compiled code.

Implemented syntax: functions, parameter access modes, basic named types,
field/enum/alias declarations, path imports with aliases, explicit and inferred
bindings, assignments, numeric/boolean expressions, calls, field access, blocks,
if/else, `match` over enum variants, return, loop, break, and continue. Nested block comments are supported.
A block-like statement (`if`, `match`, `loop`, or a bare block) at the start of a statement
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

`match scrutinee { Pattern => expr, Pattern => { block } }` parses to `ExprKind::Match`
with one `MatchArm { pattern, body }` per arm, in source order. A pattern is `_`
(`PatternKind::Wildcard`), a lone identifier (`PatternKind::Binding`, which analysis resolves
to a bare variant or a binding), a variant path with optional slots
(`PatternKind::Variant { path, slots }`) or a tuple (`PatternKind::Tuple`). Every slot is
itself a pattern, so patterns nest to any depth. Arms are
separated by commas, which may be omitted after a block-like body (`{`, `if`, `match`);
`return`, `break` and `continue` are accepted directly as an arm body (parsed as a
one-statement block); `=>` is a token. The scrutinee is parsed like an `if` condition, so a
struct literal there is SE002 (parenthesise it). A pattern is `_`, a literal (integer, optionally negative, bool, char or string), a name,
a variant path with sub-patterns, a tuple or `p | q` alternatives; an `if` guard may
follow it. Float literals, struct patterns and a missing separator are SE002 with a
message naming the gated form. A name that is a `const` is resolved to a constant
pattern before analysis; an array repeat count `[v; name]` accepts any identifier. `match` is a reserved word. Whether a pattern names a variant of the scrutinee's enum
is left to analysis.

Ordinary single-line UTF-8 string literals parse; escape sequences and default
parameter values are not supported. Generic parameters and type arguments are
parsed for functions, nominal types, interfaces, extensions and struct literals;
the later pipeline determines which generic forms are executable. Match syntax
includes nested tuple and variant patterns, literals, constant patterns,
alternatives and guards, but not float literals or struct patterns. The parser
is handwritten and uses Pratt precedence.

Fixed-array syntax includes structured `array<T, N>` (including nested element
types), element literals, repetitions, and postfix indexing. Counts are
source-located nonnegative integer literals or constant names. This crate only
parses syntax; typing, ownership and execution live in the later pipeline
crates, which gate unsupported forms with diagnostics.
