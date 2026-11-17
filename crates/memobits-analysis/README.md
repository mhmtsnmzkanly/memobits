# memobits-analysis

This crate provides parsing-independent semantic checks and lowering for the
implemented language subset. Run `cargo test --offline -p memobits-analysis` for
its unit and integration coverage.

`check_control_flow(&Module)` reports `TE020` for `break` and `TE021` for
`continue` outside a loop. It traverses nested blocks and expressions.

`check_types(&Module)` checks standalone source types and control-flow results.
The supported set includes `Bool`, internal Unit, signed and unsigned integers
through 64 bits, `f32`/`f64`, fixed arrays, structs, enums, aliases, calls,
assignments, matches, and primitive/aggregate `borrow` and `share` parameters.
It checks literal ranges, branch and function results, and the supported
operator rules. Standalone source imports and unresolved qualified paths require
project resolution and are diagnosed here. This pass checks types, not ownership.

`check_typed_module(&Module)` retains checked identities and type facts for
functions, locals, expressions, paths, and enum variants. `check_resolved_types`
and project lowering operate across reachable resolved modules, including local
imports and prelude aliases. Resolution is module-granular: all declarations in
a loaded module are checked, even if one function in it is unreachable from the
selected entry. The selected target determines which modules are loaded.

`lower_module` and `lower_resolved` produce validated `memobits-ir::Program`
values from successful checks. Lowering keeps function/local identities and
emits explicit control-flow blocks for branches, short-circuit operators, loops,
`break`, and `continue`. Primitive values are copied implicitly into owned
positions; aggregates and reference handles move. Run
`memobits-ownership::check_moves` on the resulting program to check supported
move and loan rules. A successful type check alone is not an ownership check.

The analysis and lowering passes intentionally reject language forms that are
not implemented yet. Errors use source-spanned diagnostics; type-pass codes are
`TE001`–`TE017` and `TE022`–`TE032`, while `TE020` and `TE021` are control-flow
diagnostics. Parse source before invoking these APIs and handle parse errors
separately.

Fixed arrays support homogeneous inference, nested arrays, contextual numeric
literals, length matching, empty contextual literals, and repetition counts.
Executable typed facts and lowering support primitive and nested-array elements,
indexed reads and writes, whole-array moves, array-valued branches/results,
internal owned/borrow/share calls, and row loans. Repetition `[e; N]` evaluates
the initializer once per element; zero count evaluates it zero times. Moving an
aggregate row out of an array, references to primitive elements, and other
unsupported array forms remain rejected. See the fixed-array implementation
document for the complete supported boundary.

## Structs and type aliases

`type Name { fields }` declares a nominal struct and `type Name = Other;` an alias.
A type table (`types/typetable.rs`) is built once for all modules checked together:
struct identity is `module::Name` (so `use`, qualified paths and aliases all reach the
same definition), struct `TypeId`s follow module then declaration order, and aliases are
followed to their targets wherever a type is named (annotations, signatures, array
element types, field types, literals); an alias cycle is TE026. Standalone checking
(`check_types`, `lower_module`) uses the same table with a single unnamed module.

Executable support covers A1 to A4. A1: a struct literal `P { y: 2, x: 1 }` (all
fields exactly once, any order, evaluated in source order) as the initialiser of a
`let` binding, and primitive field reads `p.x` (copied implicitly into owned
positions such as `f(p.x)`; `p.x.copy()` is optional).
A2 adds `var` struct bindings; field writes `p.x = v` / `p.x op= v` (through a `var`
owner, a `var` owned parameter, a `share` parameter or a `var` share binding; TE004
otherwise), whole-struct moves and assignment (`let q := p;`, `q = p;`, literal or call
result as right-hand side, struct-valued `if`/block results), struct parameters
(owned, `borrow P`, `share P`; call sites write `p.borrow()` / `p.share()`) and
results. Field reads work through references. A struct value is accepted in the same
owned-value positions as an array (binding initialiser, `=` right-hand side, return and
tail, owned argument, branch tails). Field writes lower to the base, then the
right-hand side, then adjacent `FieldAddr(Share)` + `Store` (compound writes read the
field first).
Literal shape errors (missing, unknown or duplicate field, non-struct name) are TE023,
field access on a non-struct or an unknown field is TE024, field privacy (reading a
private field of another module's struct, or building such a struct from another
module unless every field is `pub`) is TE025, and a struct that contains itself by value
(or an alias cycle) is TE026. Still TE017: struct literals as temporaries or field
bases, field access on a call result (`make().x`), references to primitive fields
(`p.x.share()`, like `m[i][j].share()`) and `p.copy()`.
A3 (nesting) accepts struct-typed fields, array-typed fields and arrays of structs in
every combination and depth. A place is a root local plus a chain of index and field
steps (`a[i].pts[j].x`); lowering (`lower_place` / `address_chain`) evaluates the root
and each index left to right, then forms the checked address chain (`ElementAddr` /
`FieldAddr`, with the requested access on every level) and ends in `Load`, `Store` or the
reference itself (`l.a.borrow()`, `a[i].share()`, `p.pts.borrow()`). Supported forms:
nested literals (a field initialiser is an owned-value position), `l.a.x`, `p.pts[i]`,
`a[i].x` reads; writes and compound writes through any chain (TE004 through `let`, `borrow`
or immutable roots); whole sub-aggregate replacement (`l.a = P { .. }`, `a[i] = P { .. }`,
`p.pts = [..]`); repetition of a struct literal (evaluated per element). Moving a
sub-aggregate out (`let q := l.a;`, `let r := a[i];`, as an owned argument, returned) is
TE022 (partial moves are deferred). A struct containing itself by value, also through
arrays, is TE026.
Structs in exported signatures are rejected later by the backend (LE900). TE016 (unsupported enum declaration) is retired: enums are supported since B1.
Lowering emits `StructNew` and `FieldAddr` + `Load`; `TypedModule::types` carries the
checked struct definitions.

A4 adds whole-value destructuring `let P { x, y: alias } := value;` (`var` for mutable
bindings). Every field is named exactly once (missing, unknown or duplicate fields and
duplicate binding names are TE023; naming a non-struct is TE023; a reference source is
TE002; a field-extraction source such as `l.a` is TE022; a struct with a private field
from another module is TE025). Each field binds a new owned local of the field's type,
primitive or aggregate. Lowering evaluates the initialiser once, emits one
`Extract { base, field }` plus an initialising `Assign` per binding in pattern order, and
makes the last extraction `Consume` the whole value, so a source local is moved (BE001
on later use) and a call result or literal is simply consumed. A struct with no fields
is consumed by a `Capture`.

Enums (B1, `docs/design/enum-implementation.md`). `type Shape [ Empty, Circle(f64),
Rect(i32, i32) ]` is a nominal type in the same table and id space as structs
(`TypedModule::types` holds `TypeFact`s with `fields` or `variants`). Payloads are
non-Unit primitives, arrays, structs and enums in any nesting; an empty enum is TE027 and
by-value recursion (through arrays, structs and enums) is TE026 ("recursive enum").
Construction is a unit-variant path `Shape::Empty` or a call `Shape::Circle(1.5)`, with
local, `use`d, qualified and alias-qualified prefixes; arity is TE010, a payload type
mismatch TE002, and the wrong form (payload on a unit variant, a payload variant without
arguments, an unknown variant in the standalone check) TE028. Payload arguments are
owned-value positions evaluated left to right (aggregates move in, primitives copy). A unit
variant must itself be in an owned-value position (TE017 as a temporary). Enums are
whole-value aggregates everywhere structs are (bindings, moves, parameters, results,
joins, fields, array elements, repetition); there is no equality or field access (TE007/TE024). Lowering emits `EnumNew { ty, variant, payload }`; `FunctionFacts::
variant_uses` records which expressions are variant constructions.

`match` on owned enums (B2, "B2 checkpoint" in `docs/design/enum-implementation.md`). The
scrutinee is an owned local, a call result, a construction or a block/`if`/`match` yielding an
enum (a reference or element/field place is a borrowing match, see below). Patterns are flat: `Enum::Variant`,
`Enum::Variant(a, _)`, `_`; a pattern of another enum, an unknown variant, a bare identifier,
a wrong payload count or a repeated binding is TE030. Arms unify like `if` branches (TE013;
`return`/`break`/`continue` arms are `Never`). Without a `_` arm every variant must be matched
(TE031 lists the missing ones); a duplicate variant arm, an arm after `_` and a `_` after full
coverage are TE032 errors. Bindings are immutable owned locals scoped to their arm
(`FunctionFacts::matches` records the selected variant and bound `LocalId` per arm).
Lowering moves the scrutinee once into a hidden local, emits `EnumTag` and a `Switch` with one
block per arm, extracts each arm's bound payloads with `VariantExtract` (the last consumes the
cell) and joins arm values through a block parameter like `if`. `==`/`!=` on enums stays TE007
and suggests `match`.

Borrowing `match` (B3, "B3 checkpoint"). A scrutinee whose type is a reference to an enum
(`borrow`/`share` parameter or binding, `.borrow()`/`.share()`) or that is an element/field
place (`a[i]`, `l.shape`) is matched in place (`MatchFact::borrowed`): nothing is consumed,
primitive payload bindings are copies, aggregate payload bindings are `borrow T` reference
locals (so TE004 on writes and TE017 when moved out). Lowering forms the place reference
(a hidden reference local when needed), reads the tag through it with `EnumTag`, and emits
one `VariantAddr` per bound slot instead of `VariantExtract`; mutable matching stays deferred.
