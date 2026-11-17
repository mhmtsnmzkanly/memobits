# memobits-analysis

`check_control_flow(&Module)` reports `TE020` for `break` and `TE021` for
`continue` outside a loop. It traverses nested blocks and expressions.

`check_types(&Module)` checks the standalone primitive subset: `Bool`, internal
Unit, `i8/i16/i32/i64`, `u8/u16/u32/u64`, and `f32/f64`. Integer and float
literals default to `i32` and `f64`; annotations and parameter types can
constrain literals. The pass checks local bindings and shadowing, arithmetic,
logical and comparison operators, `if` conditions and branch results, local
function calls, assignments, explicit returns, and function tail results.
It checks integer literal ranges, including the signed minimum written with
unary minus. A non-Unit function must have a tail value or a provable return
on every branch. Loops with no reachable break are divergent, including loops that return from
the function. A reachable break permits normal completion and therefore requires
a suitable result afterward. Nested loop breaks remain local. Conditions are
not constant-folded by this flow pass.

This pass reports unsupported enum declarations (TE016), imports, qualified
function paths and non-struct field access. Struct and alias declarations are
supported (see below). Primitive borrow/share parameters and named-owner conversions are supported for analysis and IR lowering. It does not resolve modules,
check ownership, or decide a public spelling for Unit annotations. `TE001`–
`TE017` and `TE022` are type-pass diagnostics; `TE020` and `TE021` are reserved for control
flow. Parse first and handle syntax diagnostics separately. Both analysis
passes return source-spanned diagnostics and must be called independently.

`check_typed_module(&Module)` runs the standalone type and control-flow checks
and returns retained facts only when both succeed. Each function has a
`FunctionId`; its parameters and local bindings have fresh `LocalId` values,
including distinct IDs for shadowed names. Expressions have per-function
`ExprId` values and IR types where they produce a value. Path uses identify
either a local or a function, so a later lowering pass can use the checked
identity without resolving names again. These facts use `memobits-ir` types.
A divergent expression has no value type. For a signed-minimum literal such
as `-128` constrained to `i8`, only the unary expression has a type fact: the
positive operand alone does not fit `i8`. Project lowering retains equivalent
facts across every resolved source module.

Parameter `Access` is retained independently from local rebinding mutability in
function signatures, local facts, and local path-use facts. Primitive borrow and share parameters retain reference types. Named-owner conversions produce explicit loans; scalar operations read via Load and share assignments lower to Store. `TE017` still rejects unsupported reference escapes and access conversions.

`check_resolved_types(&Project, &Resolution)` checks the same primitive subset
across reachable modules after successful resolution. It accepts local function
calls, imported and prelude aliases, and qualified calls. Function identities
remain module qualified, so equally named functions in separate modules retain
their own signatures. The pass returns no type diagnostics when resolution has
errors. It is still a subset check: it does not check ownership, user-defined
types, or complete project semantics.

`lower_module(&Module, package, module_path)` lowers a successfully checked
standalone module to validated `memobits-ir::Program`. `lower_resolved(&Project,
&Resolution)` checks a successful target-rooted resolution once, retains facts
across its modules, and lowers them to one program with canonical package/module
function identities. Function IDs follow sorted module order and source function
order; imported aliases, prelude aliases, and qualified references point to the
same function identity. Invalid resolutions return their existing diagnostics,
and type or control-flow errors prevent IR output. Resolution is module-granular,
so all functions in each loaded module are included even if a function within
that module is unreachable from the selected root. The selected target controls
which modules are loaded, so library lowering excludes an unrelated application
entry. Wasm emission subsequently removes functions outside the selected export call closure, including unrelated same-module entry functions. Both lowering APIs reuse retained expression types and local/function
identities. Control flow uses explicit
blocks for `if`, short-circuit Boolean operators, loops, `break`, and
`continue`. Owned bindings, calls, assignments, and returns consume aggregates
and reference handles; primitive values (integers, floats, `Bool`) are copied
implicitly with an IR `Copy` instead of being moved, and arithmetic and
conditions read their inputs. Run
`memobits-ownership::check_moves` on the resulting program for availability
diagnostics. Lowering does not check ownership or implement user-defined types.

Before producing IR, both lowering APIs also fold pure integer literal unary and
arithmetic expressions using their retained integer type facts. `LE001` reports
provable overflow and `LE002` reports a statically known zero divisor. The pass
covers signed and unsigned widths through 64 bits, including signed minimum
divided by negative one. Calls and local values are not folded; floating-point
operations keep IEEE behavior. Dynamic integer operations remain for runtime
checking.

Run tests with `cargo test --offline -p memobits-analysis`.

Known integer-zero divisors are rejected before IR output even when their
numerator is dynamic (`x / 0`, `x % (2 - 2)`). Floating-point zero division
retains IEEE behavior; unknown integer divisors are checked during execution.

Source references are now supported through the ownership gate, including calls
across resolved local modules. Reference bindings move by default. Arithmetic,
comparisons, unary operators, and Bool conditions read the primitive referent;
a primitive referent is copied implicitly into owned arguments, bindings with an
annotation and returns (`fn get(r: borrow i32) -> i32 { r }`). Reference-valued block
and if expressions remain conservatively unsupported, as do reference returns,
aggregate references, and reference rebinding assignments. Wasm reference
execution remains disabled. See `examples/analysis/references.mb`.

Fixed arrays are supported by the type-only APIs (`check_types` and
`check_resolved_types`): homogeneous inference, nested arrays, contextual numeric
literals, length matching, empty contextual literals, and repetition counts.
Executable typed facts/lowering accept arrays of primitive elements and nested
arrays (`Array<Array<i32, 2>, 3>`, `m[i][j]`, `m[i] = [..]`, rows lent with
`m[i].borrow()` / `m[i].share()`): literals,
repetition `[e; N]` (lowered to a loop over a hidden accumulator; zero count
evaluates nothing, count one evaluates once), `let`/`var` bindings, indexed
reads inside expressions, element assignment (`a[i] = v`, `a[i] op= v`, TE004 on
`let` arrays), and whole-array moves (`let b := a;`, `b = a;`). Primitive elements
are copied implicitly into owned positions (`let x := a[i];`, `a[i] = a[j];`);
`TE022` rejects moving an aggregate element (a row) into an owned position. The
primitive `expr.copy()` is optional; arrays and rows cannot be copied yet (TE017). Arrays also cross internal calls as
owned, `borrow` and `share` parameters (`Reference { inner: Array }` in IR), with
element reads through either reference, element writes through `share`, local
`.borrow()` / `.share()` bindings and reborrows; argument/parameter length or
element mismatches are TE002 and writes through a borrow are TE004. Arrays are
also function results and `if`/block values (an array-typed join parameter in
IR). Every other array form (references to primitive elements, indexing a
temporary such as `make()[0]`, borrowing a temporary, whole arrays outside an
owned-value position, reference elements) is still gated with TE017. Repetition expressions are
type-checked once even at zero count; analysis facts never expand them.

## Structs and type aliases

`type Name { fields }` declares a nominal struct and `type Name = Other;` an alias.
A type table (`types/typetable.rs`) is built once for all modules checked together:
struct identity is `module::Name` (so `use`, qualified paths and aliases all reach the
same definition), struct `TypeId`s follow module then declaration order, and aliases are
followed to their targets wherever a type is named (annotations, signatures, array
element types, field types, literals); an alias cycle is TE026. Standalone checking
(`check_types`, `lower_module`) uses the same table with a single unnamed module.

Executable support covers A1 and A2. A1: a struct literal `P { y: 2, x: 1 }` (all
fields exactly once, any order, evaluated in source order) as the initialiser of a
`let` binding, and primitive field reads `p.x` (copied implicitly into owned
positions such as `f(p.x)`; `p.x.copy()` is optional). Fields are primitives only.
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
bases, field access on a call result (`make().x`), field-level references
(`p.x.share()`), `p.copy()`, struct-typed and array-typed fields, arrays of structs.
Structs in exported signatures are rejected later by the backend (LE900). Enum types used as value types report TE001 (and the declaration TE016).
Lowering emits `StructNew` and `FieldAddr` + `Load`; `TypedModule::types` carries the
checked struct definitions.
