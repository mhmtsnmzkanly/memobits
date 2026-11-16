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

This pass reports unsupported user-defined types, imports, qualified paths,
ordinary field access. Primitive borrow/share parameters and named-owner conversions are supported for analysis and IR lowering. It does not resolve modules,
check ownership, or decide a public spelling for Unit annotations. `TE001`–
`TE017` are type-pass diagnostics; `TE020` and `TE021` are reserved for control
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
`continue`. Owned bindings, calls, assignments, and returns use consuming
operands; arithmetic and conditions read their inputs. Run
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
owned arguments and returns do not implicitly extract it. Reference-valued block
and if expressions remain conservatively unsupported, as do reference returns,
aggregate references, and reference rebinding assignments. Wasm reference
execution remains disabled. See `examples/analysis/references.mb`.

Fixed arrays are supported by the type-only APIs (`check_types` and
`check_resolved_types`): homogeneous inference, nested arrays, contextual numeric
literals, length matching, empty contextual literals, and repetition counts.
Executable typed facts/lowering still reject arrays with TE017. Indexing and
aggregate reference semantics remain unsupported. Repetition expressions are
type-checked once even at zero count; they are not expanded by analysis.
