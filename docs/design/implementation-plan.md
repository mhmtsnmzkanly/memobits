# Implementation Plan

This plan separates the accepted target language from what is implemented. The
milestones are ordered dependencies. The "Current status" section below describes
the implemented subset; a milestone is not complete merely because its crate exists.

## Milestones

1. **Workspace, project model, diagnostics** — establish crate boundaries and
   shared source/file identifiers; load `project.toml` or `--project PATH`,
   resolve the default `./src` root, validate required project fields, and
   report English diagnostics with file/line/column and stable diagnostic codes.
   Keep this phase to configuration and diagnostics; do not add language parsing.
2. **Lexing and parsing** — define source spans, tokens, syntax tree, recovery,
   and syntax diagnostics. Cover declarations, bindings, expressions, control
   flow, `type Name {}`, `type Name [...]`, aliases, imports, and manifest-driven
   module paths.
3. **Project graph and name resolution** — discover reachable modules from
   selected roots, resolve imports, visibility and aliases, apply prelude names,
   and reject missing imports, ambiguous names, private exports, and package
   dependency cycles.
4. **Type and control-flow analysis** — infer local types, check annotations,
   branch result compatibility, enum exhaustiveness, numeric defaults and
   integer overflow where statically provable, defaults completion, and Result /
   Option / three-state outcome distinctions. Produce source-located diagnostics.
5. **Typed intermediate representation and initial move checking** — lower checked syntax into a typed,
   explicit control-flow IR with source mapping. Keep ownership operations and
   runtime checks representable before adding optimization. Implement scalar move
   checks before treating the first Wasm execution path as language-conforming.
   Control-flow IR also supports static analysis; IR construction is not optimization.
6. **Wasm generation and validation** — compile a minimal application path to
   portable Wasm, validate artifacts, execute through the CLI host, and support
   application/library roots. Prove library reachability omits unrelated entry
   code and report backend/validation errors through the diagnostic layer.
7. **Ownership and borrow analysis/lowering** — implement moves (including
   numeric ownership), read-only `borrow`, exclusive mutable `share`, last-use
   lifetimes, mutation permissions, explicit copy/removal, and disjoint field
   borrowing. Reject conflicts before lowering cleanup and ownership into IR.
8. **Runtime and core collections** — implement controlled errors for dynamic
   integer overflow, invalid indexing and other checked operations; UTF-8 string
   primitives; fixed arrays and dynamic lists; Option/Result/outcome payloads;
   and normal-exit cleanup. Keep trap cleanup policy at the host/runtime boundary.
9. **Core libraries and package artifacts** — implement reusable APIs on top of
   the runtime, local binary dependency loading, `import` selection,
   `external` packaging, and separate app/library outputs. Remote fetching follows near distribution
    readiness. Defer a stable ABI.
10. **A* validation consumer** — build fixed-grid helpers and an A* example to
    exercise loops, collections, enums, ownership, and numeric behavior in a
    nontrivial client.
11. **ENF validation consumer** — start with the
    [bounded lexer fixture](enf-lexer-slice.md). Use a protocol reference to
    define UTF-8 handling, numeric constraints and parser conformance.
12. **Optimization** — measure representative programs, then optimize IR/Wasm
    while preserving diagnostics, ownership semantics, checked behavior, and
    portable output. Track compile time and runtime separately.
13. **Later design work** — design task/host coordination and parallel execution;
    revisit static storage and property/extension systems; then specify ABI
    compatibility and cross-language calls. These are not initial milestones.

## Current status

### Implemented

- **Project and CLI** (`memobits-project`, `memobits-cli`): manifest loading and
  module inventory; `project`, `syntax`, `analyze`, `ownership`, `resolve`,
  `analyze-project`, `ownership-project`, `build`, and `run` (source project or
  `.wasm` artifact, `--entry NAME`, `--lib`, `--output PATH`). Diagnostics carry
  stable codes with file/line/column. `check` is reported as unsupported.
- **Syntax** (`memobits-syntax`): basic declarations, parameter access, type forms,
  expression precedence, loop and control flow, and error recovery. Fixed-array
  types, literals, repetition, and indexing produce structured AST nodes.
- **Resolution** (`memobits-resolve`): loads reachable local modules from the
  application entry or library exports; checks lexical scopes, duplicate bindings,
  imports and aliases, visibility, enum variant paths, and prelude names. Public
  signatures reject private local types.
- **Type and flow analysis** (`memobits-analysis`): standalone and project-wide
  checking (numeric defaults, literal ranges, signatures, calls, bindings,
  assignments, branches, return analysis, loop divergence). Loop control reports
  TE020/TE021. Type-only fixed-array analysis covers homogeneous element inference,
  contextual literal typing, annotation length checks, zero-count and divergent
  repetition flow, integer index types, and constant index bounds.
- **Typed IR** (`memobits-ir`): typed CFG with structural and operand/edge type
  validation; lowering of checked modules with canonical function identities across
  local modules, imports, and qualified paths; scalar reference handles and
  Borrow/Load/Store.
- **Ownership** (`memobits-ownership`, `check_ownership`): move checking for owned
  aggregates and reference handles through branch joins and loop fixed points.
  Primitive values copy implicitly. Primitive and aggregate `borrow` and `share`
  are lowered and checked for conflicts, availability, and invalid transport.
- **Wasm backend** (`memobits-wasm`): emits primitives and supported fixed
  arrays, structs, and enums. It supports direct calls from export roots,
  branches, checked integer arithmetic, IEEE float operations, and internal
  references. Address-taken owners live in authoritative frame cells in
  a configurable stack region of linear memory. Allocation is checked and the
  stack pointer is restored on each normal return.
- **Runtime and execution** (`memobits-runtime`, wasmi): fresh instance per run,
  a default fuel budget of ten billion units (overridable with `mb run --fuel N`
  or `--no-fuel-limit`), structured host errors for traps. Source and artifact
  execution share the same path and print scalar results. The former AST
  interpreter was removed from the repository and never defined the semantics.

### Structs (A1, A2, A3, A4)

- **Structs, first slice** (`memobits-analysis`, `-ir`, `-ownership`, `-wasm`):
  `type P { x: i32, pub y: i32 }` declarations with non-Unit primitive fields;
  struct literals with every field exactly once, in any order, as a `let`
  initialiser; primitive field reads `p.x` in expressions and conditions; and
  `p.x.copy()`. `pub` types and fields work across modules. IR uses
  `TypeDef`/`Type::Struct`, `StructNew` and `FieldAddr` + `Load`; the backend
  lays fields out in declaration order at natural alignment inside the activation frame (bounded by the configured `[build].stack_size`, default 1 MiB).
  Reading a primitive field into an owned position copies it implicitly (see
  "Implicit primitive copy" below). Private access is TE025. The A2-A4
  sequence is in `struct-implementation.md`.
- **Structs, A2**: `var` structs; field writes `p.x = v` / `p.x op= v`
  (`FieldAddr(Share)` + `Store`, base then right-hand side then store); whole-struct
  moves and assignment; struct parameters (owned, `borrow`, `share`, with
  `.borrow()` / `.share()` at call sites), struct results through the hidden
  caller-allocated pointer, and struct-valued `if`/block results. Built on the
  array aggregate machinery (generalised to "aggregate" in the backend and IR
  validator). Details and the gate table are in `struct-implementation.md`.
- **Structs, A3 (nesting)**: struct-typed fields, array-typed fields and arrays
  of structs, in every combination and to any depth, through chained
  `FieldAddr` / `ElementAddr` projections exactly like nested arrays: nested
  literals, `l.a.x`, `a[i].pts[j]` reads, writes and compound writes
  (index, then index, then right-hand side, then the checked store), whole
  sub-aggregate replacement (`l.a = P { .. }`, `a[i] = P { .. }`,
  `p.pts = [..]`), `l.a.borrow()` / `a[i].share()` / `p.pts.borrow()` lent to
  `borrow`/`share` parameters (overlap follows projection paths since A4), and repetition of a struct literal evaluated per element.
  Moving a sub-aggregate out is TE022 for fields and elements alike (partial
  moves are deferred); recursive containment through arrays is TE026; layout
  nests with natural alignment and checked arithmetic inside the configured
  stack; structs and arrays in exported signatures stay LE900. Still gated:
  references to primitive fields and elements (`l.a.x.share()`), whole-struct
  `.copy()` and field access on a call result. See the A3 checkpoint in
  `struct-implementation.md`.
- **Structs, A4 (destructuring and disjoint loans)**: `let P { x, y: alias } := v;`
  (and `var`) consumes the whole value and binds every field, primitive or
  aggregate, through the IR instruction `Extract`; the validator keeps every other
  partial move unrepresentable. Loans carry projection paths (fields, constant
  and dynamic indices): distinct fields and distinct constant indices are
  independent, a dynamic index overlaps every index, a parent overlaps its
  children, and uncertain cases overlap. Structs are complete for this phase. See the A4
  checkpoint in `struct-implementation.md`.

### Enums (B1)

- **Enum types as values (no `match` in B1)** (`memobits-analysis`, `-ir`, `-ownership`,
  `-wasm`): `type Shape [ Empty, Circle(f64), Rect(i32, i32) ]` declarations whose
  payloads are primitives, arrays, structs and enums in any nesting (by-value
  recursion is TE026, an empty enum TE027); construction `Shape::Empty` and
  `Shape::Circle(1.5)` through local, `use`d, qualified and aliased paths
  (arity TE010, payload type TE002, form TE028); and enums as ordinary
  aggregates: bindings, whole assignment, moves (BE001), owned / `borrow` /
  `share` parameters, results, joins, struct fields, array elements and
  repetition. IR: `Type::Enum`, `TypeDefKind::Enum`, `EnumNew`. Layout: a `u8`
  (up to 256 variants) or `u16` tag at offset 0, then the payload area aligned
  to the largest payload alignment, size the largest variant. Enums in exported
  signatures are LE900. Loans are whole-enum conservative. Sequence,
  representation and the gate tables are in `enum-implementation.md`.

### Enums (B2)

- **Owned `match` with exhaustiveness** (`memobits-syntax`, `-resolve`, `-analysis`,
  `-ir`, `-ownership`, `-wasm`): `match scrutinee { Enum::Variant(a, _) => expr,
  Enum::Unit => { block }, _ => expr }` as an expression, in owned locals, call
  results, constructions and owned parameters. Flat patterns only. Arms unify
  like `if` branches (divergent arms allowed); missing variants are TE031,
  wrong-enum / arity / unsupported patterns TE030, unreachable arms TE032,
  non-enum or borrowed scrutinees TE029, matching a field or element TE022.
  The scrutinee is consumed (BE001 afterwards) and payload bindings are owned
  locals. IR: `EnumTag`, `VariantExtract`, `Switch`. Aliases of enum types now
  resolve variant paths in the resolver. Details in the B2 checkpoint of
  `enum-implementation.md`; example in `examples/projects/enums/`.

### Enums (B3)

- **Borrow matching** (`memobits-analysis`, `-ir`, `-ownership`, `-wasm`): a
  scrutinee that cannot be moved (a `borrow`/`share` parameter or reference
  binding, `x.borrow()`, an element or field place such as `a[i]` or `l.shape`)
  is matched in place. Primitive payload bindings are copies, aggregate payload
  bindings are read-only `borrow` references (indexable, field-readable, usable
  as `borrow` arguments; not movable, TE017, not writable, TE004). IR:
  `VariantAddr`; loan path step `Step::Variant`, where different variants of one
  enum place overlap. Disjoint writes during a payload borrow are accepted, an
  overlapping write is BE005 with the place named. Mutable matching stays
  deferred. Details in the B3 checkpoint of `enum-implementation.md`; example
  in `examples/projects/enums/`.

### Current limits

- Standalone analysis resolves types defined in the same file. Use project
  analysis for imported definitions. Reachable modules are checked in full.
  Wasm emission follows the function closure of the entry or library exports.
  Per-definition incremental compilation and external package linking are pending.
- Fixed arrays can hold primitives and nested aggregates. Constant out-of-range
  indices are diagnosed at compile time. Dynamic bounds checks report RE007.
  Implicit copies cover primitive fields and elements. Moving an aggregate out
  of a field or element is gated, while whole-struct destructuring consumes its
  owner. See [fixed arrays](fixed-array-implementation.md) and
  [structs](struct-implementation.md) for supported projections and operations.
- Borrow and share support internal primitive and aggregate parameters.
  Distinct struct fields and constant indices can be treated as disjoint.
  Dynamic indices are conservative. Reference returns, reference-valued
  branch results, and direct borrows of primitive projections are gated.
- Wasm uses the configured stack region (default 1 MiB). Checked traps carry a
  cause and source location when metadata is available. The runner discards
  trapped instances. Library exports use scalar signatures. Application
  entries can also use the private `main` outcome adapter for zero-argument
  `Result` and `Attempt` functions with primitive success payloads.
- Dynamic lists, UTF-8 strings, heap-backed cleanup, general aggregate copy,
  mutable pattern bindings, `defaults`, and `try` are pending.
- The [bounded ENF lexer fixture](enf-lexer-slice.md) runs its ASCII decimal
  acceptance cases from source and standalone Wasm. Protocol grammar,
  UTF-8 token handling and parser conformance require a protocol reference.
- Local and remote package dependencies,
  optimization, and a stable external ABI remain later milestones.

### A* validation consumer

The [A* example project](../../examples/projects/astar/README.md) completes
the fixed-grid consumer milestone. It uses four-neighbor movement with unit
costs, Manhattan distance, and a fixed-array frontier scanned for the lowest
estimated total cost. The example checks a known optimal cost and an
unreachable goal. CLI integration coverage runs both checks from source and
from a standalone Wasm build.

### Compiler-known outcome types

Owned `Option<T>`, `Result<T, E>`, and `Attempt<T, E>` use the enum pipeline
for construction, internal calls, and `match`. The compiler-known `Error`
root has a public `code: u32` field. Derived error types inherit fields in
ancestor-first order and carry a hidden concrete type tag. Zero-argument
application entries can return `Result` or `Attempt` with primitive success
payloads. The runtime reports the same outcome in source and artifact runs.
The [outcome implementation plan](outcome-implementation.md) describes the
adapter and the function-local `Option<borrow T>` slice. Explicit local
annotations enable construction, consuming local moves and matches with
last-use loan tracking. Other reference type arguments remain gated with
TE017.
Owned conversion to an Error ancestor and reporting its retained concrete
identity also remain pending.
