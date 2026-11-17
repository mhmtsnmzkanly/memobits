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
11. **ENF validation consumer** — build a bounded lexer/parser subset with UTF-8
    and protocol-specific numeric constraints; expand conformance only after the
    language core is reliable.
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
  syntax (`Array<T, N>`, literals, `[expr; N]`, indexing) produces structured AST nodes.
- **Resolution** (`memobits-resolve`): loads reachable local modules from the
  application entry or library exports; checks lexical scopes, duplicate bindings,
  imports and aliases, visibility, enum variant paths, and prelude names. Public
  signatures reject private local types.
- **Type and flow analysis** (`memobits-analysis`): standalone and project-wide
  primitive checking (numeric defaults, literal ranges, signatures, calls, bindings,
  assignments, branches, return analysis, loop divergence). Loop control reports
  TE020/TE021. Type-only fixed-array analysis covers homogeneous element inference,
  contextual literal typing, annotation length checks, zero-count and divergent
  repetition flow, integer index types, and constant index bounds.
- **Typed IR** (`memobits-ir`): typed CFG with structural and operand/edge type
  validation; lowering of checked modules with canonical function identities across
  local modules, imports, and qualified paths; scalar reference handles and
  Borrow/Load/Store.
- **Ownership** (`memobits-ownership`, `check_ownership`): move checking for owned
  locals and temporaries, including numeric values, branch joins, and loop
  fixed points. Primitive `borrow` (read-only) and `share` (exclusive mutable)
  are lowered and checked, with loan conflicts, reference availability across
  joins and backedges, and rejection of invalid reference transport (BE002).
- **Wasm backend** (`memobits-wasm`): emits and validates the primitive subset:
  constant returns, direct calls restricted to the export-reachable closure,
  branches, checked integer arithmetic, IEEE float operations, and internal
  primitive references. Address-taken owners live in authoritative frame cells in
  a configurable stack region of linear memory with checked allocation and restoration on
  every return.
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

### Known limits of the implemented subset

- Analysis success is not an ownership or borrow-safety proof. Coverage is the
  tested subset.
- Standalone `analyze` does not support imported functions or user-defined types beyond the A1-A3 structs;
  `analyze-project` supports primitive signatures across resolved modules only.
- Resolution reachability works at module granularity. Source analysis checks all
  declarations in loaded modules; there is no per-definition incremental compilation.
- Reexports, alias expansion through type aliases, public-signature visibility
  closure, and full value/type namespace validation are missing.
- Borrow/share is primitive only. Reference-valued block and `if` results and
  returned references are rejected. Reference exports and reference returns are
  rejected, and no stable external reference ABI exists.
- Fixed arrays execute for primitive (non-Unit) elements: literals, repetition
  `[e; N]` (loop lowering; `[e; 0]` evaluates nothing, owned bindings cannot be
  repeated), `let` and `var` bindings, indexed reads inside arithmetic,
  comparison and condition expressions, element assignment `a[i] = v` and
  compound `a[i] op= v` on `var` arrays (TE004 on `let`), and whole-array moves
  `let b := a;` / `b = a;` (memory copy; the source is unavailable afterwards).
  Indices may be any integer type; constant out-of-range indices are TE008,
  dynamic ones (reads and writes) trap (`RE007`). Extracting an element into an
  owned position (binding, `=`, return, tail, owned argument, array element) is
  TE022. Nested arrays (WP4) work to any depth: `Array<Array<i32, 2>, 3>`,
  literals, repetition with an array element expression (each evaluation
  separate), `m[i][j]` reads, writes and compound writes, bounds traps and
  TE008 on either index, whole-row replacement `m[i] = [1, 2];`, and rows lent
  to `borrow`/`share` parameters with `m[i].borrow()` / `m[i].share()`.
  Arrays are also function results (`-> Array<T, N>`; struct-return storage
  owned by the caller) and `if`/block values; a result may be a literal,
  repetition, call, named local or parameter (a move) and feeds a binding,
  `=`, an owned argument, an element or another result. Arrays cross internal calls (WP3): owned (`a: Array<T, N>`, moved into
  the call; a literal, repetition or named array is accepted), `borrow` and
  `share` parameters with the same `.borrow()` / `.share()` call-site spelling
  as primitives, element reads through either reference, element and compound
  writes and whole-array stores through `share`, local `let r := a.borrow();`
  / `var r := a.share();` bindings and reborrowing a reference parameter. Loans carry
  projection paths (A4): two `share` rows of one matrix with constant indices
  are independent, with a dynamic index (`m[i]`, `m[j]`) they are BE005, and a
  write while an overlapping row or array borrow is live is BE005. Fixed arrays are complete for primitive and nested-array
  elements. Still gated: references to primitive elements (`a[0].share()`,
  TE017), indexing or borrowing a temporary (`make()[0]`, `[1, 2].borrow()`,
  TE017), extracting a row (aggregate element) into an owned position (TE022;
  primitive elements are copied implicitly, rows cannot be copied yet),
  whole arrays as operands or statements (TE017), reference-typed elements and
  returned references (TE017), non-primitive element types such as `Unit`,
  and arrays or array references in exported signatures (`main`, `[export]`,
  parameters or results), which the backend rejects with LE900. Layout: each
  array local, value, call result and join parameter owns an inline cell in the
  activation frame, which must fit the configured `[build].stack_size` (default
  1 MiB; repetition also uses a hidden accumulator cell, so it takes twice the
  array size, a known inefficiency; sizes use checked multiplication and nested sizes are products);
  larger layouts are a backend diagnostic. Literal lengths are capped at
  `u32::MAX` as an analysis bound, not a memory guarantee. See the WP1-WP4
  checkpoints in `fixed-array-implementation.md`.
- **Primitive copy** (`memobits-analysis`, `-ir`, `-ownership`, `-wasm`):
  `expr.copy()` is a compiler-known zero-argument method (like `.borrow()` /
  `.share()`) for integers, floats and `Bool`. The receiver may be a local or
  parameter, an array element at any depth (bounds-checked), or a primitive
  read through a `borrow`/`share` reference (`r.copy()`, `p[i].copy()`). It
  lowers to a distinct IR instruction `Copy { source }` whose source is a
  `Read` use and whose output is an ordinary owned value (a `Load` result stays
  read-only, so `validate_read_only_loaded_values` is unchanged). Ownership
  treats it as a non-consuming read: allowed while borrows are live, BE005
  while a `share` of the owner is live, BE001 on a moved local. It works in
  every owned position, including repetition elements (evaluated per
  iteration). `.copy()` on an array, a row or a reference to one is TE017
  ("copy is currently available only for primitive values"); arguments are
  TE010. Aggregate copy and copy-on-write are not implemented and the spelling
  remains provisional. `.copy()` on a primitive is now optional.
- **Implicit primitive copy** (`memobits-analysis`, `-ir` unchanged,
  `-ownership` unchanged): integers, floats and `Bool` are never moved. Binding,
  assigning, passing as an owned argument, returning, and using as an array,
  struct or repetition element all leave the source usable, and a primitive
  array element or struct field (or a primitive read through a `borrow`/`share`
  reference, `fn get(r: borrow i32) -> i32 { r }`) may be read into any owned
  position. Lowering (`Builder::owned`) emits the existing `Copy` instruction for
  every primitive local and every `Load` result that reaches an owned position, so
  the IR validator keeps rejecting consumed loaded values and the move checker
  needs no type knowledge: only aggregates and reference handles are ever
  consumed. A copy is a read, so BE005 still applies while a `share` of the
  owner is live. TE022 covers aggregate elements (rows, structs) and aggregate fields; reference handles keep their transport rules
  (TE017). Aggregates keep move semantics (BE001).
- Frame memory is an experimental fixed 64 KiB page with addresses below 16
  reserved. Traps lack detailed source mapping, do not unwind caller frames, and
  discard the instance; no persistent-instance reset policy exists.
- The Wasm output ABI is experimental: no imports or aggregate exports; artifact
  results use raw numeric representations.

### Not yet implemented

- Milestone 6 (Wasm generation): aggregate and collection emission; imports;
  stable ABI; per-definition reachability.
- Milestone 7 (ownership and borrow): aggregate and array ownership, disjoint
  field borrowing, explicit copy/removal for aggregates, and borrow/share of
  non-primitive types.
- Milestone 8 (runtime and collections): dynamic lists (fixed arrays are done), UTF-8 strings, Option/Result/outcome
  payloads, and normal-exit cleanup for aggregates.
- Milestone 9 (libraries and packages): source and binary dependency loading,
  package cycle detection, dependency import selection, external artifact
  packaging, separate app/library outputs beyond the current CLI, and remote fetching.
- Milestones 10-12 (A* and ENF consumers, optimization): not started.
- Milestone 13 (later design): task/host coordination, parallel execution,
  static storage, property/extension systems, ABI compatibility, and cross-language calls.
- Milestone 4 gaps: enum type analysis, enum exhaustiveness, and three-state
  outcome distinctions. Struct forms beyond A4 (whole-struct `.copy()`, references to primitive fields) are gated, not analysed.

### Next step

Fixed arrays of primitive and nested-array elements are complete (WP1-WP4), and
structs are complete through A4 (nesting, destructuring and field-disjoint loans;
`struct-implementation.md`). The next work is enums and `match` on the same
frame-cell model, using the whole-value destructuring and path-aware loans as the
base for variant payload patterns. The implicit primitive copy decided in
`decisions.md` is implemented. After that: copy of aggregates, references to
primitive fields, and an external array ABI if exports ever need one. Keep
TE017/TE022/LE900 gating every form not listed under the fixed-array and struct
status above.
