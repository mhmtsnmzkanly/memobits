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
  a fixed one-page linear memory with checked allocation and restoration on
  every return.
- **Runtime and execution** (`memobits-runtime`, wasmi): fresh instance per run,
  bounded default fuel, structured host errors for traps. Source and artifact
  execution share the same path and print scalar results. The former AST
  interpreter was removed from the repository and never defined the semantics.

### Known limits of the implemented subset

- Analysis success is not an ownership or borrow-safety proof. Coverage is the
  tested subset.
- Standalone `analyze` does not support imported functions or user-defined types;
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
  TE022. Arrays cross internal calls (WP3): owned (`a: Array<T, N>`, moved into
  the call; a literal, repetition or named array is accepted), `borrow` and
  `share` parameters with the same `.borrow()` / `.share()` call-site spelling
  as primitives, element reads through either reference, element and compound
  writes and whole-array stores through `share`, local `let r := a.borrow();`
  / `var r := a.share();` bindings and reborrowing a reference parameter. Any
  element access overlaps the whole array in the loan checker. Still gated with
  TE017: array results, nested arrays, non-primitive elements, array-valued
  `if`/block results, whole arrays as operands or returns, array literals and
  repetition outside a binding initializer, `=` or an owned argument, indexing a
  non-local, element references, borrowing a temporary. Arrays and array
  references in exported signatures (`main`, `[export]`) are rejected by the
  backend with LE900. Layout: each
  array local owns an inline cell in the 32 KiB-capped activation frame (repetition
  also uses a hidden accumulator cell); larger layouts are a backend diagnostic.
  Literal lengths are capped at `u32::MAX` as an analysis bound, not a memory
  guarantee. See the WP1-WP3 checkpoints in `fixed-array-implementation.md`.
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
- Milestone 8 (runtime and collections): fixed-array layout and execution with
  dynamic bounds checks, dynamic lists, UTF-8 strings, Option/Result/outcome
  payloads, and normal-exit cleanup for aggregates.
- Milestone 9 (libraries and packages): source and binary dependency loading,
  package cycle detection, dependency import selection, external artifact
  packaging, separate app/library outputs beyond the current CLI, and remote fetching.
- Milestones 10-12 (A* and ENF consumers, optimization): not started.
- Milestone 13 (later design): task/host coordination, parallel execution,
  static storage, property/extension systems, ABI compatibility, and cross-language calls.
- Milestone 4 gaps: user-defined type analysis, enum exhaustiveness, and
  three-state outcome distinctions.

### Next step

Continue the array work packages with WP4: nested arrays and array results. Keep
TE017 gating every form not listed under the fixed-array status above.
