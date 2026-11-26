# Implementation Plan

Status snapshot: 2026-11-26. The Current status section summarizes implemented
milestones and present boundaries. The [roadmap](../roadmap.md) is the
authoritative restart point, verification record, and list of next work. Dated
checkpoints in topic documents remain implementation history.

This plan separates accepted target design from implementation status. The
milestones are ordered dependencies; a milestone is not complete merely because
its crate exists. The Current status section reflects the snapshot above.

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
   primitives starting with [owned literals and byte length](utf8-text-slice.md);
   fixed arrays and dynamic lists; Option/Result/outcome payloads;
   and [owned heap storage with normal-exit cleanup](owned-heap-foundation.md).
   Keep trap cleanup policy at the host/runtime boundary.
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

### Current implementation status (2026-11-26)

The following is the current milestone summary. Detailed historical design
checkpoints remain in the topic documents linked below; the
[roadmap](../roadmap.md) is the authoritative restart point.

- **Stages 1–4 complete.** The workspace, CLI, parser/resolver, type and flow
  analysis, typed IR, move/loan analysis, Wasm backend, project tests, and the
  documented language surface are implemented. Source project and standalone
  Wasm execution share the runtime path. Current commands include `check`,
  `test`, and `fmt` in addition to analysis, build, and run commands.
- **Ownership and data types.** Structs, enums, arrays, tuples, outcomes, Lists,
  Boxes, String ownership, closures, and supported nested owner transport are
  implemented within their documented limits. Borrow/share access is checked
  for admitted internal calls and local handles. Partial moves from live
  aggregates, reference returns, and broader reference transport remain gated.
  See the per-feature design notes and the roadmap's known-open-items list.
- **Language extensions.** Interface selection, generic functions and types,
  bounded const parameters, associated `Rhs`/`Output`, user-defined operators,
  range loops, patterns, `const`, `Self`, and the stage 4 closure/Box work ship.
  Specialization is capped at 256. Explicit call-site type arguments, generic
  methods in interface declarations, and some nested associated projections
  remain open.
- **Text and allocation.** The source spelling is lowercase `string`; `char`
  traversal, checked UTF-8 operations, and the guest size-class allocator ship.
  `Bytes` is removed; use `array<u8, N>`. Owner transport still has the
  specific restrictions recorded in the roadmap.
- **Tooling and outside-world boundary.** `mb fmt` is shipped (Stage 5 step 1).
  The next work is Wasmtime execution parity and Component Model support, then
  packages and LSP. The current host capability is the single bounded CLI
  `write_i32` Wasm import; broader host integration and stable ABI are deferred.

The roadmap records the verification counts and exact next steps. Topic documents
such as [struct implementation](struct-implementation.md), [enum implementation](enum-implementation.md), [Box](box.md), [Wasm backend](wasm-backend.md), and [formatting](formatting.md) provide lower-level implementation detail.

### A* validation consumer

The [A* example project](../../examples/apps/astar/README.md) completes
the fixed-grid consumer milestone. It uses four-neighbor movement with unit
costs, Manhattan distance, and a fixed-array frontier scanned for the lowest
estimated total cost. The example checks a known optimal cost and an
unreachable goal. CLI integration coverage runs both checks from source and
from a standalone Wasm build.

### Compiler-known outcome types

Owned `T?`, `T ! E`, and `T ?! E` use the enum pipeline
for construction, internal calls, and `match`. The compiler-known `Error`
root has a public `code: u32` field. Derived error types inherit fields in
ancestor-first order and carry a hidden concrete type tag. Zero-argument
application entries can return `T ! E` or `T ?! E` with primitive success
payloads. The runtime reports the same outcome in source and artifact runs.
The [outcome implementation plan](outcome-implementation.md) describes the
adapter and the function-local `(borrow T)?` slice. Explicit local
annotations enable construction, consuming local moves and matches with
last-use loan tracking. Other reference type arguments remain gated with
TE017.
Owned conversion to an Error ancestor and reporting its retained concrete
identity also remain pending.
