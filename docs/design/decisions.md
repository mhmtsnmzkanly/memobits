# Accepted Design Decisions

This document records accepted language and project direction. It describes the
target design, not features already implemented. Syntax examples are normative
only where explicitly stated; unresolved API spellings remain proposals.

## Project and build

- The project is a Rust workspace with crates under `crates/`; implementation
  begins with project discovery/configuration and diagnostics.
- The default manifest is `project.toml`. `--project PATH` selects another
  manifest. Unless configured otherwise, sources are rooted at `./src`.
- CLI execution and portable Wasm output are the target; begin with compile and
  run. Reconsider a separate interpreter after measuring costs.
- Project identifiers, diagnostics, comments, and published docs use English.
- Package metadata and application entry belong under `[package]`. Source files
  map to modules by path; compile reachable dependencies from selected roots.
- Source imports use `use`. `pub` permits cross-module visibility; declarations
  without it are module-private. The manifest `[export]` table maps external
  names to public internal definitions; exporting private definitions is an error.
- `[prelude]` maps automatically available short names; no extra `use` is needed.
- Dependency selection is the required `import` field. `import = []` selects all
  public exports. Dependencies may be local or remote Wasm artifacts. Source dependencies identify manifest-bearing packages. Container details and
  transitive distribution rules remain open. Remote fetching is deferred.
- `external = true` keeps a dependency as a separate artifact; `false` bundles it
  with application output. Omission means `false`. Application and library
  builds have separate roots; library output excludes unrelated entry code.
- Package dependency cycles are rejected. Stable ABI is a later goal, not an
  experimental-stage guarantee. Cross-language calls follow the core language.

## Bindings, values, and control flow

- `let` bindings cannot be reassigned or mutated through; `var` bindings can
  change while retaining their type. Bindings require an initializer. `:=`
  infers a type; `:` introduces an annotation. Shadowing creates a new binding.
- Owned assignment and owned function parameters transfer ownership, including
  numeric values. Basic numeric arithmetic and comparisons read their operands.
- Function parameter access is fixed by its signature: `T` takes ownership,
  `borrow T` grants read-only borrowing, and `share T` grants exclusive mutable
  borrowing. Call syntax cannot override the signature. A `share` parameter
  needs no extra `var`; mutation of an owned parameter requires `var`.
- `share` is not shared ownership. A `let` owner cannot produce a mutable share.
  A locally stored share binding requires `var` to mutate its target. Conflicting
  access is rejected while a borrow remains live; liveness follows last use.
  Proven disjoint child fields may be borrowed independently; uncertain dynamic
  locations are treated as overlapping. Borrowed fields in user structs are
  deferred, while borrowed payloads in Option/result-like types are supported.
- Copying is explicit and available only for copyable types. Copy-on-write may
  provide independent value semantics for suitable collections; it is distinct
  from `share`. Exact copy method spelling is still provisional. Primitive
  `expr.copy()` (integers, floats, `Bool`) is implemented with this spelling:
  it only reads its receiver (a local, an array element, or a value read
  through a reference) and yields a fresh owned value. Aggregate copy and
  copy-on-write remain open.
- Collections are homogeneous. `Array<T, N>` has fixed length; `List<T>` is
  dynamic. `let` prevents element mutation. Indexing checks bounds; proven bad
  constant indices are compile errors, dynamic failures are controlled runtime
  errors. `get` expresses absence as `Option`. Extracting an element into an
  owned binding requires explicit borrow/share/copy/removal. Removal transfers
  ownership from a dynamic list; fixed arrays need a replacement operation.
- Conditions are Bool. Value-producing branches have one compatible result
  type; use an enum for alternatives with different payload types. Enums support
  payloads and exhaustive pattern matching, with Rust-inspired semantics.
- Initial looping supports `loop`, `break`, and `continue`; there is no `while`.
- A common three-state result distinguishes success, skipped/not performed, and
  failure. It is distinct from `Option` absence. `try` propagation is optional
  syntax sugar for matching a Result: with an `else` block it handles the error;
  without one it discards the Result error. It does not catch traps. Exact
  spelling/translation of the sugar is a compiler detail.
- Functions may declare `defaults` for normal completion without an explicit
  result. Explicit returns and tail values win; a bare return or ordinary
  valueless completion yields the default. This is not error or trap recovery.
  Evaluate the default only when needed, after normal return checking exists.

## Types, numbers, and text

- Type declarations use `type Name { fields... }` for field-based types,
  `type Name [ variants... ]` for enums, and `type Name = Other;` for aliases.
- Type parameters exist only on compiler-known types: `Array<T, N>`, `List<T>`,
  `Option<T>`, `Result<T, E>`, and the three-state `Outcome<T, E>`. They share
  one category with `Array`: the compiler instantiates them per use.
  User-defined generic types are not part of the language.
- The prelude exposes the variants of `Option`, `Result`, and `Outcome` by short
  name (for example `Some`, `None`). Variants of user enums are written
  `Type::Variant`. `Result` and `Outcome` variant names are still provisional;
  a short name shared by both must be resolved before they are implemented.
- Initial integers are `i8/i16/i32/i64` and `u8/u16/u32/u64`; floats are `f32`
  and `f64`. Unconstrained integer literals default to `i32`, floats to `f64`.
  Wider integers, SIMD, and target-width integer types are deferred.
- Integer overflow is consistent across build modes: statically proven overflow
  is rejected; dynamic overflow is a controlled execution error. Wrapping,
  saturating, and checked arithmetic are explicit alternatives. Integer division
  errors remain checked.
- Floating-point operations follow IEEE behavior, including NaN and infinities.
  Protocol libraries can impose stricter finite-value requirements.
- Strings are UTF-8. Byte length and Unicode scalar iteration are separate APIs;
  integer indexing is unsupported. Initial interpolation accepts identifiers
  only, reads without consuming, and formats basic types only. String literals
  appear as owned `String`; storage may be optimized without changing semantics.
- Property/getter/setter systems, static storage, tasks, and parallel execution
  are deferred. The host/task boundary needs a separate design. Properties are
  not ordinary field syntax. Extension definitions are also not yet specified;
  initial extension targets, if adopted, are limited to same-package types.

## Repetition and implementation order

- Array repetition `[expression; N]` evaluates the expression separately for
  every element, in order. `[make_value(); 3]` calls three times. It does not
  implicitly clone an owned value; repeating an owned binding requires explicit
  copies and repeated moves are errors.
- Build the foundation in stages: workspace/project model and diagnostics;
  lexer/parser and syntax diagnostics; name resolution and type checking;
  typed IR with initial move checking; Wasm generation and validation; full
  ownership/borrow analysis and lowering; runtime and core collections; libraries; A* and ENF validation;
  optimization after behavior and measurements are established.
- A* grid helpers and a small ENF lexer/parser are staged language consumers.
  Full protocol conformance and ABI compatibility follow only after the core.

## Expression and control-flow contracts

- A trailing expression without a semicolon supplies a block/function result;
  explicit return supports early exit. Unit-returning functions may omit `-> ()`.
- Evaluate call arguments and ordinary binary operands left to right. Boolean
  `&&` and `||` short-circuit. Optimization preserves observable evaluation order.
- Element assignment `a[i] = value` evaluates the base and every index operand
  left to right, then the right-hand side, and performs the bounds checks
  immediately before the store. A dynamic out-of-range index therefore fails
  after the right-hand side's effects. Rationale: checking before the right-hand
  side would hold exclusive access to the element while it is evaluated and
  reject ordinary code such as `a[i] = a[j] + 1`; operand order still follows
  the left-to-right rule. Java orders array stores the same way. Compound
  assignment reads the element, evaluates the right-hand side, then stores.
- Owned matching consumes the scrutinee and transfers selected payloads. Matching
  a read-only borrow produces borrowed payload bindings. Mutable matching is deferred.
- Function parameters cannot override access modes at the call site; share
  parameters mutate their targets but are not rebound to another target.
- Struct fields default to module-private. External construction must not bypass
  private fields; every field must be initialized explicitly.
- Whole-value destructuring uses `let Type { field, field: alias } := value;`,
  or `var` for mutable bindings. Initial patterns name all accessible fields;
  implicit partial field moves and nested/omitting destructuring are deferred.
- Default source-root configuration is `[package].src = "./src"`; manifest
  override is resolved relative to the invoking directory.
