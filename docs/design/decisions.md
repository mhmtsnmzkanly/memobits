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
- Owned assignment and owned function parameters transfer ownership of
  aggregate values: arrays, field-based types, enums, and later collections and
  strings. Primitive values (integers, floats, `Bool`) are copied implicitly:
  binding, assigning, passing, or returning one leaves the source usable, and a
  primitive element or field may be read into an owned position. Moving a
  primitive protects no resource, and arithmetic already read its operands
  without consuming them, so requiring explicit copies only added noise. Wrap a
  primitive in a field-based type when it must not be duplicated.
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
- Copying an aggregate is explicit and available only for copyable types.
  Copy-on-write may provide independent value semantics for suitable
  collections; it is distinct from `share`. The spelling is `expr.copy()`; it
  only reads its receiver and yields a fresh owned value. It is also accepted on
  primitives, where it is never required. Aggregate copy and copy-on-write are
  not implemented yet.
- Collections are homogeneous. `Array<T, N>` has fixed length; `List<T>` is
  dynamic. `let` prevents element mutation. Indexing checks bounds; proven bad
  constant indices are compile errors, dynamic failures are controlled runtime
  errors. `get` expresses absence as `Option`. Extracting an aggregate
  element into an owned binding requires explicit borrow/share/copy/removal;
  primitive elements are copied implicitly. Removal transfers
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
  `Option<T>`, `Result<T, E>`, and the three-state `Attempt<T, E>`. They share
  one category with `Array`: the compiler instantiates them per use.
  User-defined generic types are not available now, but the door stays open:
  `<...>` after a type name is reserved for type arguments, and compiler-known
  types are instantiated through a general mechanism rather than per-type
  special cases, so user declarations can adopt it later without a redesign.
- The three-state result is `Attempt<T, E>` with variants `Done(T)`, `Skipped`,
  and `Failed(E)`. `Result<T, E>` has `Ok(T)` and `Err(E)`; `Option<T>` has
  `Some(T)` and `None`. No short variant name is shared between them.
- Errors form a hierarchy rooted in the compiler-known type `Error`, which the
  host understands. `Error` has the public fields `code: u32`, a
  program-defined numeric code, and `message: String`, which joins it when
  strings are implemented. The compiler also records the concrete error type's
  identity in every error value; programs do not write it, and the host uses it
  to name the error type from artifact metadata.
- An error type derives from `Error` or from another error type with
  `type ParseError: Error { line: u32 }`. Derivation exists only inside this
  hierarchy; it is not general inheritance. A derived type contains its
  ancestors' fields first, in order, followed by its own. Ancestor fields are
  accessed directly (`e.code`) and initialized explicitly in a literal like any
  other field.
- A borrow or share of an error is accepted wherever a borrow or share of one
  of its ancestors is expected. The current compiler implements this for
  direct internal call arguments, including reborrows. An owned error converts
  to an ancestor type only explicitly; the conversion drops the derived fields
  and keeps the recorded concrete identity. Its spelling is not designed yet.
- The error parameter `E` of `Result<T, E>` and `Attempt<T, E>` must be `Error`
  or a type derived from it. There are no separate standard error types per
  result type; simple programs use `Error` directly. An entry function may
  return `Result` or `Attempt`; the host reports a returned error through its
  `Error` part. The [current entry adapter](outcome-implementation.md)
  supports primitive success payloads. The host reports guest traps separately.
- Empty field-based types (`type Unit {}`) are allowed. Empty enums
  (`type Never []`) are rejected.
- The prelude exposes the variants of `Option`, `Result`, and `Attempt` by short
  name. Variants of user enums are written `Type::Variant`.
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
  implicitly clone an owned aggregate; repeating an aggregate binding requires
  explicit copies and repeated moves are errors. Primitive values repeat freely.
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
  A scrutinee that cannot be moved (a `borrow`/`share` parameter or reference
  binding, a field `l.shape`, an element `a[i]`, nested places) is matched in
  place and consumes nothing: a primitive payload binding is copied into a
  plain value, an aggregate payload binding is a read-only `borrow` of its
  slot that lives as long as it is used and that can be passed on, indexed and
  field-read but not moved out or written. Matching through a `share` gives
  read-only bindings too. Owned scrutinees (owned locals, temporaries, owned
  parameters) keep consuming semantics.
- Function parameters cannot override access modes at the call site; share
  parameters mutate their targets but are not rebound to another target.
- Struct fields default to module-private. Outside its defining module a
  private field cannot be read, written, named in a struct literal, or
  destructured, so a type with a private field cannot be constructed
  externally. A `pub` field is readable externally and writable through a `var`
  owner or a `share`. Every field must be initialized explicitly. Closing reads
  as well as writes lets a module keep invariants and change its representation.
- A struct literal `Name { field: value }` may not appear directly in an `if`
  condition, where `{` would be ambiguous with the block; parenthesize it.
- `match` arms are separated by commas; the comma is optional after an arm whose
  body is a block.
- A struct literal may not appear directly as a `match` scrutinee either. An arm
  that is not exhaustive is an error naming the missing variants. A duplicate
  variant arm, an arm after a `_` arm, and a `_` arm after every variant is
  already matched are errors (unreachable arms), not warnings. `return`,
  `break` and `continue` may be written directly as an arm body.
- Whole-value destructuring uses `let Type { field, field: alias } := value;`,
  or `var` for mutable bindings. Initial patterns name all accessible fields;
  implicit partial field moves and nested/omitting destructuring are deferred.
- Default source-root configuration is `[package].src = "./src"`; manifest
  override is resolved relative to the invoking directory.

## Memory layout and limits

- Aggregate values are addressed storage. Whether a value lives on the stack or
  the heap is a backend decision that the language rules, typed IR, and
  ownership analysis do not observe, so storage placement can change later
  without affecting programs.
- Linear memory is ordered: reserved low addresses, the stack, static data, then
  the heap. The stack sits below the heap so that exhausting it fails with a
  controlled error instead of overwriting heap data. The heap is introduced
  with dynamic collections and strings and grows at the end.
- The stack size is a build setting, `[build].stack_size` in bytes, with a
  default of 1 MiB. There is no separate per-function frame limit: a frame that
  cannot fit in the configured stack is a compile error, and dynamic exhaustion
  is a controlled runtime error.
- Enum tags use the smallest unsigned integer width that fits the variant
  count. Tag width and field layout are not a stable ABI.
