# Accepted Design Decisions

This document records accepted language and project direction, including the
dated decisions and implementation checkpoints below. It is not the status
catalog: for shipped behavior and current limits, use the
[roadmap](../roadmap.md). Older sections are retained as decision history;
later dated checkpoints supersede earlier wording when they conflict. Syntax
examples are normative only where explicitly stated; unresolved API spellings
remain proposals.

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
  `type Name [ variants... ]` for enums, `type Name;` for a bodyless nominal,
  and `type Name = Other;` for aliases. A bodyless nominal is distinct from an
  empty struct and cannot be constructed as a value in the current slice.
- Non-generic nominal types can attach inherent methods with a trailing
  `extend { ... }` block, or declare them in `extend Type { ... }`. Calls use
  `value.method(...)`; public methods become available across a direct module
  import. Trailing inherent extensions on generic types remain gated.
- **Superseded spellings (2026-11-23):** the type spellings in this file are
  being migrated per "Built-in type spelling" at the end of this document:
  `bool`, `char`, `array<T, N>`, `T?`, `T ! E`, `T ?! E`; `Option<…>`,
  `Result<…>`, `Attempt<…>`, `Bool`, `Char`, `Array<…>` are rejected and
  `Bytes` no longer exists. Where text below conflicts, that section wins.
- Compiler-known types include `Array<T, N>`, `Bytes<N>`, `List<T>`,
  `Option<T>`, `Result<T, E>`, and the three-state `Attempt<T, E>`. User
  nominal structs and enums also accept concrete type parameters; `u32` const
  parameters are supported for admitted fixed-array shapes. Generic enum
  variants are constructed and matched using the expected concrete enum type.
  Generic functions support one direct owned `T` parameter constrained by one
  interface bound, with explicit method selection and caller-visible unique
  evidence forwarded through nested generic calls. Other constraint shapes,
  borrowed parameters, and generic const-plus-evidence combinations remain
  gated while G1 continues.
- `Array<T, N>` remains in the portable core. `Bytes<N>` is a compatibility
  alias for `Array<u8, N>` outside the target core; existing `Bytes` sources
  remain accepted during migration.
- A postfix `T?` is shorthand for `Option<T>`. Grouped `(borrow T)?` parses as
  `Option<borrow T>`, while `borrow T?` keeps the borrow outside the optional
  type. This does not expand the current reference transport subset.
- The three-state result is `Attempt<T, E>` with variants `Done(T)`, `Skipped`,
  and `Failed(E)`. `Result<T, E>` has `Ok(T)` and `Err(E)`; `Option<T>` has
  `Some(T)` and `None`. No short variant name is shared between them.
- Errors form a hierarchy rooted in the compiler-known type `Error`, which the
  host understands. `Error` has the public fields `code: u32`, a
  program-defined numeric code, and `message: string`, which joins it when
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
- `Char` is a distinct Unicode scalar type. Single-quoted literals contain
  exactly one scalar; `\\n`, `\\r`, `\\t`, `\\0`, `\\\\`, and `\\'` escapes are
  accepted. Its current Wasm representation is an unsigned 32-bit scalar code
  point; only equality is supported in this slice.
- Tuples preserve positional type identity and order. `(value)` remains
  grouping; `(value,)` and `(first, second)` construct tuples, with `.0`/`.1`
  projections. Positional initializers evaluate in written order and store by
  tuple position. Labels are occurrence-local projection aliases: each labeled
  type or value maps its own names to tuple slots, while structural identity
  remains the ordered element types. Labeled initializers evaluate in written
  order and store by mapped slot. Internal tuple arguments/results and local
  tuples with owned String fields are supported. Named local tuples with direct
  String fields can move through internal owned parameters and results; Wasm
  transfers their cleanup with the tuple. A temporary tuple with direct String
  fields can also move directly into an owned internal call; lowering stages it
  in a cleanup-tracked local before transfer. Nominal String-owning struct
  transport retains its separate gate. Positional tuple destructuring binds every slot
  from a named owned tuple local and transfers direct String fields to their
  new local owners, clearing source tuple descriptors before scope cleanup.
  Nested positional patterns and wildcard slots consume their complete tuple
  shape; wildcard-owned Strings use normal local cleanup. Nested tuple elements
  that own Strings transfer recursively through construction and internal
  signatures, with exact descriptor clearing at each move. Local nominal
  records can contain String-owning tuple fields and clean them recursively.
  By-value nominal String-owner transport, String-owning tuple placement in
  arrays/enums, other owner placements, destructuring aliases, and partial
  destructuring remain open pending the full D2 scope.
- Strings are UTF-8. The only source type spelling is lowercase `string`.
  Byte length and Unicode scalar traversal are separate operations: `.len()`
  counts UTF-8 bytes, and `.scalar_at(offset)` reads at a byte offset. A source
  loop can advance across valid scalars by their UTF-8 widths; this does not
  promise an iterator API.
  Integer indexing is unsupported. Initial interpolation accepts identifiers
  only, reads without consuming, and formats basic types only. String literals
  appear as owned `String`; storage may be optimized without changing semantics.
- Property/getter/setter systems, static storage, tasks, and parallel execution
  are deferred. The host/task boundary needs a separate design. Properties are
  not ordinary field syntax. The implemented I1 extension slice selects a
  method explicitly with postfix `of`, and activates public extensions only
  from a direct module import. See the [runnable multi-module example](../../examples/topics/module-imports/README.md).
  Loading independent packages and cross-package extension identity remain
  outside the current implementation.
- User-defined `+` selects the compiler-provided `core::ops::Add` interface.
  Add declares associated `Rhs` and `Output` types, bound by an implementation
  with `type Rhs = T;` and `type Output = U;`. The selected method takes owned
  operands and returns its declared output. A constrained `T: Add` function
  may use `T::Rhs` and `T::Output` in its signature; specialization resolves
  these projections through the uniquely selected, forwarded evidence. A local
  interface named `Add` does not affect operator selection. Primitive numeric
  `+` remains checked and built in; broader operator families remain gated.
- User-defined `-` selects the compiler-provided `core::ops::Sub` interface.
  It follows the same owned `Rhs`/`Output` and constrained evidence-forwarding
  contract as `Add`. Primitive numeric subtraction remains checked and built in.
- User-defined `*` selects the compiler-provided `core::ops::Mul` interface.
  It follows the same owned `Rhs`/`Output` and constrained evidence-forwarding
  contract as `Add` and `Sub`. Primitive numeric multiplication remains checked
  and built in.
- User-defined `/` and `%` select the compiler-provided `core::ops::Div` and
  `core::ops::Rem` interfaces for nominal operands. Both follow the same owned
  `Rhs`/`Output` and constrained evidence-forwarding contract. Primitive
  numeric division and remainder retain their built-in checked semantics.
- User-defined `&` selects the compiler-provided `core::ops::BitAnd` interface
  for nominal operands. It uses the same owned `Rhs`/`Output` and constrained
  evidence-forwarding contract. Primitive `u32 & u32` keeps its existing
  per-bit semantics. User-defined `|` selects `core::ops::BitOr` for nominal
  operands with the same contract; primitive `u32 | u32` keeps its per-bit
  semantics. User-defined `^` selects `core::ops::BitXor` for nominal operands
  with the same contract; primitive `u32 ^ u32` keeps its per-bit semantics.
  Nominal equality and inequality select `core::ops::PartialEq`; the borrowed
  left receiver stays available and the right operand follows owned argument
  rules. `!=` negates the selected equality result. Nominal ordering selects
  `core::ops::PartialOrd` by operator and calls its matching `lt`, `le`, `gt`,
  or `ge` method directly. Each method borrows the left receiver, takes an
  owned associated `Rhs`, and returns `Bool`; ordering is never inferred from
  equality. Primitive equality and ordering remain built in. Nominal `+=`
  selects `core::ops::AddAssign` with `share self`, an owned associated `Rhs`,
  and implicit `Unit` result. It captures the writable target once, evaluates
  the RHS before invoking the method, and preserves primitive checked `+=`.
  Early-return tests for indexed and field-projected targets prove the method is
  skipped; they do not establish separate frame or allocation-cleanup guarantees.
  Nominal `-=` selects `core::ops::SubAssign` under the same receiver, RHS,
  target capture, and evaluation-order contract; primitive checked `-=` remains
  built in. Nominal `*=` selects `core::ops::MulAssign` with `share self`, an
  owned associated `Rhs`, and implicit `Unit` result. It preserves the same
  single place capture and RHS-before-method sequencing; primitive checked `*=`
  stays built in. Nominal `/=` selects `core::ops::DivAssign` under the same
  receiver, owned `Rhs`, single place capture, and RHS-before-method sequencing
  contract; primitive checked `/=` stays built in. Nominal `%=` selects
  `core::ops::RemAssign` under the same receiver, owned `Rhs`, single place capture,
  and RHS-before-method sequencing contract; primitive checked `%=` stays built in. Nominal `&=` selects `core::ops::BitAndAssign` with the same shared receiver, owned associated `Rhs`, single place capture, and RHS-before-method sequencing; primitive `u32 &= u32` follows existing per-bit `&` semantics. Nominal `|=` selects `core::ops::BitOrAssign` with the same shared receiver, owned associated `Rhs`, single place capture, and RHS-before-method sequencing; primitive `u32 |= u32` follows existing per-bit `|` semantics. Nominal `^=` selects `core::ops::BitXorAssign` with the same shared receiver, owned associated `Rhs`, single place capture, and RHS-before-method sequencing; primitive `u32 ^= u32` follows existing per-bit `^` semantics. Nominal `<<=` selects `core::ops::ShlAssign` with the same shared receiver, owned associated `Rhs`, single place capture, and RHS-before-method sequencing; primitive `u32 <<=` keeps checked shift-count behavior. Nominal `>>=` selects `core::ops::ShrAssign` with the same shared receiver, owned associated `Rhs`, single place capture, and RHS-before-method sequencing; primitive `u32 >>=` keeps checked shift-count behavior. All concrete nominal compound assignment families are enabled; generic constrained compound
  selection is supported for owned generic parameters whose selected interface
  evidence is caller-forwarded; `AddAssign`, `SubAssign`, `MulAssign`, `ShrAssign`, and `DivAssign` have
  source/Wasm proof, including distinct associated `Rhs`, missing/wrong-evidence
  rejection, and owned RHS consumption. Generic
  projected/indexed targets and remaining nominal compound operators stay gated.
  Selected indexed compounds defer dynamic bounds validation until RHS completes
  while preserving an exclusive loan on the nearest owner. Literal indices keep
  checked place capture before RHS because invalid constants are compile-time
  errors. Dynamic-index loans conservatively cover the nearest array owner while
  RHS executes, so uncertain accesses into that owner remain overlapping.
- User-defined `<<` selects the compiler-provided `core::ops::Shl` interface
  for nominal operands. It follows the same owned `Rhs`/`Output` and
  constrained evidence-forwarding contract. Primitive `u32 << u32` keeps its
  built-in behavior, with counts at or above 32 rejected statically or trapped
  dynamically.
- User-defined `>>` selects the compiler-provided `core::ops::Shr` interface
  for nominal operands, with the same owned `Rhs`/`Output` and constrained
  evidence-forwarding contract. Primitive `u32 >> u32` remains a built-in
  zero-filling shift with counts at or above 32 rejected statically or trapped
  dynamically.
- User-defined unary `-` selects compiler-provided `core::ops::Neg` for
  nominal operands. `Neg` has an associated `Output` and an owned `neg(self)`
  method; constrained generic evidence is forwarded to the selected method.
  Primitive numeric negation remains built in, including signed-minimum
  literal handling and checked runtime overflow.

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

## Ownership direction after the D2 aggregate work (2026-11-23)

- **Composition is allowed by default.** String-owning values may be composed
  into any aggregate placement (struct field, tuple element, fixed-array
  element, enum payload, nesting of these) once the type-directed ownership
  facts and cleanup cover that placement. A single shared predicate decides
  which String-owning aggregates may be transported; per-shape gates are
  temporary and are removed as each placement gains source/Wasm, capped-memory
  and negative evidence. Only compositions that cannot be proven sound stay
  rejected, each with a specific diagnostic and test.
- **References stay second-class.** References are parameter and local-loan
  forms only: no reference-returning functions, no references stored in
  struct, tuple, array or enum storage, and no named lifetime parameters.
  Data moves by value; `borrow`/`share` parameters and local loans provide
  access. This is a direction for future work, not a change to shipped
  behavior.
- **No implicit partial moves.** Moving a value out of a field, element or
  payload of a live owner stays rejected. The intended explicit forms are a
  place replacement that returns the old value (spelling open, e.g.
  `replace(place, new_value)`) and a same-type `swap` of two disjoint places;
  neither needs a default value or leaves a hole in the owner. Whole-owner
  destructuring and consuming `match` of a whole owner remain supported.
- **Fixed-array spelling.** `Array<T, N>` is the target spelling, consistent
  with `List<T>`, `Option<T>` and other applied types. The earlier
  `array(T; N)` proposal is withdrawn. `Bytes<N>` remains a compatibility
  alias outside the target core.
- **Anonymous records use the same ownership predicate.** String-owning
  anonymous records are admitted through the shared transport predicate
  together with nominal structs, not through a separate gate.

## Optional spelling (2026-11-23, user decision)

- `T?` is the preferred source spelling for optional types and is shorthand
  for `Option<T>`. The `Option<T>` spelling stays accepted with identical
  meaning and reports no warning (user decision; the earlier MW001 migration
  warning was removed). D3's legacy migration-diagnostic clause is waived by
  this decision.
- The compiler keeps a non-failing warning channel: warnings are printed with
  code and span on `check`, `build` and `run`, never change the exit status
  of an otherwise successful command, and never suppress errors. MW001 and
  MW002 are unused and reserved.
- Maintained guide sources use `T?`.

## Text traversal and spelling migration (2026-11-23)

- Scalar traversal reuses the existing collection loop: `loop ch in text`
  over a borrowed or named `string` visits Unicode scalars in order and binds
  each as an immutable `Char`. `.len()` remains the byte length. The loop
  borrows the text for its duration, like other collection loops. No general
  iterator protocol is introduced by this decision.
- `Bytes<N>` stays accepted as a compatibility alias of `Array<u8, N>` and
  reports migration warning MW003 on the non-failing channel. Maintained guide
  and fixture sources migrate; protected example directories are left
  unchanged.
- `String` is NOT a compatibility spelling: the earlier accepted decision
  "The only source type spelling is lowercase `string`" stands, and bare
  `String` stays rejected with TE001 and its migration guidance. (Corrected
  2026-11-23: an architect note briefly listed `String` as accepted with a
  warning; that contradicted the committed decision and was reverted.)

### Shipped C1 receiver rules (2026-11-23)

- `loop ch in text` accepts a named `string` local or a borrowed parameter
  (a single-segment path), like the primitive List loop. Fields, call results,
  literals and `concat` temporaries are rejected with TE017. The text is
  borrowed for the whole loop, so mutating, replacing, moving or dropping it
  inside the body is rejected by the existing loan checks (BE005). The binding
  is an immutable `Char`; `Char` supports equality only.
- Decoding happens in generated code: the loop keeps a byte offset, reads the
  scalar at the offset and advances by the lead byte's UTF-8 width, using the
  internal `StringScalarRead` instruction. No allocator or runtime change.
- MW003 reports on the bare `Bytes<N>` spelling. Bare `String` remains a
  TE001 error with migration guidance; MW002 is not used.

## Source-level tests (accepted direction, 2026-11-23)

- The language will gain a source-level test mechanism so that checked
  examples need no hand-numbered error codes: test functions (proposed
  spelling `test fn name() { ... }`), a built-in `assert(condition)`, and an
  `mb test` command that runs each test in source and standalone Wasm and
  reports failures by test name.
- Open details to settle before implementation: exact spelling, whether a
  failed `assert` traps (discarding the instance, per the trap contract) or
  returns a reported failure, test discovery and filtering, and whether test
  functions are excluded from normal builds.
- Shipped (T1/T2): the runnable guide and the examples now check their facts
  with `test fn` and `assert`; the old module-ranged check codes are gone.

## Built-in type spelling (2026-11-23, user decision)

This section supersedes earlier spelling statements in this file, including
"Optional spelling", "Fixed-array spelling" and the `Bytes<N>` notes.

- Built-in value types are lowercase: integers and floats (unchanged),
  `bool`, `char`, `string`, and the fixed array `array<T, N>` (a built-in
  feature of the core). User types and `Error` keep their declared names.
- Optional, fallible and three-state results are type operators, not named
  types:
  - `T?` — a value that may be absent; variants `Some(T)` and `None`.
  - `T ! E` — a value or an error; variants `Ok(T)` and `Err(E)`. `E` must be
    `Error` or derived from it. Example: `fn main() -> i32 ! Error`.
  - `T ?! E` — exactly the same type as `T? ! E` (a fallible operation whose
    success may carry no value). There is no separate `Attempt` type, and
    `Done`, `Skipped` and `Failed` are removed entirely (no aliases): values
    are built and matched as `Ok(Some(v))`, `Ok(None)` and `Err(e)` using
    nested patterns.
  - `?` binds tighter than `!`: `u32? ! E` is `(u32?) ! E`; parentheses group
    explicitly, e.g. `(u32 ! E)?`, `(borrow T)?` and `T ! (borrow E)`.
    Grouping is syntax only; it does not widen reference transport gates.
- Removed spellings are compile errors (TE001) with guidance naming the
  replacement: `Option<T>` → `T?`, `Result<T, E>` → `T ! E`,
  `Attempt<T, E>` → `T ?! E`, `Bool` → `bool`, `Char` → `char`,
  `Array<T, N>` → `array<T, N>`. There is no warning period.
- `Bytes` is removed entirely, as if it never existed: no alias and no special
  diagnostic (an ordinary unknown-type error). Byte buffers are
  `array<u8, N>`. Migration warnings MW001–MW003 are unused; the non-failing
  warning channel remains available for future use.
- `List<T>` is unchanged for now; its name and model are decided with the
  general collection work.
- Diagnostics and host-visible type names use the new spellings.

## Nested patterns (2026-11-23, user decision)

- `match` arms accept nested constructor patterns at any depth: enum and
  optional/fallible variants (`Ok(Some(v))`, `Ok(None)`, `Err(e)`,
  `Shape::Pair(Point::Origin, other)`), tuple patterns inside payloads and
  arms, `_` wildcards and binding names in any position.
- Exhaustiveness and unreachable-arm checks cover nested patterns; missing
  cases are reported with an example of an uncovered pattern.
- Ownership follows the existing match rules: an owned match consumes the
  whole scrutinee, moves bound payloads into the arm and releases unbound
  owned parts exactly once; an in-place (borrowed) match copies primitive
  payloads and lends aggregate payloads read-only. No partial moves out of a
  live owner are introduced.
- Literal patterns, or-patterns and guards followed in G7 (see "Shipped G7
  details"); pattern bindings with `@` remain open.

## Platform layers and memory model (2026-11-24, user decision)

- The library surface is layered like Rust's core/alloc/std:
  - **core** — always available, needs no heap: primitives, `bool`, `char`,
    `array<T, N>`, `T?`, `T ! E`, tuples, records, enums, interfaces,
    `core::ops`, string literals and read-only string operations.
  - **alloc** — available when the build includes the guest allocator:
    `List<T>` (imported as `use alloc::List;`, a Rust-owned virtual module like
    `core::ops`), heap-producing string operations (`concat`, `push_str`,
    `to_utf8_string`, …) and, later, `Box<T>`.
  - **platform** — host capabilities selected by `[host] profile`.
- `List<T>` is a library type, so it keeps a capitalized name; built-in
  language features are lowercase. Its first implementation stays in the
  compiler (Rust intrinsics); a self-hosted Memobits implementation is a later,
  separate consideration (needs allocator interface, drop, `Index`, iteration).
- A future allocator-free profile (working name `core-only`) omits the
  allocator and heap; using `alloc` there is a compile error.
- Memory model is kept: one Wasm linear memory holding reserved space, a
  shadow stack for fixed-size scope-bound values, static data, and a heap only
  for dynamically sized values. Research items (no behavior change): scalar
  replacement of small aggregates into Wasm locals, and multi-memory to
  isolate stack from heap (verify engine support first).

## Source-level tests, assert, replace/swap (2026-11-24, user decision)

- Test functions are top-level items `test fn name() { ... }`: no parameters,
  Unit result, normal module visibility (a test may call private items of its
  own module). They are type-checked by `check`, `build` and `test`, but are
  excluded from normal `build`/`run` artifacts.
- `assert(condition)` takes a `bool`. A false condition is a controlled trap
  ("assertion failed") with source location, discarding the instance like
  every other trap. It is usable in ordinary code as well. As with `drop`, an
  in-scope function, import or value named `assert` takes precedence.
- `mb test` compiles the project's tests, runs each test in a fresh instance,
  reports each test by qualified name (`ok` / `FAILED` with trap reason and
  location), prints a summary and exits non-zero if any test fails. A filter
  argument selects tests by substring. A test artifact can be built and run
  standalone for source/Wasm parity.
- `replace(place, value)` returns the old value of an owned place and installs
  the new one; `swap(a, b)` exchanges two disjoint places of the same type.
  Both are built-in functions whose first arguments are places (fields,
  elements, locals), consistent with `drop(value)`. Details are designed with
  the general owned-element work.

### Shipped T1 details (2026-11-24)

- Syntax: `test` is a contextual word (`test` directly before `fn` at item
  start). Shape errors are syntax errors (SE002): `pub`, parameters, a
  non-`Unit` result and generic parameters are rejected. Test names share the
  module namespace (a clash is ME005) and are never callable.
- Reachability: normal `resolve` targets drop test items, so tests never load
  modules, change artifacts, or appear in exports. `Target::Test` loads every
  project module with its tests. Check scope (architect rule, shipped T2):
  `mb check` always checks every project module and every test (the
  whole-project check); `mb build` and `mb run` check only the modules
  reachable from the application or library roots and ignore tests.
- `assert(condition)` lowers to the IR instruction `Assert`; the Wasm backend
  traps with reason code 12 ("assertion failed") at the call's source
  location (`memobits.traps` metadata).
- Test artifact: a library-style module exporting each test as
  `test::<module>::<name>`. `mb test` runs the exports in qualified-name order,
  one fresh instance each; source and standalone runs print identical reports.

## Alloc layer switch (2026-11-24, architect under the platform-layer decision)

- `[build] alloc = true|false` in `project.toml` (default `true`) selects
  whether the guest allocator and heap are part of the build. It is
  independent of `[host] profile`.
- `List<T>` lives in the Rust-owned virtual module `alloc` and must be
  imported: `use alloc::List;`. Using `List` without the import is an
  unknown-type error whose note names the import.
- With `alloc = false`: importing from `alloc` and heap-producing string
  operations (`concat`, `push_str`, `to_utf8_string`, …) are compile errors
  that name the `[build] alloc` setting; string literals and read-only string
  operations remain available; the emitted module contains no allocator code.

### Shipped A1 details (2026-11-24)

- `alloc` is a Rust-owned virtual module (declares `pub type List;` only so
  imports validate; it is removed from the resolution afterwards). Accepted
  forms: `use alloc::List;`, `use alloc::{List};`, and `use alloc;` with
  `alloc::List<T>` in types. Aliasing (`use alloc::List as X;`) is not
  supported. A project module named `alloc` is ME011.
- Missing import: NE003 `unknown type 'List'` with the note ``add `use alloc::List;` to use List``.
  The applied `List<T>` stays reserved (as `array<T, N>` and `Error`); a
  module that does not import it may still declare a bare user type `List`.
- `[build] alloc = false`: `alloc` imports are ME012; `concat`, `push_str`
  and `to_utf8_string` are TE033, both naming `[build] alloc`. The Wasm
  backend already emits the allocator only when a heap operation is
  reachable, so the artifact has no allocator functions, no `memory.grow` and
  `memory.maximum == memory.minimum` (checked in
  `crates/memobits-cli/tests/alloc_layer.rs`). Example:
  `examples/topics/core-only`.
- Standalone single-file commands (`mb analyze FILE`, `mb ownership FILE`)
  accept `use alloc...` but do not enforce the import requirement (they have no
  module resolver).

## Owned elements in collections (2026-11-24, architect, from accepted principles)

Derived from "composition allowed by default", "references stay second-class"
and "no implicit partial moves"; no new user-facing principle.
- `List<T>` and `array<T, N>` accept any admitted element type, including
  `string` and String-owning aggregates. (`List<T>` is no longer limited to
  `u8`/`u32`; the old "unchanged for now" note in "Built-in type spelling"
  is superseded.)
- Non-empty list literals use the existing contextual form: with an expected
  `List<T>`, `[a, b, c]` builds a list (as `[]` already builds an empty one);
  elements evaluate once in written order and move in.
- `items[i]` on a list is a place, like array indexing: bounds-checked
  (controlled trap), copyable elements read by copy, non-copyable elements
  usable only in place — as `borrow`/`share` receiver or argument, in an
  in-place `match`, or through a projection (`items[i].name.len()`). Moving
  an element out of a live collection is rejected (partial move); use
  `pop()`, `replace(items[i], v)` or `swap(...)` instead. `get(i) -> T?`
  stays available only for copyable `T`.
- A live loan of an element blocks operations that may move or reallocate
  storage (`push`, `pop`, `clear`, replacement) — enforced by the existing
  loan checker at owner granularity.
- `loop x in items` binds copies for copyable elements and read-only loans
  for non-copyable elements, for the duration of each iteration. Consuming
  iteration is not part of this step.
- Element-borrow limits recorded during D2 (`grid[i][j].borrow()`,
  `bag.items[0].borrow()`, `d.title.size()`) are lifted under these rules.

### Shipped E1 and R1 details (2026-11-24)

Facts about the shipped behavior; no new decisions.

- E1a/E1b: `array<T, N>` and `List<T>` hold any admitted element type
  (primitives of every width, `bool`, `char`, `string`, owner structs, tuples,
  enums, arrays). Element cleanup is type-directed: scope exit, `clear`,
  reassignment, `drop` and early returns release each owned element once. A
  List grows by doubling and moves elements bitwise; `pop` moves an owner into
  the `T?` payload. `get`, `contains` and `index_of` stay primitive-only
  (`get` on other elements is TE022 pointing at `items[i]`, the searches are
  TE017). Nested `List<List<T>>` was TE017 here and is lifted by G1 (below);
  reference elements stay TE017. Live element loans block `push`, `pop`,
  `clear`, moves and reassignment (BE005).
- R1 `replace(place, value) -> T`: a built-in; an in-scope function, import or
  value named `replace` (or `swap`) takes precedence. The first argument is a
  place: a `var` local or `share` parameter, or a field, array element or List
  element at any depth, whose owner is a `var` or a `share` parameter.
  Evaluation order: the place path (indices) once, then `value` into a hidden
  owner local, then the checked address (bounds trap RE007), then a bitwise
  exchange; the old value is the result and is not released. A read of the old
  value in `value` is fine because its loans end before the exchange. An early
  `return` while evaluating `value` leaves the place untouched and releases the
  staged values.
- R1 `swap(a, b)`: two places of the same type; the exchange is bitwise (no
  heap data is copied or released). Overlap is decided by the loan checker:
  the same local, the same constant element, or dynamic indices into one
  collection are BE005 (conservative). A runtime-equal-index check is a
  possible later extension.
- R1 owning overwrite: `items[i] = v` and `x.field = v` on String, List and
  String-owning aggregate places lower to the same RHS-first exchange, then
  release the old value exactly once. Errors: TE002 type mismatch, TE004
  immutable owner, TE006 non-place first argument, TE007 `swap` type
  mismatch, BE005 overlapping or live loans.
- `loop x in array` over non-copyable array elements binds read-only borrows,
  as for a List; mutating the array inside the loop is BE005.
- Known limits: `concat` as a replacement value is accepted for `string`
  places. (The earlier limit on `if`/`match` replacement values is lifted by
  D1, below.)
- D1 (2026-11-24), facts only: the three mirrored String-owner predicates are
  one rule in `memobits-ir` (`is_nominal_string_owner` over an
  `OwnerTypeModel` adapter; analysis `lower.rs` and `types.rs` only classify
  their own type representation). An ignored match payload is marked by
  `LocalKind::DiscardedMatchPayload` on the IR local instead of a name.
  Widened behavior: (a) an owner temporary (struct or record literal, direct
  call result, array literal) passed to an owned parameter is staged in a
  hidden local like tuple and array elements; (b) `replace(place, value)`
  accepts an `if` / `else if` / `match` expression (blocks as branches) of
  `string`, `List` or String-owning aggregates as `value`: each branch moves
  its value into the hidden replacement local before the join, so no heap
  value crosses a join; (c) a struct literal may mix a String field with
  owner-struct and owner-array fields. Error-derived types that own heap
  Strings, directly or nested, report LE900 "Error-derived type 'T' cannot own
  heap Strings yet". A BE005 on `swap(a, b)` between two projected places adds
  a note that swap needs two disjoint places. `Resolution::ignored_tests` was
  removed (unread). (The two limits left open here, a struct literal as a
  function's tail expression and `if`/`match` owner values outside `replace`,
  are lifted by G1, below.)
- G1 (2026-11-24), facts only:
  - `if` / `else if` / `match` expressions (blocks as branches) of `string`,
    `List` or String-owning aggregates (structs, tuples, enums, arrays) work
    in every value position: binding, call argument, assignment RHS, function
    tail and `return` operand. `Builder::value_sink` is installed by the
    expression itself when no caller did (`take_value_sink` /
    `finish_value_sink` in analysis `lower.rs`): each branch moves its value
    into one hidden destination local before the join, so no heap value
    crosses a join. Branch inputs that were not chosen stay owned by their own
    locals and are released at their scopes; a moved-from source is cleared at
    run time, so release stays exact on both paths. A `return` inside a branch
    releases everything in scope, including the not-yet-initialized sink
    (which is registered for cleanup only after the join). Results of other
    types (primitives, borrows) still join through block parameters.
  - A struct literal (named or anonymous record) of a String-owning type may
    be a function's tail expression or `return` operand: `owned_result`
    stages the `StructNew` output in a hidden local first.
  - `List<List<T>>` (any admitted inner element type, e.g. `List<List<string>>`):
    `outer.push(inner)` moves the inner List in (bitwise descriptor); `outer[i]`
    is a List place, so `outer[i][j]` reads, `outer[i][j] = v`, and the List
    methods `push`, `pop`, `clear`, `len`, `get`, `contains`, `index_of`,
    `loop x in outer[i]`, `outer[i].borrow()` / `.share()`, `replace`, `swap`
    and `outer[i] = v` work through the element place. A mutating method on
    `outer[i]` evaluates the index path, then the pushed element, then forms a
    checked share address held in a hidden local that the List instruction
    targets; the root must be a `var` or `share` parameter (TE017 otherwise).
    `outer.pop()` yields `List<T>?` (the only Option with a List payload;
    `Some(list)` and user enums with List payloads stay gated by the List-move
    rule). Cleanup is type-directed: scope exit, `clear`, overwrite, `drop` and
    early returns release each inner List (elements, then block) exactly once;
    growth moves inner descriptors bitwise. Moving an inner List out of
    `outer[i]` stays TE022 (use `pop`, `replace` or `swap`); arrays of Lists and
    List fields in structs and tuples are lifted by F2 (below).

## Stage 3 ergonomics (2026-11-24, user approved architect defaults)

- `try … else` (direction LANG-07): `let n := try parse(s) else e { return Err(e); };`
  binds the `Err` payload to `e` in the handler, which must produce a value of
  the success type or exit. Without `else`, an `Err` is discarded (assignment
  context leaves the target unchanged). On `T?`, `try x else { … }` handles
  `None`. `try` is matching sugar: it does not catch traps.
- Ranges in loops: `loop i in 0..n` (half-open) and `loop i in 0..=n`
  (inclusive) over integer types, bounds evaluated once in written order.
  Ranges are not first-class values in this step.
- String interpolation (direction STR-06): `"x = {x}"` with identifiers only,
  read without moving, basic types (integers, floats, bool, char, string);
  `{{` and `}}` escape braces. It produces a heap string, so it belongs to the
  alloc layer.
- `const NAME: T = expr;` at module level, evaluated at compile time from
  literals, other constants and pure built-in operators; primitives and
  `string` literals only in this step.
- Numerics: `checked_*` arithmetic returns `T?`; `saturating_*` added;
  bitwise operators and shifts for all integer widths; signed `>>` is an
  arithmetic shift; shift counts keep the bounded-count rule.
- Patterns: literal patterns, or-patterns `A | B` (bindings must agree), and
  `if` guards; exhaustiveness treats guarded arms as non-covering.
- `~` bitwise complement for integers; `Self` names the extended type inside
  `extend` blocks.

### Shipped G3 details (2026-11-24)

- Syntax: `loop name in a..b` and `loop name in a..=b` are statements
  (`StatementKind::RangeLoop`); `..` and `..=` are lexer tokens. Each bound is a
  full expression (so `a + 1..b * 2` is `(a + 1)..(b * 2)`); a range is parsed
  only directly in the header. Anywhere else (`let r := 0..5`, `..5`, an
  argument, parentheses, a chain `0..3..5`) it is SE002 "a range ... is not a
  value". There is no `step` and no reverse range; `5..0` is empty.
- Typing: both bounds must have one integer type. An untyped integer literal
  bound takes the other bound's type (with two literals the type is `i32`);
  mismatched types are TE002, float, bool or other bounds are TE017 "range
  bounds must be integers". The loop variable is immutable (TE004 on
  assignment) and scoped to the body.
- Semantics: `a` then `b` are evaluated once, left to right, before the first
  iteration, even when the range is empty. A body that changes a variable used
  as a bound does not change the iteration. `a..b` runs while `cursor < b`;
  `a..=b` runs while `cursor <= b`; `break`, `continue`, early `return` and
  cleanup of body owners are those of other loops.
- Lowering: bounds and a cursor live in hidden locals. The cursor is copied into
  the loop variable and advanced before the body, so `continue` re-enters the
  header like a bare loop. Half-open advances with a checked `+ 1`, which
  cannot overflow because `cursor < b`. Inclusive uses a hidden `remaining`
  flag (initially `a <= b`): when `cursor == b` the flag is cleared instead of
  incrementing, so the increment never runs at the type's maximum and no wrap
  or trap occurs.

### Shipped G4 details (2026-11-24)

- Grammar: a string literal body is split at lex time. `{{` and `}}` are
  literal braces; `{name}` is a placeholder where `name` is one identifier
  (a letter or `_`, then letters, digits or `_`; Unicode letters allowed). A
  lone `}`, an unterminated `{`, an empty `{}` and anything else inside the
  braces (spaces, expressions, field access, calls, `:` format specifiers,
  nested braces, string literals) is a lexical error SE001 whose span covers
  the offending braces. Backslash escapes remain unsupported. A literal
  without placeholders is exactly the old static literal (`{{`/`}}` become
  single braces), so programs without interpolation lower and encode
  byte-identically (checked on all 14 example artifacts and 112 command
  outputs with `docs/tools/equivalence.sh`). The AST node is
  `ExprKind::Interpolation(Vec<InterpolationPart>)` with `Text` and
  `Value(Path)` parts.
- Typing: the identifier is read like any value read (NE001 unknown name, BE001
  after a move, BE005 while it is exclusively shared). Supported value types
  are all integer widths, floats (F3), `bool`, `char` and `string` (also through
  `borrow`/`share` parameters). Floats were rejected with TE017 "formatting
  floating-point values in string interpolation is not supported yet" in G4
  (a shortest round-trip formatter was judged disproportionate then); F3
  supports them with Rust's `Display` text, see "Shipped F3 details".
  Every other type (structs, enums, tuples, arrays, `List`, optionals,
  functions) is TE017 "cannot interpolate a value of type 'T'". The result
  type is `string`. Under `[build] alloc = false` an interpolating literal is
  TE033 naming the setting.
- Formatting: integers are decimal with `-` for negatives (signed values from
  `i8` to `i64` and unsigned values to `u64` are exact, including the
  minimum and maximum); `bool` is `true` / `false`; `char` is its UTF-8
  bytes; `string` copies its bytes.
- Lowering: each distinct interpolation shape (text pieces plus the types of
  the interpolated values) becomes one synthesized internal function
  `$interpolate$N` appended after the source functions (existing function IDs
  do not move). Its parameters are the values (`borrow string` for strings,
  by value for primitives) and its body is the new IR instruction
  `InitInterpolatedString`, followed by the usual capture, scope end and
  return. A literal lowers to an ordinary call: identifiers are read left to
  right, once each (a String is borrowed for the call, a primitive is copied);
  the call result is staged in a named owner local so every consumer sees a
  plain String move, with exact cleanup on every path (early return,
  `break`, `continue`, a later argument that exits, discarded statements).
  This accepts interpolation wherever a String value is accepted: bindings,
  arguments (owned and `.borrow()` temporaries), returns and tails, struct
  field initializers, tuple/array/List elements, `Some(...)`, branch and
  match values and replacement of a `var`.
- Wasm: `InitInterpolatedString` computes the exact byte length of every part
  in a 64-bit sum (text and string lengths, `int_len` for integers, constants
  for `bool`, a comparison chain for `char`), traps with the heap-allocation
  reason only when the sum exceeds the memory limit or the single block
  reservation fails, then writes the parts in order into the one block with
  `memory.copy`, `int_write` and `char_write`. No allocation, and so no trap,
  happens after the block is reserved, and there is no quadratic concat.
  The three formatting helpers are added to the module only when an
  interpolation is reachable. Text pieces use the same static data table as
  string literals.
- Limits: floats (above); width, padding, precision and other format
  specifiers; interpolating expressions or fields (bind a local first);
  interpolation in `const` initializers (a later step); raw literals.

### Shipped G6 details (2026-11-24)

- Operators: `&`, `|`, `^`, `<<`, `>>` and the compound forms `&= |= ^= <<= >>=` work on every integer width (`i8`..`i64`, `u8`..`u64`). Operands of `& | ^` share one type; the shift count is always `u32` (TE002 otherwise, also for compound shifts). Floats, `bool` and other types are TE007. `<<` discards the high bits (no overflow trap); `>>` is arithmetic for signed types and zero-filling for unsigned types. A count at or above the width is LE003 when constant (`i8 shift count must be less than 8`, also for `<<=`/`>>=`) and a controlled trap otherwise (reason 11, "shift count must be less than the bit width"). User-defined `BitAnd`/`Shl`/... dispatch (OP1) for nominal types is unchanged. The previous gates (signed shifts, non-`u32` bitwise operators and compound assignment, `u32`-only methods) are removed.
- Literal typing: an untyped literal operand takes the expected type or the other operand's type. A bitwise or shift expression built only from untyped literals with no other type information still defaults to `u32` (hashing convention, unchanged); arithmetic literals default to `i32`.
- Methods on every integer width (receiver type `T`, argument `T`; the shift methods take a `u32` count): `bit_and`, `bit_or`, `bit_xor`; `wrapping_add/sub/mul/neg`, `wrapping_shl/shr` (count masked with `width - 1`); `saturating_add/sub/mul`; `checked_add/sub/mul/div/rem/neg/shl/shr` returning `T?`. `checked_*` is `None` on overflow, a zero divisor, `MIN / -1` and a shift count at or above the width; `MIN % -1` is `Some(0)` (NUM-01; Rust reports it as overflow, the Memobits tables take this as the one documented difference). `checked_neg`/`wrapping_neg` are `0 - x` (unsigned `checked_neg` is `Some(0)` only for 0). A non-integer receiver is TE007, an argument mismatch TE002, a wrong argument count TE010. A user inherent method with one of these names on a nominal type keeps priority. A literal receiver of a `checked_*` method defaults to `i32` (no inference from the expected `T?`).
- Backend: integers stay normalized in Wasm locals (8/16-bit values are sign-extended or masked after every `<<`, wrapping and shift result; 32-bit native; 64-bit `i64`). New IR `BinaryOp`s (`WrappingSubtract`, `WrappingShiftLeft/Right`, `Saturating*`, `Checked*`) lower in `memobits-wasm/src/numerics.rs`; checked results are written into the scalar-option frame cell with the overflow flag as the tag (Some = 0, None = 1). IR validation requires equal integer operands (a `u32` count for shifts) and the `T?` option type for checked operations.
- Constant evaluation is shared: `memobits-syntax/src/numeric.rs` holds the integer semantics (wrapping, saturating, checked, shifts, bitwise) used by both the static-expression checks (`memobits-analysis/src/constants.rs`, which also folds `wrapping_*`, `saturating_*`, `bit_*` with constant operands) and `const` items (`memobits-resolve/src/consts.rs`, operators only; methods stay outside const initializers, so `checked_*` never folds). A `checked_*` result is an option and is never folded.
- Tests: `crates/memobits-cli/tests/g6_numerics.rs` compares Memobits source (`mb test`, `mb run`) and standalone Wasm with Rust's own integer methods over boundary values for all eight widths (hash tables), static folds against Rust in both directions, `const` items, constant/dynamic shift errors and traps, and negatives.
- Limits: no `overflowing_*`, `pow`, `abs`, `rotate_*`, `leading_zeros` or other bit-counting methods; `~` followed in G8; `checked_*`, `saturating_*`, `wrapping_*` do not fold in `const` initializers.

### Shipped G5 details (2026-11-24)

- Grammar: `[pub] const NAME: Type = expr;` is a module item (`ItemKind::Const`);
  `const` is now a reserved word (generic `<const N: u32>` is unchanged). The
  annotation is mandatory (SE002 otherwise). Allowed types: `i8`..`i64`,
  `u8`..`u64`, `f32`, `f64`, `bool`, `char`, `string`; anything else (aliases,
  arrays, `String`, optionals) is TE017. A repeat count `[v; NAME]` accepted only an
  identifier that starts with an uppercase letter (any name since G7).
- Evaluation (`memobits-resolve/src/consts.rs`, after names, imports and
  visibility are validated, over every loaded module, used or not): a typed
  evaluator that follows the checker's literal rules (an untyped literal takes
  the expected or the other operand's type; `i32`/`f64` otherwise; the `-`
  literal form reaches the signed minimum; casts use their operand's own type,
  so `300 as u8` has an `i32` operand) and the static-expression rules of
  NUM-01/NUM-04/NUM-05: checked integer arithmetic per width (LE001, LE002 with
  `MIN % -1 == 0`), `as` casts with Rust semantics, bitwise and shift operators
  only on `u32` (count >= 32 is LE003), IEEE floats (f32 operations round to
  f32), comparisons (ordering on numbers, equality on numbers, bool and char),
  `&&`, `||`, `!`, unary `-` (signed only) and `+`. A string constant is a
  literal or another string constant. Values are memoized; a dependency cycle
  is LE004 and names the path; a cycle failure or an error in one constant
  does not hide errors elsewhere. Names resolve through the module's own
  constants and `use m::NAME [as X];`, or the qualified `m::NAME`.
- Inlining: each use is replaced in the syntax tree by the value, so later
  passes see a literal and the const items and their imports are removed
  (programs without constants and without a named repeat count skip the pass
  and lower byte-identically). Bool, char and string become the ordinary
  literals; numbers become `ExprKind::TypedNumber { raw, ty }`, a literal with a
  fixed type (not adaptable like `5`): the checker types it as `ty`, lowering
  emits one constant, the constant analysis treats it as a known value, and a
  constant array index is checked statically.
- Use sites: expressions anywhere (arguments, `let`, `return`, operands,
  conditions, `loop i in 0..LIMIT`, array indexes, struct fields, method
  bodies), `{NAME}` in a string literal (folded to text at compile time;
  adjacent text merges, so `"{A}{B}"` of constants is one static literal and
  needs no allocator), and, for `u32` constants only, array lengths
  `array<T, SIZE>`, nominal const arguments `Lane<SIZE>` and repeat counts
  `[v; SIZE]` (other integer types are TE017). Float constants cannot be
  interpolated (TE017, as for floats today).
- Names: constants share the module's value namespace (ME005 against
  functions, types, imports and other constants); private by default
  (ME007), `pub` for other modules; a const cannot be an application entry or
  a library export (ME009) and is not a type (ME008). Locals, parameters,
  loop variables and tuple/destructure bindings shadow a constant; assigning
  to one is TE004. A bare identifier in a `match` arm that named a visible
  constant was TE017 until G7 (now a constant pattern, see G7).
- Standalone commands `mb analyze` / `mb ownership` on one file fold that
  file's constants too (`fold_standalone_constants`); `mb syntax` only parses.
- Limits: no `static`/global storage, no mutation, no calls (including
  `wrapping_*`/`checked_*` methods), no `if`/`match`/blocks in initializers, no
  aggregates, no interpolation in initializers, no non-`u32` array lengths, no type aliases as the const type.

### Shipped G2 details (2026-11-24)

- Divergence: an `if`/`else` or `match` arm that cannot fall through
  (`return`, `break`, `continue`, or a block ending in one) joins with the other
  branch's type, in any position and for owner values (value-sink lowering
  already skips diverging branches). Genuinely different branch types stay
  TE013.
- `try` is a reserved word. Grammar: `try operand [else [name] { handler }]`,
  where the operand is a unary-level expression (`try a.b(c) else e { ... }`,
  `1 + try f() else { 0 } * 2` is `1 + ((try f() else { 0 }) * 2)`), the
  handler is a block, and an `else` belongs to the nearest `try` (no ambiguity
  with `if ... else`). A `try ... else` that starts a statement ends at its
  closing brace; the `;` is optional there.
- Lowering: the parser builds an ordinary `match` with two arms and marker
  patterns `$try_ok(v)` / `$try_err(name)` that the checker resolves by the
  scrutinee's built-in enum (`Ok`/`Err` on `T ! E`, `Some`/`None` on `T?`).
  On `T ?! E` (`(T?) ! E`) the markers select the `!` layer, so the result is
  the `T?` payload. Evaluation, moves, exhaustiveness and cleanup are the
  existing match rules: the operand runs once, an owned success value moves out,
  an unused owned success value is released once, traps are not caught.
- Without `else`: `target = try expr;` (plain `=` only; `+=` etc. are SE002)
  assigns on success and does nothing on failure (the target place is only
  evaluated on the success arm; if the RHS moved the target, the target is
  unavailable on the failure path and later uses are BE001). `try expr;` as an
  expression statement discards the failure and any success value. In every
  other position (binding initializer, tail, argument, condition, `return`) a
  `try` without `else` is SE002 "`try` needs `else`".
- Diagnostics: handler type mismatch TE013 ("`try` handler must produce T or
  exit"), name on `T?` TE030, non-fallible operand TE029, missing `else` SE002.
- Error types cannot own heap storage (LE900), so error payloads are plain
  data and nothing heap is released on the failure path; the owner paths are
  success payloads (bound, moved, discarded or overwritten) and handler locals.
  `Ok(Some(heap))`, `Ok(list)` constructors and a struct literal inside `Ok(...)`
  were gates here and are lifted by F2 (below).

### Shipped G7 details (2026-11-24)

- Grammar: `PatternKind::{Literal, Constant, Or}` and `MatchArm.guard`. A
  pattern is `alt (| alt)*`; an alternative is `_`, a literal (integer with an
  optional `-`, `true`/`false`, char, string without placeholders), a name, a
  variant path with sub-patterns, or a tuple/group; `(p | q)` groups. `|`
  alternatives and sub-patterns nest at any depth. A guard is `if expr`
  between the pattern and `=>` (any `bool` expression). Float literals,
  struct patterns and `@` stay SE002. `[v; name]` repeat counts take any
  identifier (an identifier after `;` cannot be anything else); an unknown or
  non-`u32` name is reported by the const pass (NE001 / TE017).
- Scrutinee types: besides enums and tuples, any integer, float, bool, char or
  string value (or a reference to one). Such a scrutinee is always matched in
  place and never moved (a string temporary is released after the match); a
  lone binding arm is allowed for these types (an integer copy, a read-only
  reference for strings) and stays TE030 for an enum or tuple scrutinee.
  Floats accept only `_`/a binding (no float literal or constant pattern).
- Literal semantics: equality in the scrutinee's type. Integers must fit the
  type (TE030 "does not fit u8", also `-1` for unsigned); bool/char/string
  literals need a bool/char/string position; strings compare length then bytes
  in place (new IR instruction `StringEquals`: two read-only borrows, `bool`
  output, no allocation, no move; static and heap strings alike).
- Constants (`consts.rs` rewriter): a bare identifier that names a visible
  `const` (including an `as` alias), or `m::NAME`, becomes
  `PatternKind::Constant { path, value }` before analysis (a local of the same
  name does not shadow it in a pattern). The checker lets a lone name that is a
  variant of the matched enum stay that variant; otherwise it is the constant's
  literal with the same type rules (a `u8` constant against an `i32` scrutinee
  is TE030). `f32`/`f64` constants are TE017 as patterns. Any other bare
  identifier is a binding. The `try ... else name` handler name is never a
  constant.
- Exhaustiveness (`types/patterns.rs`): the pattern matrix gained `Lit`
  (integer/char/string: an infinite domain, so a literal never completes a
  signature), bool as a two-constructor type (`false`/`true`) and `Or`
  (expanded into rows when it heads a column; a head alternative is useful when
  any alternative is). A guarded arm is checked for reachability but never
  joins the matrix. TE031 names missing values (`false`, `Some(_)`, `(true, _)`)
  and, when only `_` is missing, says to add a `_` or binding arm; with guards
  present it notes that guarded arms do not count. TE032 is unchanged.
- Or-patterns: each alternative is checked in its own scope; all must bind the
  same names with the same types (TE030 for a missing name or a different
  type); later alternatives reuse the first alternative's locals, so the arm body
  exists once. The checker stores the or-free `alternatives` of each arm and
  lowering emits one decision-tree leaf per alternative that binds and jumps to
  the arm's single body block (no body duplication).
- Lowering: the decision tree gained a literal column: test the first row's
  literal (`==` after a `Load`, or `StringEquals`), rows with that literal or
  an irrefutable pattern continue without the column, the rest continue on the
  failing edge (after a failed bool test the other bool literal is certain).
  All occurrences are references, so nested literals reach through
  `VariantAddr`/`FieldAddr` like other sub-patterns.
- Guard ownership rule: a guard never moves anything. For an in-place match
  (references, element/field places, scalars, strings) the arm's bindings are
  already read-only views; they are bound at the leaf, the guard runs and a
  true guard jumps to the body. For an owned (consuming) match the checker
  gives every binding a guard twin (a copy for primitives, a read-only
  reference otherwise); the leaf binds the twins by address into the owner,
  evaluates the guard, and only on `true` moves the real payloads out (so unbound
  owned parts are released exactly once as before). On `false` the owner is
  untouched and matching resumes with the rows after this one in the same
  decision-tree state (later alternatives of the same arm are tried too). Each
  leaf re-evaluates the guard expression (lowering duplicates guard code, never
  arm bodies); guard temporaries are released inside the guard. Guards may use
  `&&`/`||`, calls and `return`.
- Limits: the guard, literal and unbound-String limits that G7 recorded here
  (aggregate bindings and String-owning tuples in payloads, a literal on the
  `Ok` payload of `string ! E`, a variant that leaves a String unbound) are
  lifted by F2 (below). `@` bindings, struct patterns, ranges and float
  patterns remain open.
- Tests: `crates/memobits-cli/tests/g7_patterns.rs` (20), parser/analysis tests
  updated for the removed gates; guide `enums_outcomes.mb` (`literal_patterns`,
  `constant_patterns`, `or_patterns`, `guards`: 109 tests).

### Shipped G8 details (2026-11-24)

- `~x`: bitwise complement of any integer type at its own width (Rust `!x`; `~0u8` is 255, `~(-128i8)` is 127, `~0u64` is `u64::MAX`). Prefix operator with the precedence of unary `-`/`!` (`~x as T` complements first; `-~x` and `~~x` nest). Floats, `bool`, `char`, `string` and nominal types are TE007 ``"`~` requires an integer, found T"``; there is no `core::ops::Not`-style interface and no overloading (primitive-only, `!` stays `bool`-only). An expected type applies to the operand (`let c: u8 = ~0;`); with no context an operand built only from untyped literals defaults to `u32`, like `& | ^ << >>` (`let a := ~0;` is `4294967295`), and `~x` with a typed `x` has the type of `x` (`let c: u16 = ~a` with `a: u8` is TE002). The parser gate that rejected `~` (lexical SE001) is gone; `~` is a lexer symbol and a prefix operator.
- Evaluation is shared: `memobits-syntax/src/numeric.rs::complement` (`kind.wrap(!value)`) is used by the `const` item evaluator (`memobits-resolve/src/consts.rs`) and the static-expression folder (`memobits-analysis/src/constants.rs`), so constant and dynamic results agree; `const` items fold `~`, and a statically known `~x` participates in LE001/LE002/LE003 checks like any other folded operator. IR `UnaryOp::Complement` (validation requires an integer operand and equal output); Wasm lowers it to `xor -1` and re-normalizes narrow results (unsigned masked, signed stays sign-extended), so 8/16-bit results are exact; no trap is possible.
- `Self` (resolved in `memobits-syntax/src/self_type.rs`, right after parsing, so later passes only see the written type): inside `extend` blocks of every form (inherent `extend T { }`, trailing `type T ... extend { }`, `extend T of Interface { }`, including its `type Output = Self;` bindings) `Self` is the extension target type with its generic and const arguments (`extend Pair<T>`-style trailing blocks: `Self` is `Pair<T>`; `Lane<const N>`: `Lane<N>`; `extend Pair<i32>`: `Pair<i32>`; a qualified target keeps its path). Positions: parameter and result types, `let` annotations, nested type arguments (`array<Self, 2>` style), struct literals `Self { .. }` (the target's type arguments are filled in), destructuring `let Self { .. } := v;`, enum variant paths in expressions and patterns (`Self::Variant`, `Self::Variant(x)`), anywhere inside method bodies. There are no static-style calls in the language yet (every method takes a receiver), so `Self::method(..)` is not applicable. `Self<..>` is rejected ("takes no type arguments"), a bare `Self` value ("names a type, not a value"), `Self::X` as a type ("is not a type").
- Errors (all SE002, at the `Self` token): outside `extend` blocks (free functions, type declarations, `const` items) ``"`Self` is only available inside an `extend` block ..."`` (this replaces the former NE003 "unknown type 'Self'"; F1 removed the duplicate NE003 that used to follow at the same span).
- Interface declarations: `Self` in an `interface` declaration is rejected with ``"`Self` in interface declarations is not supported yet"``. The existing interface machinery selects implementations by the explicit target and would need new dispatch semantics (the bound receiver `T`, associated projections and the `of Interface` selection do not model a `Self` return), so it is deferred, not approximated.
- Tests: `crates/memobits-cli/tests/g8_complement_self.rs` (12): `~` against Rust `!x` on all eight widths (dynamic table hash, double complement, `~x & x`/`| x`/`^ x`, assignment), boundary values written out, `const` items and static folds against Rust for every width (LE002 hit counts), literal defaulting, TE007/TE002 negatives, `Self` in every position over source `mb test`/`mb run` and standalone Wasm (generic, const-generic, instantiated, enum, generic enum, `of Add`/`of Neg`/user interface, cross-module public extensions), an explicit-type twin of the same program, outside-extend and interface negatives. `wp20_s_gaps` now expects TE007 for `~` on a nominal type. Guide: `numbers.mb` `bitwise_complement`, `generics.mb` `self_in_extend_blocks`, `operators.mb` `self_in_interface_extensions` (112 tests).
- Limits: no `~` overloading or `Not` interface; `Self` in interface declarations; no `Self` in free functions, type declarations or constants; no `Self::associated_type` projection.

### Shipped F1 details (2026-11-24)

Facts about the shipped behavior; no new decisions (principle A: compositions
are allowed once cleanup is proven).

- Method arguments: every non-receiver argument of an inherent method, an
  interface-selected (`of I`) method and a generic nominal method is checked
  and lowered by the same code as a free-function argument
  (`check_call_argument` in analysis `types.rs`, `lower_call_argument` in
  `lower/calls.rs`). An owned struct, tuple, record, array, enum, List or
  String moves in (a temporary is staged in a hidden owner, a String owner uses
  the shared transport predicate), `.borrow()` / `.share()` conversions pass a
  loan to `borrow` / `share` parameters, and a mismatch is the same TE002 /
  TE017 as for a function ("argument does not match the borrow parameter
  access; use an explicit .borrow() or .share() conversion"). Argument count
  errors stay TE010. Receiver rules are unchanged. The former TE017 on
  `q.eqx(r)` and the TE002 "expected R, found borrow R" are gone.
- Heap String and owner call results: a call that returns a heap `string` or a
  String-owning aggregate (struct, tuple, record, enum, array) and is not bound
  directly is staged in a hidden `call result` owner local
  (`stage_fresh_call` in `lower.rs`), so the IR validation rule "assigned
  directly to a whole local" holds. Positions: function tail and `return`
  operand, `push` argument, array, List and tuple elements, enum payloads
  (`Some(g())`, `Ok(g())`, user variants), `push_str` suffix (released right
  after the append), plus the already working binding, assignment, owned
  argument, struct field and branch-sink positions. The hidden owner is
  registered for cleanup before later operands run, so an early `return`
  releases it. `string ! E` still needs its immediate consuming match (TE018),
  and List call results keep their own rule.
- Literals: the lexer (`memobits-syntax/src/literals.rs`) accepts `0x`/`0X`
  hexadecimal, `0b` binary and `0o` octal integers and `_` between the digits
  of any integer or float literal (also in the fraction and the exponent),
  doubled `__` included. It emits one canonical decimal spelling (value as
  `u128`), so contextual typing, range checks (type error on overflow of the
  contextual type), `const` items, literal patterns, array lengths, repeat
  counts and constant folding see the same text as for decimal and are
  unchanged. Spans keep the original spelling. SE001: nothing after a prefix,
  `_` directly after a prefix, a trailing `_`, an invalid digit for the radix
  (also letters, so `0xFFu8` fails: there are no literal suffixes and none were
  added), `1e_5` / missing exponent digits, and a radix literal above
  `u128::MAX`. A malformed literal lexes as `0` to avoid cascading errors.
- `Self` outside an `extend` block reports only SE002 now: name resolution no
  longer adds NE003 "unknown type 'Self'" at the same span.
- Tests: `crates/memobits-cli/tests/f1_followups.rs`. Stale negatives that
  pinned the lifted gates were updated (see launch-progress F1).
- Limits: unchanged otherwise; the tuple-with-enum validation error, the
  `string ! E` immediate-match rule and the List call-result rule are lifted by
  F2 (below).

### Shipped F2 details (2026-11-24)

Facts about the shipped behavior; no new decisions (principle A: compositions
are allowed once cleanup is proven). This supersedes the "still gated" lists in
the G1, G2 and G7 details above for everything named here.

- Ownership model: `List<T>` is a heap leaf like `String` in every shared
  owner predicate (`owns_string_aggregate`, the nominal-owner rule
  `is_nominal_string_owner` through its `OwnerTypeModel` adapters, the tuple
  rule, the analysis `contains_string_owner`). A struct, tuple, array or enum
  that holds a List anywhere is therefore a heap owner: its locals are tracked
  like String owners, moves clear the source descriptor, and scope exit, early
  returns, overwrite, `replace`, `swap`, `clear` and `drop` release it
  type-directed (elements first, then the block). Wasm layout stores a List
  field or payload as the 12-byte descriptor.
- Payload composition: a freshly built owner used as an enum payload (a nested
  variant, struct or record literal, array) is staged in a hidden
  `enum owner payload` local first (`lower_variant`), as owner elements already
  were. `Ok(Some(heap))`, `Ok(list)`, `Ok(Label { .. })`, `Some(Pair { .. })`,
  `Some(list)`, a user variant with a List payload and a heap `Ok(x)` in `if` /
  `match` branches work; a List captured for a payload or a field moves in like
  a String (the IR validator accepts a List capture that feeds `ListPush`,
  `EnumNew`, `StructNew` or `ArrayNew`).
- `string ! E` is an ordinary String-owning enum now: the special rules for
  `Result<String, E>` (the "immediate consuming match" requirement, the
  `approved_ok` / `ResultReturn` flow, the `String enum payloads require a
  consuming match` check on `VariantAddr` and the call-argument exclusion) are
  gone from the validator. A heap `string ! E` call result can be bound,
  passed as an owned argument, returned, tail-called, stored in a struct field,
  a tuple, an array or a List, wrapped in `Some(..)`, or consumed by `try ...
  else`, with the same staging and cleanup as `Kind::Word(string)`. The
  entry-outcome tag stays only for the entry ABI and the UTF-8 validation
  result.
- Literal patterns on the `Ok` payload of `string ! E` (`Ok("abcd")`,
  `Ok("a" | "b")`) work: the decision tree reaches the payload through a
  `VariantAddr` like for any enum. A literal or a guard binding inside a
  String-owning tuple that sits in an enum payload works too: references into
  an owner held by decision-tree and guard-view locals are accepted by the Wasm
  borrow validation when every assignment comes from an element, field or
  variant-payload address (`lent_elements`, previously elements only), and
  chains rooted at such a local count as rooted at a named owner. A guard in an
  owned match may therefore bind a whole String-owning aggregate or parts of a
  String-owning tuple in a payload (the twin is a read-only reference; nothing
  moves until the arm is taken). The two TE017 messages for these cases are
  gone.
- Lists in aggregates: construction in struct and record literals, tuples,
  arrays (`array<List<T>, N>`, including tuples with List fields as array
  elements) and enum payloads; the place chain `s.l`, `t.0`, `a[i]`, `a[i].l`
  is a List place for `len`, `get`, `push`, `pop`, `clear`, `contains`,
  `index_of`, `loop x in ..`, `replace`, `swap`, `s.l = v`, `a[i] = v` and
  `.borrow()` / `.share()`. A mutating method needs a `var` or `share` root
  (TE017 otherwise). Moving a List out of a field or element is still a partial
  move (TE022). A struct that holds a List and a String as fields is admitted by
  the transport rule (List and String are the two leaf kinds).
- List call results: a call that returns a `List` is staged in a hidden owner
  like a String call result (`stage_fresh_call`), so it works as a function tail
  or `return` operand, a `push` argument, an element or payload, a struct or
  tuple field, a receiver (`ml(5).len()`), a replacement value and a discarded
  statement.
- Tuples holding String-owning enums or arrays: the tuple transport rule accepts
  enum, array and List fields (`(gk(), 1)`, `take((k, 2))`,
  `fn f() -> (Kind, i32)`, arrays of such tuples); destructuring and matching a
  tuple with an enum field moves or lends the enum by the existing extraction
  sequence. A tuple that holds a nominal String-owning struct keeps the earlier
  TE017 gates for destructuring and owned calls. (F2 kept a nominal struct with
  a direct String or List field plus a heap-owning enum or tuple field out of
  the transport predicate; F3 admitted it, see "Shipped F3 details".)
- Mixed variants: a variant that mixes a String with other payloads may leave
  the String unbound (`K::Two(_, b)`, `K::One(_, n)`): the unbound String is
  extracted into a discarded local and released with the arm. The IR check that
  every String `VariantExtract` consumes its base accepts a non-final extraction
  when a later extraction of the same owner local consumes the cell.
- Diagnostics: an integer pattern and a constant array index in a diagnostic
  echo the literal as written (`0x1FF`, `-0b1000_0001`, `1_6`); the lexer
  records the original spelling of every literal whose canonical decimal
  differs (F2 kept it in a thread-local table keyed by span; F3 moved it into
  the AST literal node, see "Shipped F3 details"), checks keep using the
  canonical value. The negative literal pattern's operand
  span now covers only the digits.
- Wasm backend: `supported_type` accepts List array elements, `has_string_fields`
  counts List fields, `construction_aliases` skips `EndListLocal` after a struct
  constructor, and the borrow validation counts enums and Lists as heap storage.
- Tests: `crates/memobits-cli/tests/f2_payloads.rs` (14): payload composition,
  `string ! E` in every position and literal patterns, List call results, List
  storage in structs, tuples and arrays with `replace` / `swap`, tuples with
  enums, unbound String payloads, guards and literals in String tuples, range
  echo, rejected partial moves, and the struct gate; capped-memory stress
  (memory capped to initial + 1 page, 4,096 iterations, half of them returning
  early with every composition live) for payloads, storage and guards, plus a
  mutation program that keeps a list-carrying variant and a heap `string ! E` in
  a never-emptied List and must trap with "guest heap allocation failed". Stale
  negatives were rewritten as positives in `d2_nested_result_storage.rs`,
  `g1_limits.rs` and `tuple_nested_arrays.rs`. Guide: `collections.mb`
  (`list_call_results`, `lists_inside_aggregates`), `enums_outcomes.mb`
  (`heap_payload_composition`, `string_results_everywhere`,
  `unbound_string_payloads`, `guards_in_string_tuples`), `tuples.mb`
  (`tuples_with_string_owning_enums`): 122 tests.
- Limits: moving a List out of a field, element or payload of a live owner
  (use `replace`, `swap`, `pop`); struct with a direct String/List field plus a
  heap-owning enum or tuple field by value across a call (lifted in F3);
  reference elements and fields stay rejected; a guard still cannot move anything.

### Shipped F3 details (2026-11-24)

Facts about the shipped behavior; no new decisions (principle A: compositions
are allowed once cleanup is proven, and the float text is exactly Rust's).

- Float interpolation: `{x}` for `f32` and `f64` prints exactly Rust's `Display`
  text (`format!("{}", x)`): the shortest digits that read back as the same
  value of that width (an `f32` uses its own shortest text, so `0.1f32` prints
  `0.1` while the same value widened to `f64` prints `0.10000000149011612`),
  never an exponent (`1e20` is `100000000000000000000`, `1e-7` is
  `0.0000001`), no `.0` for integral values (`3.0` is `3`), `-0` for negative
  zero, `NaN` (any NaN, no sign), `inf` and `-inf`. G4's TE017 "not supported
  yet" for floats is gone; other unsupported types keep their TE017, whose
  text now lists floats among the supported types.
- Guest algorithm (`crates/memobits-wasm/src/float_format.rs`): Burger-Dybvig
  free-format shortest digit generation on fixed 1,280-bit big integers
  (`r`, `s`, `m+`, `m-` and a temporary, 40 little-endian `u32` limbs each),
  with no tables. The scale is estimated from the binary exponent
  (`ceil(log10(2) * floor(log2 v) - 1e-10)`, never above the true exponent and
  at most one below, repaired by one fix-up step); digits come from repeated
  `x10` and subtraction; the boundaries are inclusive exactly when the mantissa
  is even; the gap below the smallest power of two in a binade is half as wide;
  a digit decision that is both "low" and "high" rounds by comparing `2r` with
  `s` (ties up). The text is built in a static scratch region (five big
  integers, 32 digit bytes and a 336-byte text buffer, 1,168 bytes, reserved
  after the string data) and copied into the interpolation block; `float_text`
  returns the length for the length pass and `float_write` formats again for
  the write pass. The eight functions are written in a small text assembler
  with named locals and labels (`assemble` in the same file) and are appended
  after the three integer helpers.
- Reachability: the formatter functions, their eight function types and the
  scratch region exist only when a reachable `InitInterpolatedString` has an
  `f32` or `f64` part. A program without a float placeholder is byte-identical
  to the F2 output (`docs/tools/equivalence.sh` against a HEAD build:
  14 artifacts and 337 command outputs identical; the guide's new float test is
  left out of the compared copy because the F2 compiler cannot compile it). The
  formatter adds about 1.7 KB of code to a minimal program (3,307 bytes with a
  float placeholder against 1,601 with an integer one).
- Constants: `{NAME}` of a float `const` folds at compile time with Rust's
  formatter (`f32` constants as `f32`); a program whose float placeholders all
  fold keeps no formatter, and an all-constant literal is a static literal as
  before.
- Literal spellings (F2 tech debt): the lexer returns a `NumberLiteral`
  (`canonical`, plus `written` when the source spelling differs: radix prefix
  or `_` separators). It is the payload of `TokenKind::Number` and
  `ExprKind::Number`; `Deref<Target = str>` keeps every check on the canonical
  text and `NumberLiteral::written()` is what diagnostics echo (integer
  patterns, constant array index). The thread-local side table and
  `literal_spelling` are deleted. Diagnostics are unchanged.
- Transport: the shared predicate (`is_nominal_string_owner`) admits a nominal
  struct whose fields are String, List, primitives, nested admitted owners,
  non-empty arrays of owners and, new, enums and tuples: one that owns heap
  storage is a `Heap` field (cleaned type-directed; it never makes a struct an
  owner on its own), a plain enum or tuple counts as a primitive field. A struct
  still needs at least one direct String, List or nested owner field, so a
  struct holding only an enum field stays outside. Such a struct moves by value
  into calls (consumed, ignored, returned, dropped on an early return) with the
  aggregate-parameter prologue clearing moved descriptors by type and active
  tag, as for other owners. The TE017 text for owned struct calls no longer
  mentions enum or tuple fields.
- Tests: `crates/memobits-cli/tests/f3_floats.rs` (9): an f64 table of more than
  7,000 values (`MAX`, `MIN`, `MIN_POSITIVE`, subnormals, `EPSILON`, every power
  of ten from `1e-323` to `1e308` with both neighbors and the negative, every
  power of two from `2^-1074` to `2^1023`, 2,500 seeded random finite bit
  patterns), an f32 table of more than 3,000 values (same families, 2,500
  random), NaN, infinities and zeros, mixed placeholders and parameters,
  constants, reachability (`f64.ceil` present only with a float placeholder),
  capped-memory loops (4,096 iterations, memory capped to initial plus one
  page, plus a mutation program that keeps every string and must trap with
  "guest heap allocation failed"), the struct transport stress under the same
  cap with the same mutation, and plain enum and tuple fields. Expected texts
  are `format!("{}", v)` in the test; the guest hashes each formatted string
  and the test hashes Rust's, and every value matched from source and from the
  standalone Wasm. A unit test in `float_format.rs` drives the helpers directly
  against Rust over about 10,000 more values, and
  `memobits-syntax/tests/f3_literals.rs` covers the literal node. The workspace
  `Cargo.toml` builds the `wasmi` crates with `opt-level = 3` and without debug
  assertions in the dev profile, which turns the table tests from many minutes
  into seconds.
- Limits: matching a `List`-payload enum field of a struct in place
  (`match m.k { Many(l) => .. }` where `Many` holds a `List`) fails IR
  validation (TE018), with or without a call (found while testing; a String
  payload works); a struct holding only an enum or tuple field is still not a
  transport owner; there are no precision, width or exponent options (format
  specifiers remain open).

## Stage 4: functions as values, closures, generics, Box (2026-11-25, user approved)

- **Function types** are written `fn(T1, T2) -> R` (`-> R` omitted for
  Unit); parameter access modes appear in the type (`fn(borrow string) -> u32`).
- **Named functions** may use an expression body: `fn f(x: i32) -> i32 => x * 2`
  (block bodies keep the existing tail/`return` rules). Same in `extend`.
- **Anonymous functions** are named functions without a name:
  `fn(x: i32) -> i32 => x * 2` or `fn(x: i32) -> i32 { … }`; with a known
  expected function type, parameter and result types may be omitted
  (`fn(x) => x * 2`). The bare `x => …` form is not used (it would clash
  with match arms).
- **One function type, access modes decide escaping** (reusing the
  language's ownership vocabulary instead of new keywords):
  - an owned `fn(...)` value may be stored, returned and moved; it may only
    capture by move (owned environment, alloc layer when non-empty);
  - a `borrow fn(...)` parameter receives any function value, including
    closures that capture surrounding variables by read-only borrow; like
    every borrow it is second-class: callable and passable, never stored or
    returned (non-escaping, no heap);
  - a `share fn(...)` parameter additionally accepts closures that mutate
    captured variables (exclusive access for the call's duration).
  A function value that captures nothing works everywhere and needs no heap.
  Captures are inferred from use: read → borrow, mutation → share, explicit
  move into an owned environment only for owned `fn` values.
- **Generics**: several type parameters and bounds via
  `where T: A + B, U: C`; borrowed generic parameters allowed; existing
  single-bound forms keep working.
- **`Box<T>`** (alloc layer, `use alloc::Box;`): single-owner heap box built
  with `Box(value)`; field access, method calls and `match` see through the
  box automatically; recursive types are allowed only through `Box`.
- Order: H1 function values + anonymous non-capturing functions + `=> expr`
  bodies → H2 borrow/share closures → H3 generics → H4 Box → H5 owned
  (escaping) closures.

### Shipped H1 details (2026-11-25)

Facts about the shipped behavior of the first Stage 4 step; the Stage 4
decision above is unchanged. (H5b changed one H1 fact: function values are no
longer copyable scalars; every function value is a move-only owner, see "Shipped
H5b details". Lending to `borrow fn`/`share fn`, calling in place and fresh
values per mention of a name cover the old copy uses.)

- Syntax: `fn(T1, borrow T2) -> R` is a type (the `\0fn` path in the AST; the
  last type argument is the result, the `\0unit` marker when `-> R` is
  omitted). `(fn(i32) -> i32)?` needs the parentheses, since `-> R` takes a
  whole type; `fn(i32) -> i32?` is a function returning `i32?`. An anonymous
  function is `ExprKind::Function`: `fn(x: i32) -> i32 => expr`,
  `fn(x: i32) -> i32 { ... }`, `fn(x) => expr` (types from an expected function
  type), parameters may be `var`. `=> expr` after the head of a named function,
  an `extend` method or a `test fn` is a block that is only its tail; a
  trailing `;` after an expression body is optional.
- Typing: parameter types come from annotations or the expected function type
  (else TE002 "cannot infer the type of parameter 'x'"); the result comes from
  `-> R`, the expected type or, for an `=>` body without either, the body's
  type. An expected function type of another arity is TE010. The body is
  checked as a separate function (`Checker::anonymous_function`); a name that
  resolves to a local of an enclosing function is TE017 "closures that capture
  variables arrive in the next step" (constants, top-level functions and
  imports resolve normally). A `borrow`/`share` parameter of function type is
  TE017 (it belongs to H2). Function types containing a `List` parameter or
  result are TE017 (a List needs a direct internal call). Function values
  have no equality: `==`/`!=` is TE007. Access modes are part of the type, so
  `fn(string) -> u32` and `fn(borrow string) -> u32` do not unify (TE002).
- Values: a top-level function named without a call is a value of its type,
  including imported functions (visibility is the module loader's) and `extern`
  host functions (a plain Wasm import; source `mb run` links it). A generic
  function is a value only where the expected function type fixes its type
  argument (`let f: fn(i32) -> i32 = id;`, an argument position); otherwise
  TE002 explains it. `test fn` names are never in scope (NE001 "test functions
  cannot be called or used as values"). A local of function type shadows a
  top-level function of the same name.
- Calls: `f(x)` through a local or parameter, `s.callback(x)` through a
  function-valued field, `xs[i](x)`, `(make())(x)`, `make()(x)`. Arguments
  follow the target's parameter access modes exactly like a direct call
  (owned moves, `.borrow()` / `.share()` loans, String and owner temporaries
  staged in hidden owners). A method of the same name wins over a field
  (`value.run` still reads the field). Builtin method names (`len`, `get`,
  `push`, ...) also win over fields of the same name.
- Representation: one `i64` per function value: low word = slot in the
  module's function table, high word = environment pointer (always 0 in H1).
  Slot 0 is never filled, so one function table has `n + 1` slots, filled by
  an active element segment at offset 1, holding only the functions used as
  values that are reachable. IR: `Type::Function(Signature)` is a scalar
  (`Type::is_scalar`), `Constant::Function(FunctionId)` creates a value,
  `Call` with a local/value callee is an indirect call; named direct calls
  keep `Source::Function`. The Wasm backend erases function types to `u64`
  (`crates/memobits-wasm/src/function_values.rs`), emits `i64.const slot` for a
  constant and `call_indirect` (one Wasm type per distinct signature, shared
  with function types) for an indirect call, preceded by a slot-range check
  that traps with reason 13 `InvalidFunction` ("call through an invalid
  function value"); a signature mismatch cannot occur because values are only
  made from typed functions, and `call_indirect` would trap natively anyway.
  Function values cannot appear in exported signatures or the entry's result
  (LE900 "Wasm exported signatures cannot use function values"). They need no
  heap (`[build] alloc = false` works).
- Owners through function values: the shared heap-ownership analysis
  (`scoped_string.rs`) treats a call through a function value as a call to
  every address-taken function of the same signature (`call_targets`), so owned
  String/owner arguments, returned owners and `share` String parameters get the
  same moves and exact cleanup as direct calls (capped-memory evidence below).
- Anonymous functions are lifted: each becomes an ordinary IR function
  (`<parent>$anonymous$<id>`) with the next function ids; the parent evaluates
  to `Constant::Function`. Facts: `FunctionFacts::anonymous`,
  `anonymous_functions`.
- Limits (H1): no captures (next step), no `borrow fn`/`share fn` parameters,
  no function types with List parameters or results, no equality, no exported
  function values, no generic function value without an expected type.
- Tests: `crates/memobits-cli/tests/h1_function_values.rs` (18): helpers,
  recursion through values, every storage position (struct, tuple, record,
  array, List, enum payload, `T?`), copyability, imports and visibility,
  generic instantiation by expected type, externs, anonymous functions in
  every position, `=>` bodies (functions, methods, tests), calls through
  fields, methods, elements and results, argument modes and owners, the Wasm
  table/element/`call_indirect` structure, `alloc = false`, the invalid-slot
  trap, exact owner cleanup through function values (memory capped to
  initial + 1 page, 4,096 iterations x 1,024-byte strings, plus source and
  Wasm runs), and the negatives. Guide: `functions.mb` (6 tests, 129 total).

### Shipped H2 details (2026-11-25)

Facts about the shipped non-escaping closures; the Stage 4 decision is unchanged.

- Parameters `borrow fn(..)` / `share fn(..)` (also in function types) take a
  function value bare. In IR a `share fn` is a `Borrow` of the function cell (the
  share effect lives in the closure's loans on its captures). They are references:
  callable (`Load` then `Call`), passable to another `borrow fn`/`share fn`
  parameter (a `share fn` never to a `borrow fn`), never stored, returned or put
  in fields/collections (`read_type` keeps function references, so `ensure` and
  `push` reject them: "reference values cannot escape").
- Captures are inferred in the checker by a structural capture analysis (H2b),
  not by probing diagnostics. Per function literal one analysis pass
  (`closure_body` with `BodyMode::Infer`) checks the body once without facts, with
  every enclosing name bound as a hidden share parameter (a function-typed name
  takes the access of its effect). The checker records the names it looks up
  (uses) and calls `note_write` wherever it accepts a write permission:
  assignment and compound-assignment targets (whole, `x.f`, `x[i]`), `replace` /
  `swap` places, `push` / `pop` / `clear` / `push_str`, `.share()` conversions,
  a share reference passed on as it is, receivers of `share self` methods, and the
  captures of nested literals (propagated outward). Everything else is a read.
  The result (used names in first-use order, written subset) is cached per literal
  for the duration of the outermost literal, so a nested body is analysed once and
  the real check binds the captures as trailing hidden `borrow`/`share` parameters
  of the lifted function with those accesses. Cost is linear in the body size
  (12 nested levels check in milliseconds; the earlier probe-and-promote design
  doubled per level) and nothing depends on diagnostic wording (`root_note` is
  diagnostics only). Names of grandparent functions are captured transitively. A
  function-typed capture takes the access of its effect (`share fn` parameter or
  mutating closure = share). One consequence over the probe design: a `share self`
  method call inside a literal now makes a share capture (it used to fail IR
  validation).
- A capturing literal is valid only as a direct argument of a `borrow fn`/`share fn`
  parameter or as the initializer of an immutable `let` (`ClosureContext`); the
  `let` local is second-class (`Binding::closure`): usable only as a callee or as
  an argument to such a parameter. The mode needed (read = Borrow, any share =
  Share) is checked against the parameter (TE017).
- IR: `InstructionKind::ClosureNew { function, captures }` (captures are
  `Borrow`/`Share` references of the creator's places, one per trailing capture
  parameter); output is a `Function` value of the declared signature. Loans:
  the closure value's provenance is the union of its captures' provenance (also
  through `Assign`/`Capture`/`Copy`/edges), and borrowing a closure local to pass
  it keeps those loans; hence BE005 while live and access after the last use.
  `address_taken` carries capture counts so an indirect call reaches closures of
  the declared signature; String writes through a closure link to the creator's
  owner (`ShareWrite`).
- Wasm convention (one for all indirect calls): type = declared parameters, an i32
  environment pointer, then the hidden aggregate-result pointer. Table entries are
  thunks: a plain function's thunk drops the environment; a closure's loads one
  capture address per capture from the environment and calls the lifted function.
  The environment is a frame cell of 4 bytes per capture in the creator's frame
  (`FrameLayout::closures`), pointer in the high word of the i64 value. No heap.
- List parameters/results in function types are allowed; calls through function
  values follow direct-call rules (IR gates removed, checker `value_call`).
- Syntax: `=> place op= expr` is a Unit assignment body.
- Casts read through a reference (`captured as i32`).
- Not done: built-in `each` methods on arrays/Lists (users write helpers such as
  `visit(f: share fn(i32), n)`); explicit `.borrow()`/`.share()` on a function
  argument; owned (escaping) closures stay H5.
- Tests: `crates/memobits-cli/tests/h2_closures.rs` (18); guide `functions.mb`
  (+5 tests, 134 total). H1 negatives for captures, borrow/share fn parameters
  and List function types were replaced or removed.

### Shipped H3 details (2026-11-25)

Facts about the shipped generics step; the Stage 4 decision is unchanged.

- Syntax: `where T: A + B, U: C` (the parser emits one `WhereBound` per interface;
  a repeated parameter name is fine). Declarations are validated once
  (`validate_template`): every bound names a declared type parameter, bounds take
  no type arguments, const parameters have type `u32`, no parameter is declared
  twice (TE007 at the declaration). The old "one parameter, one bound, direct
  `T`" gate (`supported_generic_function`) is gone.
- Inference (`types/generics.rs`, shared by calls and function values): the
  written parameter types are matched against the argument types
  (`Checker::unify`): a bare parameter, `array<T, N>`, `List<T>`, `T?`,
  `T ! E`, tuples, nominal generics (`Pair<A, N>`, via the type table's generic
  origin and arguments) and function types (access modes must agree) bind type
  and const parameters; `borrow`/`share` references are stripped before binding.
  Arguments are checked in written order. An argument whose parameter type still
  mentions an unbound parameter is checked without an expected type; a function
  literal, a generic function named as an argument, or a parameter type that
  projects (`T::Rhs`) waits for a second pass. A function literal gets the
  function type with the still-open result as `Ty::Error` (its body decides
  the result); an open parameter type is TE002. After the arguments, the
  expected result type fixes parameters nothing else bound; an expected result
  also types a literal argument (`let x: u32 = fold(xs, 0, ..)`). A parameter no
  argument or expected type fixed is TE002 "cannot infer the type argument 'U'
  of generic function 'f'" (a diverging argument keeps its old message). Explicit
  type arguments at a call (`f<i32>(x)`) do not exist.
- Evidence: one `GenericEvidence { parameter, interface, candidate }` per bound,
  selected per bound at the call: the evidence the enclosing specialization
  forwards (same interface and target), else the one visible implementation
  ("no visible implementation of 'I' for X satisfies generic bound 'T: I' of 'f'"
  or "ambiguous generic evidence for bound 'T: I'; candidates: ..."). Evidence
  is selected as soon as its parameter is bound, so projections in later
  parameter types resolve. A method call on a value of a type parameter selects
  its interface with `of` (unchanged); without `of`, a method provided by one
  bound says to use `of`, one provided by two bounds names both
  ("method 'm' is provided by the bounds 'T: A' and 'T: B'; select one with `of
  Interface`", TE024).
- Specialization key: template identity + the specialized function type +
  the sorted type and const arguments + the evidence of every bound in bound
  order (module and span of each implementation). The existing 256 cap applies
  (TE007 "generic specialization limit exceeded").
- Projections: `T::Name` resolves through the evidence of `T`'s own bounds (not
  by target type). When several bounds define `Name` it is TE008 "associated type
  'Name' of 'T' is ambiguous: bounds ... both define it"; the qualified form
  `T::Interface::Name` (interface by its last path segment) selects one.
  Anything deeper (`T::A::B::C`, or `T::X::Y` where `X` is no bound) stays NE008
  / TE008 "nested associated type projection ... is not supported".
- Generic function values: the expected function type is matched against all
  parameters and the result (several parameters, bounds with evidence); a
  generic function named as an argument of a generic parameter of function type
  is specialized after the other arguments fixed its parameter types
  (`apply2(first_of, 5, true)`).
- Types and methods: several type and const parameters on nominal types work
  (`P<A, B, const N: u32>` and its `extend` methods). Methods with their own
  type parameters are SE002; `type X<T> where T: I` is still "not implemented
  yet"; a const parameter is not a value expression (`[x; N]`, `0..N`). (All three are
  lifted by F4, see "Shipped F4 details".)
- Body checking is unchanged: each specialization is checked with the concrete
  types, so there are no generic-body diagnostics beyond the concrete ones.
- Argument checking against a still-open parameter type skips only the type
  comparison (done after inference); access rules (`.borrow()`/`.share()`)
  apply as in direct calls. List argument rules for open parameter types are
  checked by the IR validation instead of the front end.
- Changed tests: `cli.rs` (the `nested<T>(T?)`/`unsupported<T, U>` gate checks
  became a working call and a TE002; five "constrained ...Assign remains gated"
  checks assert acceptance of the uncalled generic).
- Tests: `crates/memobits-cli/tests/h3_generics.rs` (16): several type/const
  parameters with several bounds and forwarding, specialization keys (types,
  consts, evidence across two modules), borrowed/shared parameters and compound
  types, higher-order helpers over arrays/Lists (closures capturing, `share fn`),
  projections through several bounds, generic function values, owners through
  generic code (String, struct, nested struct, List, `T?`) under capped memory
  (initial + 1 page, 4,096 iterations x 1,024 bytes; source and Wasm), cross-module
  evidence, and the negatives (missing and ambiguous evidence, ambiguous method
  and projection, nested projection, uninferred parameter, conflicting types and
  consts, invalid declarations, wrong arity/kind of type arguments, the 256 limit).
  Guide: `generics.mb` (+5 tests, 139 total); example `generics-operators` (6 tests).

### Shipped H4 details (2026-11-25)

Facts about the shipped `Box<T>` step; the Stage 4 decision is unchanged. The
implementation notes are in `docs/design/box.md`.

- Import and layers: `use alloc::Box;` (same rules as `List`: the alloc layer,
  `alloc = false` is ME012, a missing import is NE003 `unknown type 'Box'` with
  the note ``add `use alloc::Box;` to use Box``, and a missing import for the
  constructor is NE001 with the same hint). The `alloc` virtual module now
  declares `List` and `Box`. After parsing, an applied `Box<T>` in a module that
  has `use alloc::Box;` is rewritten to `alloc::Box<T>` (the same pass as
  `Self`), so a module that does not import it may still declare its own
  `type Box<T> { .. }`.
- Surface: `Box(value)` moves `value` into a fresh box (any admitted `List`
  element: primitives, strings, structs, tuples, enums, arrays, Lists, function
  values, boxes; never a reference or `Unit`). `unbox(b) -> T` is a built-in
  like `drop` / `replace` (an in-scope function, import or value of that name
  takes precedence): it consumes an owned box and moves the value out. Moving
  a box out of a field or element is the usual partial-move TE022; use
  `replace`, `swap` or `unbox(replace(place, Box(..)))`.
- Ownership: a box is a single owner. Moves, scope exit, reassignment
  (`b = Box(..)`), `drop(b)`, early returns, `replace` / `swap` on box places
  and overwrite of box fields and elements release the box block and the
  value's owned contents exactly once. Loans on the contents are loans on the
  box (BE005 for moving or writing the box while one is live). `Box<T>`
  works as a field, array element, `List` element, `T?` / `T ! E` payload,
  tuple element, enum payload and generic argument.
- Representation (interim, replaced by H4b below): the checker has a distinct
  `Ty::Box`; H4 stored it in the IR as a one-element `List<T>` (12-byte List
  descriptor, not one pointer word). H4b gave Box its own IR type and one
  pointer word; see "Shipped H4b details".
- Auto-deref: a field access, index, method receiver or `match` scrutinee of
  type `Box<T>`, `borrow Box<T>` or `share Box<T>` (any number of nested
  levels) addresses the boxed value. `b.f`, `b[i]`, `b.m()` (receiver modes
  apply to the boxed place; a by-value method consumes the box), `b.f = v` and
  `b.f += v` (the box must be `var` or a `share` parameter), `replace(b.f, v)`
  and `swap(b.f, c.f)` work. `match b { .. }` on an owned box consumes it and
  moves payloads out; on a borrowed box or a place it lends the value in place.
  A refutable pattern on a payload of type `Box<T>` sees through the box in an
  in-place match (`Node(Node(_, v, _), _, _)`); in a consuming match it is
  TE017 (bind the box and `unbox` it). A `.borrow()` / `.share()` of a box
  passed to a parameter of the content type lends the content.
- Recursive types: the by-value recursion check (TE026) is unchanged and only
  follows fields, payloads and arrays, so recursion through `Box<T>`, a `T?`
  of a box or a `List` of boxes is accepted and direct recursion is rejected.
  Wasm releases a type that reaches itself with one generated function per
  type (`recursive.rs`); in H4 that function recursed once per node and
  trapped with a call-stack error for chains of hundreds of thousands of nodes
  (fixed by H4b: the release is iterative).
- Limits (H4; the first two are lifted by H4b): the IR representation above
  (single-word layout not done);
  built-in String and List methods (`len`, `push`, ...) do not auto-deref (bind
  or `unbox` first; user methods do); a payload bound by an owned `match`
  cannot be passed directly as an owned call argument (`f(unbox(rest))`, the
  existing List rule); a consuming match or by-value method consumes one box
  level; box contents cannot be a reference or `Unit`; a Box cannot cross the
  entry ABI.
- Tests: `crates/memobits-cli/tests/h4_box.rs` (18): construction, fields,
  assignment, methods, indexing, `replace`/`swap`, contents of every kind,
  containers, linked list and binary tree (insert, sum, depth, nested
  patterns), deep recursion, capped-memory repeated build-and-drop (memory
  capped to initial + 1 page, 4,096 iterations) for trees, box contents and
  owned matches, reassignment/`drop`/early return, a mutation check that keeps
  trees and must trap with "guest heap allocation failed", and the negatives
  (missing import, `alloc = false`, direct recursion, use after move, moving
  out of a box field, immutable write, loans, nested-pattern gate). Guide:
  `collections.mb` (+2 tests, 141 total); example `examples/apps/tree`
  (4 tests).
### Shipped H4b details (2026-11-25)

H4b completes the H4 `Box<T>` step. The Stage 4 decision is unchanged: this
records the facts of the single-pointer-word box and the iterative release.
Implementation notes are in `docs/design/box.md` and `docs/design/wasm-backend.md`.

- Representation: the IR has its own type `Type::Box(T)`. A box is one `i32`
  pointer (4 bytes, 4-aligned) to a heap block whose payload, after the 8-byte
  block header, is one value with T's layout; there is no list descriptor,
  length or capacity. An empty (never filled or moved-out) box is the null
  pointer. Struct fields, enum payloads, array elements, tuples and locals
  therefore shrink: a `{ Box<i32>, i32 }` struct is 8 bytes (16 with a
  `List<i32>` field), an `array<Box<i32>, 4>` field 16 bytes (48 for Lists);
  checked by `a_box_occupies_one_pointer_word_where_a_list_occupies_a_descriptor`
  in `memobits-wasm`. The block of a box is exactly header plus T (a one-element
  List block used to be rounded up by the List growth policy).
- Owner rules are unchanged: a box is a heap owner in every owner predicate
  (moves, scope exit, reassignment, `replace`, `swap`, `drop`, early returns,
  loans, `T?` / `T ! E` / tuple / array / List / enum-payload / generic /
  function-value compositions). IR instructions: a Box local is built with
  `EmptyList` (empty box) and `ListPush` (reserve the block and move the value
  in), emptied with `ListPop` (move the value out, release the block) and
  addressed with `ElementAddr` at the constant index 0 (the address of the
  value; no bounds check, a live box always holds one). These share the
  List owner-slot instructions deliberately: only their Wasm emission and type
  checks differ for `Type::Box`. All H4 tests pass unchanged.
- Iterative release: releasing a recursive owner type no longer recurses per
  node. A recursive type gets one release function that walks the value's own
  fields inline and *defers* every `Box` or `List` position whose element
  mentions a recursive type onto an intrusive worklist (one Wasm global head
  per deferral kind); one shared `drain` function pops items in a loop. The
  links live in storage that is already dead: a deferred box item links
  through the free-list word of its own (still allocated) block header, a
  deferred List item through the `data` word of its descriptor (a heap List
  has `data == allocation + 8`, restored when popped). No allocation happens
  during release, so releasing never fails and needs no memory beyond the
  structure. The call-stack depth of a release is constant (user code,
  `release_T`, `drain`). A million-node linked list, degenerate left/right
  trees of 100,000 nodes, a 200,000-deep `List`-of-children chain, mutually
  recursive types and balanced trees release without trapping; building such
  structures in user code that recurses is still bounded by the call stack.
- Built-in method auto-deref: `len`, `get`, `contains`, `index_of`,
  `is_char_boundary`, `byte_at`, `scalar_at` (reads, through `borrow`, `share`
  or owned boxes) and `push`, `pop`, `clear` (writes: the box must be a `var`
  or a `share` parameter) act on the String or List inside a box, at any box
  depth, when the receiver is a named local, field or element holding the box
  (a box returned by a call must be bound first, TE017). `push_str` and `concat`
  do not see through a box.
- Consuming-match nested patterns through a box payload (TE017) stay rejected.
  Moving owned parts out of a box's content while the block remains needs
  partial-move tracking inside the box that the owner model does not have; the
  new representation does not change that. In-place matches are unchanged.
- `[prelude]`: `Box` cannot be mapped (`Box='alloc::Box'` is ME005 because the
  virtual `alloc` module declares the name); `List` behaves the same, and an
  alias of an alloc type (`Seq='alloc::List'`) does not give the alias the
  built-in methods, so no prelude support was added. Import with `use alloc::Box;`.
- Allocator note (not changed): released blocks are reused first-fit from one
  free list, so a program that frees many blocks of one size and then
  allocates many larger ones scans the whole list per allocation. Box blocks
  are now exact-size, so mixed shapes in one run can expose this; it is
  unrelated to the release depth.
- Exported Wasm signatures cannot use `Box` (own diagnostic, "the external Box
  ABI is not defined").
- Tests: `crates/memobits-cli/tests/h4_box.rs` (25: the 18 H4 tests unchanged
  plus million-node list, degenerate/other recursive shapes, balanced tree,
  capped-memory long-list build/drop and its mutation check, built-in method
  auto-deref and its negatives); `memobits-wasm` layout test; guide
  `collections.mb` (+2 tests, 143 total).

### Shipped BK1 details (2026-11-25)

Backend-only change; no language or ABI change. Facts:
- The guest allocator's single first-fit free list is replaced by segregated size classes: 52 classes (four-byte steps to 32 bytes, then four per octave up to 65,536 bytes) with a non-empty bitmap and one list head per class in a 216-byte static table, plus the old exact-size list for blocks above 65,536 bytes. Small requests round up to their class size and take the lowest non-empty class at or above it; a small request with no small block available reuses the head of the large list before growing. Alloc and free are O(1) for small sizes. No splitting or coalescing was needed to keep the capped-memory tests (initial + 1 page) passing.
- Block header format unchanged (capacity at 0, next at 4; payload at +8), so String/List/Box descriptors and the H4b release worklist (which reuses `next` of still-allocated blocks and never touches `capacity`) are unchanged. A small block's capacity is now always an exact class size, so a freed block returns to the class it was taken from.
- Behavior unchanged: allocation failure still returns zero without changing any list (trap "guest heap allocation failed"). Programs without heap use are byte-identical; heap programs differ (+453 bytes of code, the table) and produce identical output.
- Pathology fixed: freeing 60,000 small blocks and then allocating 60,000 100-byte strings took 9.1 s (source run, debug build, no fuel limit; the default 10 billion fuel budget was exhausted) and now takes 0.05 s.
- Tests: `crates/memobits-cli/tests/bk1_allocator.rs` (5).

### Shipped H5 details (2026-11-25)

Facts about the shipped owned (escaping) closures; the Stage 4 decision is unchanged.

> **Superseded by H5b (see "Shipped H5b details" below).** The interim parts of this
> section no longer hold: the per-type representation switch and its whole-program
> discovery, the dynamic mutation rule (trap 14, `ClosureReadOnly`, the bit-31
> flag), and copying of plain function values (a `let` bound to a function name
> or a non-capturing literal is now move-only, like every function value). The
> rest (move captures, heap environment, release, `alloc = false`, positions,
> lending) is unchanged.

- **Where a closure is owned.** An anonymous function with captures whose expected
  type is an owned `fn(...)` (not a `borrow fn`/`share fn` parameter) is an owned
  closure: a function result or tail, an annotated `let` or `var` (`let f: fn(i32)
  -> i32 = fn(x) => x + n;`), a struct field, enum payload, tuple/array/List element,
  `T?` payload or an owned argument. No keyword: if a closure is used in such a
  position all its captures are moves. An unannotated `let f := fn(..) captures` stays
  a second-class closure (H2); using it where an owned value is needed is TE017
  "second-class". Without an expected function type a capturing closure stays
  second-class too. A closure without captures is a plain function value everywhere.
- **Captures.** Captured primitives (and plain function values) are copied; a String,
  List, Box, struct, enum, or owned closure is moved and the enclosing variable is
  unavailable afterwards (BE001, the ordinary move check). The closure owns its copy:
  a captured primitive keeps the value it had when the closure was created. A
  `borrow`/`share` parameter, a reference binding of a non-copyable type or a
  second-class closure cannot be captured by an owned closure (TE017 "captures by
  move"). A nested owned closure may copy a primitive out of its parent's environment.
  The closure body is the lifted function of H2 (captures are trailing `borrow`/`share`
  reference parameters); only the creation and the thunk differ.
- **Mutation rule.** The closure value owns the environment, so mutating a captured
  variable (assignment, `push`, `push_str`, a `share` call, calling a captured `var`
  closure that mutates) changes the closure's own copy. Whether a closure mutates is
  not part of the type, so the rule is dynamic: a closure that mutates its
  environment (any share capture) carries a flag; a call through a *mutable place* is
  always allowed (a `var` local, a field or element of one, a `var` parameter, a
  `share fn` parameter, or a temporary such as `make()()`); a call through an
  immutable place (a `let`, an owned parameter, a field of a `let`, a `borrow fn`
  parameter) traps with reason 14 "a closure that mutates its environment was called
  through an immutable place; hold it in a `var` or a `share` parameter" when the
  closure mutates, and runs normally when it only reads. Lending to a `share fn`
  parameter from an immutable place is checked at the lend site the same way. A `var`
  closure captured by another owned closure makes the new closure mutating.
- **Ownership and copying.** An owned function type that has owned closures anywhere in
  the program (whole project) is an owner type: its values are moved, stored,
  returned, replaced (`replace`) and dropped like any String-owning aggregate; the
  environment and everything it owns is released exactly once (the shared owner
  predicates apply, recursive environments use the H4b iterative release; a
  100,000-deep chain of closures drops). Copying a closure with an environment is
  rejected by the move check (BE001 for `let g := f; f(..)`, passing it twice, storing it
  twice), and `List::get` / reading a closure out of a field are TE022 as for any owner;
  call in place (`list[i](x)`, `holder.run(x)`) instead. Non-capturing function values
  stay copyable: a function name or non-capturing literal is a fresh value at each use,
  and an immutable `let` bound to one is copied by rebuilding it. Function types
  without owned closures keep the H1 rules exactly (copy like a primitive, `get`
  works). Consequence to know: the representation is chosen per exact function type,
  by whole-program discovery, so writing the first capturing closure of `fn(i32) -> i32`
  changes the copy rules of every value of that type (plain function parameters used
  twice need a plain `let`, `get` becomes TE022). Assigning to a whole owner local
  (`f = make()`) was the general struct-owner limitation (TE018; superseded by F4, which
  assigns whole owners, see "Shipped F4 details").
- **Lending.** Passing an owned closure to a `borrow fn` or `share fn` parameter lends
  it without moving (the argument is written bare); the closure is still usable
  afterwards. Second-class closures cannot become owned values (TE017).
- **Representation.** The checker runs in passes (`types/owned_fn.rs`): pass one finds
  the function types with owned capturing closures, later passes represent those types
  as a wrapper struct `{ call: fn, env: Box<Env> }` (a tuple-module IR struct named
  after the type, so every tuple/struct owner rule applies) and `Env` is an enum with a
  `Plain` variant and one variant per closure literal whose payload is the captured
  values. `ClosureOwned { function, env, enum_ty, variant, mutating }` builds the
  callable word from the box; calls read field 0 in place. The environment is a
  heap block (alloc layer): `[build] alloc = false` rejects an owned closure with
  captures with TE033 naming the setting; plain and non-capturing function values and
  H2 closures still need no heap. The table thunk adds the variant field offsets to the
  environment pointer; release is the ordinary type-directed release of the enum.
  Exported/entry signatures cannot contain function values (LE900).
- **Loans.** A second-class closure stored in a wrapper local (an owned function type
  that also has a `let`-bound H2 closure) keeps its capture loans (`StructNew` and
  `Borrow` carry provenance).
- Tests: `crates/memobits-cli/tests/h5_owned_closures.rs` (16: typical uses, every
  owned position, generics, copy/move semantics, plain copies, move and copy
  negatives, borrowed-capture negatives, `alloc = false`, mutation rule through
  every kind of place with source and Wasm traps, per-type representation, lending, capped-memory creation
  and drop of 4,096 rounds with heap captures in 12 positions plus the mutation
  check, 100,000-deep chain). Stale H1/H2 negatives updated. Guide `functions.mb`
  (+5 tests).
- Not done: closures capturing by reference into a heap environment (not planned: a
  heap environment owns, it does not borrow); a statically visible mutating flag in
  the type; copying a closure explicitly (no `clone`); `drop(f)` of a whole
  closure (scope end and `replace` release it, as for every struct owner); unannotated
  `let f := fn(..) captures` becoming owned by later use.

## Owned closure mutation and function value ownership (2026-11-25, user chose option C)

- `var fn(T, …) -> R` is the type of an owned function value whose
  environment may change when it is called (a closure that mutates its
  captured state). It can only be called through a mutable place (`var`
  local, `share` parameter, field or element of a mutable owner).
- `fn(T, …) -> R` values never mutate their environment: an owned closure
  whose body mutates a capture is a compile error in a `fn(...)` position,
  with a note suggesting `var fn(...)`. A `fn(...)` value may be used where
  a `var fn(...)` is expected; the reverse is rejected.
- Lending: `fn` values may be lent to `borrow fn` and `share fn` parameters;
  `var fn` values only to `share fn` parameters.
- All owned function values (`fn` and `var fn`) follow one rule everywhere:
  they are move-only owners with a nullable environment (null = no heap,
  trivial release). Calling through a place and lending borrow the value and
  do not move it. A function name or a non-capturing literal produces a
  fresh value at each mention. This replaces the interim per-type switch and
  the runtime check (trap 14), which are removed.

### Shipped H5b details (2026-11-25)

Facts about the shipped uniform function value ownership and `var fn(...)`; the
decision above ("Owned closure mutation and function value ownership") is implemented
as written.

- **Representation.** Every function type is the wrapper struct `{ call, env }` (an IR
  struct named after the signature, in the tuple module): `call` is the callable word
  (table slot plus environment word) and `env` a `Box` of a compiler-made enum with a
  `Plain` variant and one variant per owned closure literal of that signature. It does
  not depend on any other code: the whole-program discovery passes (`types/owned_fn.rs`)
  are gone and the wrapper is interned on first use by the checker. A function name,
  a non-capturing literal and a second-class closure have an empty `env` box (null
  pointer, no heap); releasing such a value is the ordinary empty-box check.
  `fn(...)` and `var fn(...)` of one signature share the wrapper and the environment
  enum (`var` is checker-only), so `fn` to `var fn` needs no conversion code. Plain
  function values need no allocator code beyond the empty-box release; `[build] alloc =
  false` still rejects a closure with captures (TE033).
- **Ownership.** Function values are move-only owners everywhere: `let g := f;` moves
  `f`, passing to an owned parameter or storing twice is BE001, a field or element is
  read only in place (`holder.run(x)`, `list[i](x)`, `loop f in array` binds a borrow)
  and leaves a field only through `replace`/`swap`, a List through `pop`/`replace`/`swap`
  (`List::get` and a field read are TE022 like any owner). Calling through a place and
  lending to `borrow fn`/`share fn` borrow, they do not move. Each mention of a function
  name or a non-capturing literal is a fresh value, so `apply(inc, 1)` twice needs no
  copy. Assigning a whole function value (`f = g;`) was TE018 with a note to use
  `replace(f, g)`; F4 makes `f = g;` work (see "Shipped F4 details").
- **`var fn`.** `var fn(T, ..) -> R` parses in every type position (parentheses as for
  `fn`: `(var fn() -> i32)?`, `List<var fn() -> i32>`, fields, payloads, generics,
  results) as the AST path `\0fn`, `var`. An owned closure that mutates a capture
  (assignment, `push`, a `share` call, calling a captured `var fn`, lending it to a
  `share fn`) is accepted only where the expected type is `var fn`; in a `fn` position it
  is TE017 "this closure changes its captured state ('x')" with a help suggesting
  `var fn(...)`. Calling a `var fn` value needs a mutable place (a `var` binding or
  parameter, a `share fn` parameter, a field or element of a mutable owner, a
  temporary); anything else is TE004 at compile time. `fn` converts to `var fn` at the
  top level of a position (not inside `List<..>` or other type arguments, which are
  invariant); the reverse is TE002 with a help. Lending: `fn` to `borrow fn` and
  `share fn` (any lender); `var fn` only to `share fn` and then from a mutable lender
  (TE004), to `borrow fn` is TE017. A `borrow`/`share` parameter is written `borrow fn`
  / `share fn`; `borrow var fn` is TE017. A `share fn` parameter may call the value it
  is lent, so passing it on to a `borrow fn` stays an error.
- **Removed.** The run-time mutation check: IR `ClosureReadOnly`, the `mutating` field of
  `ClosureOwned`, trap reason 14 (`MutatingClosure`) and bit 31 of the slot word with
  the per-call mask. Trap codes above 13 are unused again. Wasm output for programs with
  no function values is unchanged.
- **Known limits.** A `var fn` held in an enum payload or `T?` is moved and dropped but
  cannot be called through a `match` binding (bindings are read-only places); take it
  out into a `var` first (`replace`, `pop`). `var fn` cannot be a `borrow`/`share`
  parameter type. Unannotated `let f := fn(..) captures` stays second-class (H2).
- Tests: `crates/memobits-cli/tests/h5b_function_ownership.rs` (8: per-module
  independence, move-only plain values, `var fn` positions and mutable-place calls,
  mutating closure in `fn` position, coercion and lending matrix, capped-memory run of
  4,096 rounds with heap environments and its mutation check); `h1_function_values.rs`,
  `h5_owned_closures.rs` and the guide `functions.mb` updated to the move-only rule
  (lending through `borrow fn`, `replace`, in-place calls). Guide: 149 tests.

### Shipped F4 details (2026-11-25)

Facts about the shipped follow-ups; no new decisions (they implement the accepted rules
"assignments finish evaluating the RHS before replacing an owner", S2 field replacement,
R1 owning overwrite and the H3 generics step).

- **Whole-owner local reassignment.** `x = value` on a `var` local, or on a `share`
  parameter, of a String-owning struct, record, tuple or enum (including enums with heap
  payloads, `Box` payloads and function values) and of a function value (`fn` / `var fn`,
  with or without a captured environment) is accepted. `String`, `List`, `Box` and array
  locals keep their existing paths (unchanged output). Order: the right-hand side is
  evaluated completely into a hidden owner local first (staged exactly as for
  `replace(place, value)`), then the old value is released exactly once and the staged
  value is moved in. The RHS may read the old value through a borrow whose loan ends
  first, or move it (`acc = combine(acc, x)`; the assignment initializes the moved-from
  local again). An early exit (`return`, `break`, `continue`) while the RHS is evaluated
  leaves the local untouched and releases the staged value. `x = x` is accepted. A local
  with a live loan is BE005 ("cannot assign to `x` while it is borrowed/shared"). The target
  must be mutable (TE004 for `let` and for an owned non-`var` parameter) and the value of
  the same type (TE002).
- **Lowering.** For a non-parameter local the staged value is installed with the IR
  `Assign { initialize: false }`: the ownership pass makes the local available again, and
  the Wasm backend releases whatever the local still owns (a moved-out value is cleared, so
  this is a no-op), copies the staged descriptor in and clears the source. For a `share`
  parameter the exchange form of R1 is used (`SwapPlaces`, then the staged old value is
  released at the end of the statement). IR validation (`scoped_string.rs`) now accepts a
  struct or enum `Assign` with `initialize: false` on a mutable non-parameter local. A stored
  `var h := owner.share()` handle keeps its store-through-reference path.
- **Still rejected.** A `share fn(...)` parameter cannot be reassigned as a whole (it lends
  the caller's function value): TE018 "a `share fn` parameter lends the caller's function
  value and cannot be reassigned as a whole yet". Pre-existing limits found while testing,
  unchanged: a struct with an `array<string, N>` field built from a named array local, and
  a struct with an array-of-String field read through `shelf.items[i]`, fail IR validation
  (TE018) with or without reassignment.
- **Const generic parameters as values.** Inside a generic function, type or method with
  `const N: u32`, a name `N` that no local shadows is a `u32` value of the specialization
  being checked: arithmetic, comparisons, casts, `loop i in 0..N` and `0..=N`, interpolation
  (`"{N}"`), closure bodies, call arguments and `[x; N]` repeat counts. The parameter
  shadows a module constant of the same name; a local of the same name shadows the
  parameter; `N = ..` is TE004 "cannot assign to const generic parameter"; outside any
  generic item `N` is NE001. Implemented by `PathTarget::Const(value)` (a path use with the
  specialization's value) and `Checker::generic_consts` for the repeat count.
- **Method-level type and const parameters.** An inherent method (including methods in a
  trailing `extend { .. }` of a generic type) may declare `fn m<U, const K: u32>(self, ..)
  where U: B`. Interface declarations and `extend T of I` methods still reject them (SE002).
  Calls infer the method's own parameters exactly like a generic function (argument
  matching in written order with function literals last, the expected result, one evidence
  per bound; the shared `Checker::infer_call` in `types/generics.rs`) starting from the
  receiver type's arguments, which stay fixed. A method parameter may not repeat a parameter
  of its type (TE007). The method is specialized per call: the key is the receiver type, the
  specialized function type, the type and const arguments of both lists and the evidence of
  every bound (the existing 256-method cap applies, TE007). Generic methods get no eager
  function id; unused ones are not checked until called.
- **`where` bounds on type declarations.** `type Pair<T> where T: A + B { .. }`: each bound
  must name a declared type parameter, without type arguments (TE007 at the declaration).
  Every written instantiation is checked: let annotations, parameter and result types,
  struct fields, enum payloads, struct literals, nested generic instances and the
  specializations of generic functions. A missing or ambiguous implementation is TE007
  "no visible implementation of 'I' for X satisfies bound 'T: I' of type 'Pair'". The
  evidence selected at instantiation (the one visible implementation, or the evidence the
  enclosing specialization forwards) is carried by the specialization of the type's methods,
  so methods may use `T::Rhs` / `T::Output` and operators on `T`. Evidence follows the
  function rule: primitives have no interface implementations, so `Pair<u32>` with
  `T: Add` is the "missing implementation" error.
- Tests: `crates/memobits-cli/tests/f4_followups.rs` (8: every owner kind, loops and early
  exits, edge cases, a capped-memory run of 4,096 iterations with 4,096-byte strings, loan
  and type negatives, const values, method parameters, type bounds). Its mutation check
  (skipping the old-value release in the Wasm `Assign` makes the capped run fail with
  RE007) is in `.local-design/logs/f4-mutation.log`. Stale negatives updated: `cli.rs`,
  `d2_owned_struct_transport.rs`, `d2_nested_owner_transport.rs`,
  `d2_record_owner_transport.rs`, `h5b_function_ownership.rs`. Guide: 154 tests.

## Source formatting (2026-11-25, architect default; stage 5 step 1)

- `mb fmt` formats Memobits sources to one canonical style, derived from the
  style already used by the runnable guide: 4-space indentation, opening
  braces on the same line, one space around binary operators and after
  commas/colons, one blank line between top-level items (blank lines inside
  bodies are preserved but collapsed to at most one), maximum line width 100
  with breaking of long argument/parameter/field lists one item per line
  with trailing commas, and all comments preserved in place.
- Formatting never changes meaning (same syntax tree modulo positions) and
  is idempotent. `mb fmt --check` reports files that would change and exits
  non-zero without writing.

### Shipped S5-1 details (2026-11-25)

- `mb fmt [--check] [--project PATH | FILE...]` is shipped; rules, examples, guarantees and
  limits are in [formatting.md](formatting.md), usage and exit codes in the CLI README
  ("Formatting"). Exit 0 when nothing needs formatting (or all files were rewritten), 1 when
  `--check` finds a file that would change, on a syntax error (the file is untouched and the
  SE diagnostics go to stderr), on a failed self-check (PE008) and on usage or I/O errors.
- Implementation: `memobits_syntax::format` (`format_source`, `same_syntax`,
  `syntax_fingerprint`). It is token-driven, not a pretty-printer over the syntax tree, because
  the tree is lowered (`try` becomes `match`, `Self` is resolved, grouped `use` lists are
  expanded, parentheses are dropped) and printing from it could not reproduce what the user
  wrote. Comments are read from the gaps between tokens and attached to tokens; the tree is
  used only to tell generic `<`/`>` from comparisons and to find item starts. Every result is
  verified (parses, same tree modulo spans, same comments, second pass identical) before it is
  returned.
- Interpretations of the binding style, for the architect to confirm or overrule:
  1. "One blank line between top-level items" is applied to every pair except two adjacent items
     that were each written on one line with no blank line between them (runs of `use`, one-line
     functions and types, as in the guide); a blank line the source had is kept.
  2. Inline bodies are kept inline: `fn f() -> i32 { 1 }`, `match x { A => 1, B => 2 }`, struct
     literals and arrays written on one line stay on one line while they fit in 100 columns; a
     body, `match`, struct, record or array written with a newline after its opening bracket
     stays expanded. An inline `if`/`else` chain that does not fit is expanded block by block.
  3. In an expanded `match`, expression arms end with a comma (including the last) and arms whose
     body begins with `{`, `if` or `match` take none. This removes the `},` the guide and the
     enf-lexer example used in nine places.
  4. `where` stays on the line the source put it on.
  5. A trailing comma in a one-element tuple or tuple pattern is preserved; a parenthesized
     single expression never gains one.
- Applied to the examples: `examples/guide`, `examples/topics/*`, `examples/apps/*` and
  `examples/analysis/*.mb` are formatted (formatting-only change; 15 files changed, mostly blank
  lines between multi-line items, trailing commas in broken lists and `match` commas).
  `mb run` and `mb test` output (stdout, stderr, exit status) of every example is byte-identical
  before and after (`.local-design/logs/s5fmt-before` vs `s5fmt-after`); the only output that
  differs is the byte count in `mb check` for two projects, because the `memobits.traps` custom
  section stores source positions (code, data and every other section are byte-identical). The
  guide still runs 154 tests. `examples_documented.rs` now fails when any example is not
  formatted. `docs/design/proposed-language-guide.mb` (a historical proposal) does not parse and
  is not formatted. Memobits sources inside Rust test files are not reformatted.
- Tests: `crates/memobits-syntax/tests/format_corpus.rs` (4: 42 repository files, 2,712 Memobits
  programs embedded in Rust tests, each program re-flowed five ways, and 1,401 programs with
  comments inserted between arbitrary tokens twelve ways, all idempotent, tree-preserving and
  comment-preserving), `format_cases.rs` (23), `crates/memobits-cli/tests/s5_fmt.rs` (6) and
  `examples_documented.rs::every_example_is_formatted`.
- Known limit: dense inline block comments can push a line across the width limit between the
  first and second pass; the self-check then reports PE008 and leaves the file untouched.

<a id="execution-engines-and-the-component-model-2026-11-26-user-decision-not-implemented-yet"></a>

## Execution engines and the Component Model (2026-11-26, user decision)

> Implementation status: S5-2a is complete. S5-2b and S5-2c have shipped first slices; other aggregate mappings and additional host capabilities remain future work. See the [roadmap](../roadmap.md) for current limits.

- Two engines are used, selected by command rather than by a flag:
  - `mb run` and `mb test` use **wasmi** (interpreter: instant start, fuel
    limits, detailed trap reports) for the development loop;
  - `mb build` produces core artifacts and, with `--component`, supported
    WebAssembly Components with their WIT world;
  - `mb exec` runs built artifacts and supported Components with **wasmtime**
    (Cranelift JIT and the Component Model).
  Core `.wasm` behavior is covered by engine parity tests for `mb run` and
  `mb exec`. wasmtime is built behind a
  Cargo feature that is enabled by default for `mb`.
- The Component Model is the external ABI direction: supported exported
  signatures map scalar types and selected error outcomes; the broader mapping
  plan includes `string`→`string`, `List<T>`→`list<T>`, `T?`→`option<T>`,
  `T ! E`→`result<T, E>`, structs→`record`, enums→`variant`, tuples→`tuple`,
  with names in kebab-case. This broader mapping is not fully implemented.
- The CLI console capability is available through a WIT import. Additional
  host capabilities mapped from `[host] profile` remain future work.
- Original planned order and current status: (1) `mb exec` with wasmtime and
  engine parity tests — complete; (2) WIT type mapping and
  `mb build --component` — partial, with scalar components and a limited
  application outcome slice shipped; (3) host capabilities as WIT imports —
  partial, with the CLI console import shipped. Other aggregate mappings, derived
  errors, Unit outcome payloads, library outcome exports and additional
  capabilities remain gated.
