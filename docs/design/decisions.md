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
  outputs with `.local-design/g4/equivalence.sh`). The AST node is
  `ExprKind::Interpolation(Vec<InterpolationPart>)` with `Text` and
  `Value(Path)` parts.
- Typing: the identifier is read like any value read (NE001 unknown name, BE001
  after a move, BE005 while it is exclusively shared). Supported value types
  are all integer widths, `bool`, `char` and `string` (also through
  `borrow`/`share` parameters). Floats are rejected with TE017 "formatting
  floating-point values in string interpolation is not supported yet": a
  shortest round-trip (Rust `Display`) float formatter needs Ryu-style
  tables or big-number arithmetic that the hand-assembled guest backend does
  not have, which is disproportionate for this step; the diagnostic keeps the
  decision visible and floats can be added later without a source change.
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
  TE017 gates for destructuring and owned calls. A nominal struct that has a direct String or List field and an
  enum or tuple field that owns heap storage stays outside the shared transport
  predicate: it can be built, matched in place and released in its scope, but
  moving it into a call is TE017 ("a field that is an enum or tuple is not
  admitted yet") or LE900.
- Mixed variants: a variant that mixes a String with other payloads may leave
  the String unbound (`K::Two(_, b)`, `K::One(_, n)`): the unbound String is
  extracted into a discarded local and released with the arm. The IR check that
  every String `VariantExtract` consumes its base accepts a non-final extraction
  when a later extraction of the same owner local consumes the cell.
- Diagnostics: an integer pattern and a constant array index in a diagnostic
  echo the literal as written (`0x1FF`, `-0b1000_0001`, `1_6`); the lexer
  records the original spelling of every literal whose canonical decimal
  differs (thread-local, keyed by span and checked against the canonical text),
  checks keep using the canonical value. The negative literal pattern's operand
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
  heap-owning enum or tuple field by value across a call; reference elements and
  fields stay rejected; a guard still cannot move anything.
