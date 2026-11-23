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
- Until then, the runnable guide uses module-ranged check codes (1xx–9xx)
  documented in examples/guide/README.md.

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
    success may carry no value). There is no separate `Attempt` type.
    `Done(v)`, `Skipped` and `Failed(e)` remain as constructor and pattern
    aliases for `Ok(Some(v))`, `Ok(None)` and `Err(e)` on this type.
  - `?` binds tighter than `!`: `u32? ! E` is `(u32?) ! E`; parentheses group
    explicitly, e.g. `(u32 ! E)?` and `(borrow T)?`.
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
