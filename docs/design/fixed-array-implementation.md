# Fixed-array implementation sequence

`Bytes<N>` is a built-in spelling for `Array<u8, N>`. It accepts the same
nonnegative integer literal lengths, including zero, and uses ordinary array
literals. The two spellings have identical type identity, ownership, borrowing,
layout and ABI restrictions. Bare `Bytes` still resolves as a user-defined
type or import. Dynamic byte buffers are outside this slice.

The accepted design uses homogeneous `Array<T, N>`, array literals `[a, b]`,
repetition `[expression; N]`, and checked indexing. This document separates
syntax support from executable collection semantics.

## Future Bytes API inspirations

These Rust crates suggest areas to explore after the
[first executable String slice](utf8-text-slice.md).

- Buffer cursors and borrowed byte ranges. [bytes](https://docs.rs/bytes/latest/bytes/)
- Checked fixed-width numeric reads and writes with explicit endianness.
  [byteorder](https://docs.rs/byteorder/latest/byteorder/)
- Search and delimiter handling on arbitrary bytes, including invalid UTF-8.
  [bstr](https://docs.rs/bstr/latest/bstr/)
- Typed views over binary data with explicit layout constraints.
  [zerocopy](https://docs.rs/zerocopy/latest/zerocopy/)
- Packed flags and bit-level views with explicit bit order.
  [bitvec](https://docs.rs/bitvec/latest/bitvec/)

Advance an idea only when a concrete consumer shows what it needs and why
existing array operations fall short. Check bounds, loan lifetimes, and
aliasing where relevant. Typed views also need layout, alignment and value
validity checks. Verify behavior in source and Wasm, and benchmark against
ordinary array code when reduced copying or faster access is the motivation.
These themes leave the current `Bytes<N>` array equivalence in place.

## Syntax foundation

Represent element lists, repetitions, and indexing explicitly in the AST.
Repetition retains one expression and a source-located count; the parser must
not clone its expression or evaluate it. `Array<T, N>` retains structured type
arguments so nested element types and constant lengths cannot be silently lost.
The initial syntax accepts nonnegative integer literal lengths; general constant
expressions and const generics require later design work.

Resolver and semantic traversals must visit array elements, repeat expressions,
and index operands. Nested element type names must be resolved. Until array
semantics exist, analysis reports an explicit unsupported diagnostic and returns
no typed executable IR. Parsing an array does not imply type checking or running
it is supported.

## Type and flow analysis

Implement homogeneous element checking and contextual literal typing. Infer
length from element lists and verify annotated lengths. Empty literals require
an element type from context. Verify repetition count and element type without
expanding arbitrarily large ASTs. Reject layouts too large for the chosen target
before backend allocation; the practical diagnostic limit is an implementation
constraint, not a reason to allocate host memory proportional to unchecked input.

Every repeat element evaluates its expression separately in source order.
`[make_value(); 3]` invokes the function three times. Reusing an owned binding
must follow explicit move/copy rules. A zero count evaluates no element expression;
its type-checking and ownership treatment must be specified and tested before
executable repetition is enabled.

## Ownership and IR

Fixed arrays always contain initialized elements. `let` prevents element mutation.
Element extraction into an owned binding requires explicit borrowing, sharing,
copying, or replacement. Array indexing alone must not accidentally transfer a
scalar or aggregate element. Model index expressions and their evaluation order,
then represent addresses and initialized owner storage in typed IR.

Use conservative overlap checking initially; add proven disjoint constant-index
borrows only with dedicated tests. Dynamic indices overlap unless proven otherwise.
Aggregate moves, cleanup, and normal-exit storage lifetime must be checked before
array programs pass the shared ownership gate.

## Execution and validation

Define aligned array layout and checked size multiplication. Constant out-of-range
indices produce compile diagnostics; unknown indices receive runtime bounds
checks. Preserve identical checked behavior across profiles. Integrate typed
loads/stores with authoritative storage and the existing frame allocator, keeping
unsupported aggregate exports rejected until the ABI is defined.

Test lengths zero/one/nested, homogeneous inference, annotation mismatches,
repetition call counts and order, repeated owned moves, let mutation rejection,
index evaluation order, constant/dynamic bounds, aliasing, nested calls, and
source/artifact equivalence. Dynamic List and String follow a separate sequence.

## Syntax implementation checkpoint

The structured array AST and parser are implemented. Resolver traversals inspect
all operands and nested element type names. Control-flow and constant-checker
traversals handle the new nodes without dropping subexpressions. Semantic
analysis explicitly rejects array types, literals, repetition, and indexing with
TE017; no executable array IR is produced. Parser regressions cover nested types,
postfix precedence, source spans, malformed delimiters/counts, and recovery.
The next step is homogeneous element typing and length validation.

## Type-checking checkpoint

Standalone and resolved type-only analysis now infer homogeneous array elements
and literal lengths, apply contextual numeric element types recursively, and
validate annotation lengths. Empty literals require an element type from context.
Repetition checks its expression once without allocating or expanding count-sized
ASTs; even zero repetitions type-check the element expression. Length literals
are checked against u32::MAX, a current analysis implementation bound rather
than a promise that every such layout fits memory.

Typed executable IR remains gated with TE017. Indexing, array references,
reference-valued elements, owned array call arguments, and array execution remain
unsupported. Type-only success is not an ownership proof. The next step is typed
aggregate IR and ownership rules, including initialized element storage and
explicit element access; backend layout size must be checked before execution.

## Flow and index analysis checkpoint

Repeated-array flow now distinguishes zero count from positive count. A zero
repeat evaluates no element expression for control-flow purposes, so a `return`
inside it cannot satisfy the enclosing function's return requirement. Type/name
checking still visits the repeat expression. Positive repeats retain element
flow, and a divergent element uses its contextual element type where available.
Regression tests compare list and repeat forms.

Type-only analysis now checks that array indices have integer types and rejects
constant negative or out-of-range indices. Small literal constants are checked
statically. Typed executable facts still reject arrays/indexing with TE017, and
dynamic bounds checks remain pending backend/IR support.

## Executable array checkpoint (WP1)

Executable support is a deliberately small vertical slice: a `let` array of
non-Unit primitive elements, built from a literal and read by index inside
expressions.

- IR: `Type::Array { element, len }`, `ArrayNew { init: ArrayInit }`
  (`Elements` consumes one operand per element; `Zeroed` is defined for repeat
  lowering and covered by backend tests but never emitted by analysis) and
  `ElementAddr { loan, base, index, access }`, the array twin of `Borrow`. An
  indexed read is `ElementAddr(Borrow)` + `Load`; the bounds check is part of
  `ElementAddr`. The validator rejects non-primitive/Unit elements, array block
  parameters and array signature types, non-integer or non-Read indices, and
  loan-id reuse across `Borrow` and `ElementAddr`.
- Analysis: array literals are accepted only as a `let` initializer, array
  locals only as the base of an index, and indexing only on a named local.
  Element reads are read-only values: TE022 rejects moving one into a binding,
  `=` right-hand side, return, block/if tail, owned call argument or array
  element. TE017 still gates repetition, `var` arrays, element and whole-array
  assignment, whole-array use as a value, array parameters/results/references,
  nested arrays and non-primitive elements.
- Ownership: `ElementAddr` reads its base like `Borrow` (availability checked,
  not consumed) and its index like a normal operand; `ArrayNew` consumes its
  elements. A loan on an array local overlaps every element (no index
  reasoning).
- Wasm: every array-typed local and value owns an inline, element-aligned cell in
  the activation frame; array operands push the cell address. A frame must fit the
  configured `[build].stack_size` (default 1 MiB); `checked_mul`/`checked_add` overflow and the limit
  are backend diagnostics, never host allocations. `ElementAddr` does an
  unsigned compare against the length (negative indices become huge) in the
  index's own width, so 64-bit indices are never truncated, and traps with
  `unreachable` like integer overflow. Array assignment/capture use
  `memory.copy`, `Zeroed` uses `memory.fill` (bulk memory, on by default in
  wasmi).
- Because a literal is built in its own value cell and copied into the binding,
  an array effectively uses twice its size in the frame.

## Executable array checkpoint (WP2)

WP2 adds mutation, repetition and whole-array moves on top of WP1.

- Analysis accepts `var` arrays; `a[i] = v` and `a[i] op= v` (`+= -= *= /= %=`,
  same operator rules as scalars); `[expr; N]`; and whole-array `let b := a;` /
  `b = a;` / `b = [..]` / `b = [x; N]`. Arrays of primitive elements only.
  A whole-array value (literal, repetition or named local) is accepted only as
  a binding initializer or the right-hand side of `=`. Element assignment to a
  `let` array is TE004; a constant out-of-range write index is TE008; the
  element-extraction rule TE022 also covers `a[i] = a[j]` (write
  `a[i] = a[j].copy();`; see the primitive copy in `implementation-plan.md`).
- Element assignment lowers per D2: base, index (captured), then the right-hand
  side, then `ElementAddr(Share)` and `Store` adjacently, so the bounds trap
  fires after the right-hand side's effects. A compound write first does
  `ElementAddr(Borrow)` + `Load`, then the right-hand side, `Binary`, and a
  second `ElementAddr(Share)` + `Store`.
- Repetition lowers without any new instruction. Count 0 emits only
  `ArrayNew Zeroed` and evaluates nothing. Count 1 emits a one-element
  `ArrayNew Elements` (a single evaluation, no loop). Count N >= 2 emits a hidden
  mutable accumulator local (`ArrayNew Zeroed`), a hidden `u32` counter and a
  loop whose body evaluates the element expression (index captured first),
  stores it through `ElementAddr(Share)`, and increments; after the loop the
  accumulator is moved out with a consuming `Capture`. IR size and compiler
  work do not depend on N. Because the element operand is consumed inside the
  loop, repeating an owned binding (`[x; 3]`) is a use-after-move (BE001) in the
  ownership pass; counts 0 and 1 do not reach a second evaluation and are
  accepted, as is any expression that does not consume a binding (`[x + 0; 3]`).
- Whole-array move is `Assign` (or a consuming `Capture`) of an array operand;
  the backend copies with `memory.copy`. The source local becomes unavailable,
  so any later use (including indexing) is BE001 until it is reassigned.
- Ownership and loans needed no new rules: `ElementAddr` already treats its base
  like `Borrow`/`Share`, and a Share element write conflicts with any live
  element reference of the same array (BE005), tested with hand-built IR because
  array references are not expressible in source before WP3.
- Wasm: an `ArrayNew` or array `Capture` whose output is consumed only by the
  immediately following `Assign` to an array local is constructed directly in
  that local's cell (`construction_aliases`); the `Assign` then emits nothing.
  This removes the WP1 doubled frame usage for literals and halves it for
  repetition (accumulator + binding cell). Element operands are scalars read
  before the write, so in-place construction cannot read a half-written cell
  (`a = [a[1] + 0, a[0] + 0]` is covered by a test). Frame cap tests now use
  repetition and run in milliseconds.

Still gated with TE017: array parameters, results and references (WP3/WP4),
nested arrays and non-primitive elements, array-valued `if`/block results and
block tails, whole arrays as call arguments, operands or return values, array
literals and repetition outside a binding initializer or `=`, indexing a
non-local, and element references (`a[i].share()`). Arrays in exported
signatures remain rejected by the backend.


## Executable array checkpoint (WP3)

WP3 lets arrays of primitive elements cross internal function calls.

- Signatures: `a: Array<T, N>` (owned), `a: borrow Array<T, N>` and
  `a: share Array<T, N>`. In IR a parameter names its pointee type, so the
  parameter local of a `borrow`/`share` array is `Reference { access, inner:
  Array }`, exactly like primitives; the validator now allows an array (never a
  nested reference) as the referent, accepts `Borrow` of an array owner or array
  reference, and keeps array results and array block parameters invalid. `var`
  on an owned array parameter permits element writes to the callee's own copy;
  `var` on a reference parameter stays TE017.
- Source spelling mirrors primitives: the caller writes `a.borrow()` or
  `a.share()` (a bare array for a reference parameter is TE017) and the
  signature decides the access; `share` needs a `var` owner. Local bindings
  `let r := a.borrow();` and `var r := a.share();` work as for scalars, and a
  reference parameter or binding can be passed on (reborrow) to a parameter of
  equal or weaker access. A `let` share binding cannot write (TE004).
- Typing: indexing unwraps an array reference. Reads work through `borrow` and
  `share`; `a[i] = v` and `a[i] op= v` require `var`/share ownership and are
  TE004 through a `borrow` or an immutable share binding. A constant
  out-of-range index through a reference is TE008, the D1 extraction rule
  TE022 applies unchanged, and a length or element mismatch between argument and
  parameter is TE002 (`expected borrow Array<i32, 3>, found borrow Array<i32,
  2>`). An owned array argument may be a literal, a repetition or a named array
  (a move). A whole array may be assigned through a share reference
  (`a = [1, 2];` stores with a memory copy).
- Ownership and loans needed no new rules. An owned argument is captured (moved)
  when it is evaluated, so later arguments cannot use it (BE001). `.borrow()` /
  `.share()` are ordinary `Borrow` instructions rooted at the array local, so
  every element access overlapped the whole array (A4 narrows this to projection paths: distinct constant indices are independent, a dynamic index overlaps every index): an element write while a
  borrow or share is live is BE005, two `share` (or share + borrow) arguments of
  one array in a call are BE005, and any number of `borrow` arguments are fine.
  These are tested in source form (`memobits-analysis/tests/array_references.rs`).
- Wasm: a reference to an array is the owner cell's address (an `i32` Wasm
  parameter/local). `ElementAddr` pushes the base operand, which is the cell
  address for an owner and the pointer for a reference, so one code path does
  the unsigned bounds check against the length from the type. An owned array
  parameter arrives as a pointer to caller-side storage (the caller's captured
  value cell or a literal's cell, which stays valid for the whole call because
  the callee frame sits above it); the parameter prologue `memory.copy`s it into
  the callee's own cell, so a `var` parameter never writes into the caller and
  every recursive activation has its own copy. A whole-array `Store` through a
  share reference is a `memory.copy` too. Parameter cells count against the
  frame limit (the configured stack size) of the callee.
- Exports: `main` and `[export]` functions with array or array-reference
  parameters are rejected by the backend with LE900 ("cannot take arrays or
  array references; the external array ABI is not defined"). There is no
  external array ABI.

Still gated: array results and array-valued `if`/block results (TE017), nested
arrays and non-primitive elements (TE017), element references (`a[0].share()`,
TE017), borrowing a temporary (`[1, 2].borrow()`, TE017), rebinding a reference
handle, and arrays/array references in exported signatures (LE900).


## Executable array checkpoint (WP4)

WP4 finishes fixed arrays for primitive and nested-array elements.

- IR: `Type::Array` elements may be arrays (validated recursively). Function
  results and block parameters may be arrays. A `Load` of a whole array
  reference is invalid (rows are only addressed, never loaded). Rows use the
  existing `ElementAddr` twice: `m[i][j]` is `ElementAddr(m, i)` giving
  `Reference { inner: Array }`, then `ElementAddr(row, j)`, then `Load`.
- Analysis: the old single-address "allowed array" gate became a set of
  owned-value positions (binding initialiser, `=` right-hand side, `return` and
  tail value, owned array argument, array element, repetition element). The
  position propagates into the tails of `if` and block expressions, so
  `let a := if c { [1, 2] } else { [3, 4] };`, `{ [5, 6] }`, and a named array
  moved in a branch are accepted. Array results use the same positions
  (`-> Array<i32, 3> { [1, 2, 3] }`, `return a;`, `a` an owned local or
  parameter). A call returning an array is accepted wherever an owned array is.
  Indexing accepts a named local or a row chain rooted at one; a call result
  or other temporary (`make()[0]`) is TE017 ("bind the array to a local
  first"). `m[i].borrow()` / `m[i].share()` are element references to a row
  with the same ownership requirements as `m.borrow()` / `m.share()` (a `let`
  or `borrow` root cannot be shared: TE017); a reference to a primitive element
  (`m[i][j].share()`) is still TE017. Constant indices are checked on every
  level (TE008). Extracting a row (`let r := m[i];`, `m[i] = m[j];`, passing
  `m[i]` as an owned argument, returning it, an expression statement `m[i];`)
  is TE022 exactly like a scalar element.
- Lowering: `m[f()][g()] = h()` evaluates and captures the root and every
  index left to right (f, g), then the right-hand side (h), then forms the
  whole checked address chain and the `Store` adjacently, so any bounds trap on
  either index fires after the right-hand side's effects (decision D2, now on
  every level). A compound write forms a Borrow chain and `Load` first, then
  the rhs and `Binary`, then a Share chain and `Store`. Every level of a Share
  chain has Share access. A row `Store` through a Share reference is a
  whole-array `memory.copy`, so `m[i] = [1, 2]` moves a freshly built row into
  the slot (its old contents are replaced); a self-referential rhs such as
  `m[0] = [m[0][1] + 0, m[0][0] + 0]` is safe because the new row is built in
  its own value cell first. Repetition needed no change: its element expression
  may be an array (`[[0; 2]; 3]`, `[[next(), next()]; 3]`), each iteration
  evaluates it separately and stores it into the accumulator slot.
- Result design (struct-return). An array-returning function has one extra
  trailing Wasm parameter, a pointer to caller-allocated result storage. The
  caller passes the address of the call's own output value cell in its
  frame; the callee's `return` does one `memory.copy` of the returned array
  into that pointer before releasing its frame. No pointer into a dead callee
  frame ever exists. The result can alias nothing: the cell is fresh, and
  `memory.copy` is overlap-safe anyway. `main` or an `[export]` returning an
  array is LE900 ("cannot return arrays"); arrays also stay out of exported
  parameters.
- Join design. The simpler sound option was chosen over lowering into a
  destination slot: block parameters of array type are allowed, and each is an
  ordinary frame cell. A join edge copies the array argument into the
  parameter cell (`memory.copy`), after the scalar arguments are staged and
  before the staged values are assigned. Ownership is unchanged: the edge
  consumes its argument, so a named array moved on one branch is unavailable
  after the `if`. The cost is one extra copy per array join and one extra cell
  per array value.
- Layout: `array_layout` is the size and alignment of an array type, the
  element size times the length with `checked_mul` at every level, so nested
  sizes are products and overflow is the same "exceeds the configured stack
  size" diagnostic as an over-large frame. Layout cost depends on the
  nesting depth of the type only, never on a source-supplied count; no host
  allocation scales with a count. Call output cells, join parameter cells and
  nested value cells count against the cap (each array-typed IR value owns a
  cell, with no slot reuse, so a function with very many array-returning calls
  can hit the cap).
- Loans: rows are `ElementAddr` loans rooted at the array local, so a borrow of
  any row, element or the whole array overlaps all of them: writing `m[i][j]`
  while `m.borrow()` or `m[k].borrow()` is live is BE005, and two `share` rows
  of one matrix in one call are BE005. A borrow-chain's parent loans are
  excluded from conflicts with the chain's own next level.

Still gated, with the diagnostic: references to primitive elements
(`m[0][0].share()`, TE017); indexing or borrowing a temporary (`make()[0]`,
`[1, 2].borrow()`, TE017); extracting an element or row into an owned position
(TE022 for rows only; primitive elements are copied implicitly; whole-row or
array copy is not available); whole arrays used as
operands or expression statements (TE017); reference-typed elements and
returned references (TE017, `a` where `a` is a `borrow`/`share` array); `Unit`
elements (TE017); arrays and array references in exported signatures
(parameters and results, LE900); reference rebinding (TE017).

## Primitive collection search

`array.contains(value) -> Bool` checks for an element equal to `value`.
`array.index_of(value) -> Option<u32>` returns `Some(index)` for the first
zero-based match or `None` if no element matches. Both use `==` and
require a search value of the element type. Supported element types are `Bool`, `i8`, `i16`, `i32`, `i64`,
`u8`, `u16`, `u32`, `u64`, `f32`, and `f64`. This includes `Bytes<N>`.
For an empty array, `contains` returns false and `index_of` returns
`None`. With float elements, signed zeros compare equal and NaN never
matches.

The receiver is evaluated and borrowed before the value is evaluated
once. The scan stops at the first match. The receiver can be a local,
a borrow or share handle, a row or field of a local aggregate, or an array
value such as a literal or a function result.
[Runnable language guide](../../examples/guide/src/main.mb)

## Fixed array iteration

`loop value in items { ... }` evaluates the iterable once and visits its
elements in increasing index order. It supports fixed arrays with numeric or
`Bool` elements, including `Bytes<N>`. The iterable can be an array value,
an array reference, or a field or row reached through a local binding. An
empty array evaluates the iterable and skips the body.

Each iteration binds an immutable primitive copy within the body. A read loan
holds the iterable for the body and prevents overlapping writes and moves.
`continue` advances to the next element, `break` leaves the loop, and `return`
exits the function. Bare `loop { ... }` still repeats until control leaves it.
[List iteration](list-slice.md#list-iteration) uses the same loop syntax.
Iteration over Strings and arrays of aggregates remains deferred.

[Runnable language guide](../../examples/guide/src/main.mb)

## Implicit primitive copy checkpoint

The decision that primitives are copied implicitly supersedes the earlier
element-extraction wording in this document. Where it says that TE022 rejects
moving an element into a binding, `=` right-hand side (`a[i] = a[j]`), return,
tail, owned argument or array element, that now holds for aggregate elements
(rows of a nested array) only; a primitive element is read into any owned
position through `Load` + `Copy` and the array stays whole. Repeating a
primitive (`[x; 3]`, `[a[0]; 3]`) is fine, so the repeated-move BE001 applies
only to aggregate elements. `.copy()` on a primitive element is optional. The
swap `let t := a[0]; a[0] = a[2]; a[2] = t;` is now the natural spelling.


## Arrays of structs and array fields (A3)

Arrays of structs, struct-typed elements inside nested arrays, and array-typed
struct fields now execute. The projection machinery above (chained
`ElementAddr`, `Share`/`Borrow` chains, whole-element `Store` as `memory.copy`,
TE022 for extracting an aggregate element, per-element repetition) is reused
unchanged and generalised to mixed chains of `ElementAddr` and `FieldAddr`
(`a[i].pts[j].x`). An element that is a struct is an aggregate element for the
purposes of every rule above: `a[i] = P { .. }` replaces it in place, `a[i]`
cannot be moved out (TE022), and `a[i].borrow()` / `a[i].share()` lend it. See
the A3 checkpoint in `struct-implementation.md`. References to primitive
elements (`m[i][j].share()`) remain gated, and so do references to primitive
fields.
