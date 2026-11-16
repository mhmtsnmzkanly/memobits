# Fixed-array implementation sequence

The accepted design uses homogeneous `Array<T, N>`, array literals `[a, b]`,
repetition `[expression; N]`, and checked indexing. This document separates
syntax support from executable collection semantics.

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
  the activation frame; array operands push the cell address. Frames are capped
  at 32 KiB (`MAX_FRAME_SIZE`); `checked_mul`/`checked_add` overflow and the cap
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
  element-extraction rule TE022 also covers `a[i] = a[j]` (use `a[j] + 0`-style
  arithmetic instead until an explicit copy exists).
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

