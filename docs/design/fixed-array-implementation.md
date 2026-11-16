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
