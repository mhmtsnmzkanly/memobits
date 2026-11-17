# Typed intermediate representation

## Boundary

`memobits-ir` holds compiler data independently of syntax, project loading, and
name resolution. Analysis produces this representation after successful name,
type, and structural control-flow checking. Structural IR validation, source
analysis, and ownership checking run as separate checks. See the
[implementation plan](implementation-plan.md) for the executable subset.

Type inference must remain in one analysis traversal. The checker should retain
typed expressions and resolved local/function identities, then lower them to
control flow. Re-running a second, slightly different inference algorithm in the
backend would allow analysis and execution to disagree.

## Identity and source mapping

Functions use canonical module/declaration identities. Locals receive distinct
IDs per function, including shadowed bindings. Basic blocks and temporary values
also receive function-local IDs. Instructions retain the original source spans
of operations and operand uses. Compiler-generated edges may have no source
span; they must not invent positions in user source.

## Control flow

Blocks contain ordered instructions and one terminator. Conditions branch to
blocks, loops have backedges, and break/continue target their enclosing loop.
Returns terminate the current path. A block that cannot complete normally must
not produce an ordinary Unit result merely because it has no tail expression.
Short-circuit operators require branches so the right operand is not evaluated
on the skipped path.

## Ownership operations

Operand uses distinguish reading from consuming ownership. Arithmetic,
comparisons, and conditions read their inputs. Binding transfer, owned argument
passing, assignment transfer, and return consume move-only inputs. Primitive
values copy implicitly. Compound assignments read and then write the destination.
Borrow and share operations preserve their access distinction in the IR.

Move analysis propagates availability for locals and temporaries through the
control-flow graph. A use after a move on any reachable incoming path is an
error. Loops require a fixed point; checking only one traversal of a loop body
would miss reuse on the next iteration. Reinitialization restores availability
when permitted by the binding's mutation rules.

## Verification targets

- Repeated arithmetic reads of one scalar remain valid.
- Repeated owned transfer of an aggregate is rejected.
- A move on one reachable branch is reflected at the join.
- Loop backedges preserve move state across iterations.
- Shadowing gives the new binding a fresh identity.
- Call arguments retain left-to-right evaluation order.
- Library roots exclude unrelated application entry code.

Aggregate layout and Wasm emission consume validated IR. Heap-backed cleanup
and embedded-loan tracking remain pending. The IR is an internal compiler format.

## Current lowering and validation

The IR data model and its validator are implemented. Functions carry an explicit
mapping from parameters to initialized local slots. The ownership gate
checks availability and loan conflicts for supported internal borrow/share uses.

Standalone analysis now retains expression types and resolved identities with
per-function expression IDs. Standalone lowering uses those retained facts and
returns structurally validated IR. Source diagnostics prevent IR from escaping.
Project-wide retained facts and lowering preserve canonical identities across
local modules and feed the same ownership and Wasm pipeline.

`Capture` materializes an operand before subsequent side effects. Owned call
arguments consume the original local at capture time; arithmetic reads snapshot
the value without moving the local. Binary left operands, local callees, and
compound-assignment destinations are captured before later expressions execute.
Short-circuit right operands remain in conditional control flow.
