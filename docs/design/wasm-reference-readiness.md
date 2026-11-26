# Primitive Wasm reference readiness

This historical plan follows the source-reference audit and records the
checkpoints through primitive reference emission. See the
[roadmap](../roadmap.md) for current support.

## Implementation sequence

1. Extend frame layout to distinguish address-taken primitive owner locals from
   existing reference handles. Reborrows of reference locals and temporary
   reference values reuse their address and must not allocate a second owner
   cell. The layout helper must accept source-generated call reborrows before emission is enabled.
2. Give each invocation an aligned, bounded linear-memory frame. Check stack
   allocation overflow before changing the stack pointer. Save the incoming
   pointer and restore it on every normal return, including early returns.
3. Make owner cells authoritative. Once a local is address-taken, parameter
   initialization, assignment, arithmetic reads, and direct owner reads must use
   the cell. A Wasm local mirror must not hide mutations made by a callee.
4. Represent internal primitive references as addresses. Lower Borrow to an
   address/reborrow, Load to width-correct loads, and Store to width-correct
   stores. Preserve signedness, Bool validity, and checked arithmetic behavior.
5. Enable internal reference signatures only behind the combined ownership
   gate. Keep reference exports, reference returns, aggregate/nested references,
   and unsupported owner forms rejected until their contracts are defined.
6. Validate generated modules and run source/artifact equivalence tests before
   enabling the CLI path. Existing runtime runs use fresh instances; persistent
   instances would require an explicit trap/reset policy.

## Required executable tests

- Share mutation visible in caller, including direct owner reads after last use.
- Independent owners, simultaneous read-only borrows, and nested reborrows.
- Every primitive width, signed and unsigned loads, floats, and Bool conditions.
- Left-to-right arguments, compound assignment snapshots, and short-circuiting.
- Recursive/nested calls with distinct frames and early-return restoration.
- Repeated calls without stack growth; bounded exhaustion produces a trap.
- Compile-time rejection of conflicting loans, moved handles, immutable target
  writes, unsupported external signatures, and dangling-reference escapes.
- Existing owned numeric programs keep their results and checked failures.

The static analysis remains a tested primitive subset. Passing its regression
suite is a prerequisite for emission, not a proof of the complete future language.

## Frame layout implementation checkpoint

Step 1 is implemented and tested. Only address-taken primitive local owners
receive cells. Reborrows of primitive reference locals and temporary handles
reuse their existing addresses and require no new cells. Invalid IDs, primitive
temporaries, function roots, Unit, nested references, and Owned reference access
are rejected. Source-generated call IR is included in the layout tests.

The next implementation step is bounded per-invocation frame allocation and
restoration. The layout helper remains separate from executable emission;
Borrow/Load/Store programs still receive unsupported backend diagnostics.

## Activation frame implementation checkpoint

The emitter now has per-invocation frame allocation and restoration scaffolding.
Nonempty frames use a private, fixed one-page linear memory, with addresses below
16 reserved and a 65536-byte exclusive upper bound. Allocation checks remaining
capacity before addition or stack-pointer mutation. Each activation retains its
base in a local and restores the stack pointer on normal and early returns.
Zero-frame programs do not acquire memory or a stack global.

The fixed capacity is an experimental implementation limit. Traps do not unwind
caller frames; the current runtime discards the instance after execution. A future
persistent-instance API must reset or discard trapped instances.

Tests inject frame sizes into ordinary primitive functions through a private
test helper to execute this infrastructure before reference instructions are
enabled. This does not yet implement authoritative owner cells or reference
loads/stores. Those are the next integration step.

## Primitive reference execution checkpoint

Internal primitive Borrow/Load/Store now execute in Wasm after the combined
ownership gate. Address-taken owners use authoritative frame cells; parameter
initialization, direct reads, assignments, captures, calls, arithmetic, control
flow edges, and returns use that storage. Reborrows reuse pointers and typed
loads/stores preserve scalar width and signedness. Source and artifact CLI
execution are tested together. This supersedes earlier disabled-emission status
for internal primitive references only. Exported reference signatures, reference
returns, aggregates, indirect calls, and a stable external reference ABI remain
unsupported. Trap instances must be discarded rather than reused.
