# Borrow and share implementation sequence

This document applies the accepted access rules to the primitive compiler path.
The checkpoints record the primitive implementation as it landed. See the
[roadmap](../roadmap.md) for current support and the accepted rules in
[decisions](decisions.md).

## Frontend access information

The documented conversions are `owner.borrow()` and `owner.share()`. Parsing a
conversion does not prove it is legal. Function types must retain access modes
through standalone and project-wide signature resolution; a function parameter
must not become owned merely because it is stored as a function value.

Local metadata must distinguish owner mutability, access capability, and handle
rebinding. A share parameter permits writing its target without `var`, but does
not permit replacing its owner identity. A borrow parameter never permits
writing. An owned parameter requires `var` for mutation. Local share handles
require `var` for target mutation, as recorded in the accepted decisions.

## Loans and calls

Conversions identify the original owner. Calls require access matching their
signature. A temporary borrow or share argument starts its loan when evaluated,
so later arguments cannot conflict with it before the call ends. Stored handles
extend loans through their last reachable use. Control-flow joins and loops must
preserve conflicts, including moves and writes to the owner while a loan is live.

Read-only loans can coexist; an exclusive share conflicts with other access to
its overlapping owner. The initial primitive implementation must not claim field
disjointness or aggregate lifetime support. Unsupported reference escape cases
must produce diagnostics instead of allowing dangling access.

## Wasm representation

Mutable share must write back to the original owner. Passing the scalar value
alone cannot implement this. A pointer-based implementation needs addressable
owner cells and reentrant frame allocation so recursive calls do not overwrite
another call's storage. Linear-memory loads/stores must use the declared source
type and preserve checked numeric semantics.

Backend representation follows static access proof; it does not replace it.
External exports with access parameters require an explicit ABI decision and
must remain unsupported until that contract exists. The current scalar owned
ABI does not imply a public reference ABI.

## Required verification

Verify owner preservation after borrowing, caller mutation through share,
immutable-owner rejection, overlapping argument rejection, last-use release,
branch/loop conflicts, local handle mutability, and recursive/nested calls.
Source and artifact execution must agree. Existing owned scalar programs and
move checks remain regression coverage throughout this work.

## Access metadata checkpoint

Analysis now preserves parameter access in internal function types and retained
IR signatures. Bindings, local facts, and path uses retain access separately
from rebinding mutability. This is infrastructure only: borrow/share parameters
still produce TE017 and cannot be lowered to executable code.

The next IR foundation distinguishes reference handles from loaded scalar reads.
A raw read through a reference must not become an owned transfer accidentally.
Until explicit copy semantics are implemented, direct load results remain
read-only through captures and block arguments; arithmetic may compute a fresh
owned result. Loan origin, liveness, and conflict checking remain required before
this foundation can enable source-level borrowing.

## Reference validation gate

The structural validator must check parameter-local reference shape and reject
store through a read-only borrow. Creating a reference must retain the declared
inner type and access capability. A borrow cannot be strengthened to share.
Loan identifiers identify creation sites; loop iterations may execute the same
site repeatedly and must not be mistaken for simultaneous distinct static IDs.

Read-only scalar loads require propagation through captures and block arguments,
including cyclic edges, before checking consuming uses. Merely checking the
instruction immediately after a load would permit an owned transfer through an
alias. This structural restriction is temporary and conservative; it does not
prove loan liveness or absence of conflicting access to the owner.

## Initial backend frame direction

Internal mutable references will use addresses in linear memory. Every owner
whose address is taken needs an authoritative frame cell; ordinary reads and
assignments of that owner must access the same cell. A mirrored Wasm local would
become stale after a callee writes through a share.

Frames must be allocated per activation with alignment and explicit stack bounds,
then released on normal returns. Traps end the current execution; the current
runtime instantiates afresh per run, so it does not reuse a partially unwound
frame stack. A persistent-instance API would need an explicit reset/unwind policy.
External reference parameters and reference returns remain unsupported until a
reference ABI is specified. Stack capacity is an implementation limit, not a
language semantic rule or a stable ABI commitment.

## Loan analysis boundary

The initial loan analysis will combine backward reference-slot liveness with
forward may-provenance across captures, assignments, and block arguments. A join
retains every possible origin, so a later write cannot ignore the owner selected
on another incoming branch. Reference arguments remain live during evaluation
of subsequent arguments and through the call.

Reference returns and reference-valued call results remain explicitly unsupported
until signatures describe their origin relationship. No guessed lifetime mapping
will be accepted as a stable language contract. Loop-carried references need
special care because one static creation site may execute multiple times.

## Frame layout checkpoint

The backend now has a tested layout helper for primitive local owners. It assigns
cells deterministically, aligns each cell by its scalar width, checks arithmetic
overflow in offsets, and rounds nonempty frames to 16 bytes. It rejects temporary,
reference, and Unit owner roots. This helper is not yet used to generate memory
or share instructions; executable reference support remains disabled.

## Reference availability checkpoint

The shared ownership gate now checks primitive reference-handle availability,
including parameter initialization, moves, uninitialized slots, branch joins,
and loop backedges. Borrow and Share uses require an available source but do
not consume it; explicit handle transfers consume their source. CFG argument
binding preserves incoming availability rather than manufacturing initialized
parameters. Source reference lowering and Wasm frame emission remain disabled
and are the next integration boundary.

## Source lowering checkpoint

Primitive source references now lower to validated IR and pass through the shared
ownership gate. Conversions require named local owners or references. Calls
create explicit reborrow sites while evaluating arguments left to right, keeping
loans live across later argument evaluation. Reference bindings transfer handles;
primitive arithmetic and conditions load snapshots, and share assignments store
through the handle. Share parameters permit target writes without `var`; local
share handles require `var`.

Owned calls and returns cannot silently extract borrowed scalars. Reference
returns, nested/aggregate references, reference rebinding, and reference-valued
block/if expressions remain unsupported. This conservative scope prevents owner
origin escape before signatures and joins carry a lifetime contract.

CLI ownership commands accept this subset; build and run continue to reject
reference programs at the Wasm backend (LE900). Addressable frame cells and
reference-aware emission remain the next implementation stage.

## Reborrow-aware layout checkpoint

Frame layout now accepts existing primitive reference locals and temporary
reference handles without allocating extra owner cells. Source-generated
implicit call reborrows are covered by tests. Primitive owner cells retain
deterministic alignment. This supersedes the earlier layout limitation for
reference roots; execution still awaits per-invocation frames and emission.

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
