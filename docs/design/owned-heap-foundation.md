# Owned heap foundation

This proposal follows the [accepted memory layout and ownership decisions](decisions.md).
Storage placement is private to the backend. Owned aggregate transfers move,
borrows read, and shares grant exclusive mutable access. The heap follows
static data and grows at the end of linear memory.

## Current starting point

The [Wasm backend](../../crates/memobits-wasm/src/lib.rs) reserves the first
16 bytes, then lays out the configured stack, the optional outcome return
cell, and reachable String literal descriptors and bytes. The initial Wasm32
memory covers these regions rounded up to 64 KiB pages. Modules without
reachable concat keep their fixed memory maximum. Frame entry checks the
stack bound, and normal return restores the stack pointer. The
[typed IR](typed-ir.md) records consuming operands, initialization,
reassignment, and control-flow edges. General drop insertion remains pending.

The [static layout planner](../../crates/memobits-wasm/src/memory.rs) now
places the stack, outcome cell and literal regions using one checked cursor.
It preserves the current memory limit and leaves the cursor unchanged after
a failed reservation. The byte heap starts at the exclusive end of static data.

## First consumer

`let joined := left.concat(right);` borrows both inputs and initializes an
independently owned String. The inputs stay usable after the call. The
combined bytes remain valid UTF-8 and can be read with the existing String
operations or lent to an internal borrow parameter.

This slice accepts concat as the direct initializer of an immutable local.
The owned result stays in that binding until its lexical exit. Moving,
returning, sharing for mutation or replacing it requires broader drop
elaboration. Typed IR verifies that the owning descriptor cannot escape and
that all normal exits release these bindings in reverse initialization
order. Since only those locals own heap allocations, the initialization
instruction supplies storage provenance without changing the descriptor.

Guest allocation grows memory only as needed, after checking the widened
exclusive byte end and its page ceiling. A failed grow traps at the concat
call before publishing a descriptor or advancing the cursor. On scope
exit the cursor returns to the released block's start. Verified nesting
across function calls requires no free list or runtime ownership flag.
Memory pages remain at their high-water mark and can immediately be reused.

Once the foundation works, List can reuse the byte allocator and owned
cleanup. Element initialization, element drops, and capacity changes belong
to later List work.

## Audit of scoped allocation

At each reachable block entry, the IR validator requires every incoming
edge to agree on the live concat locals and their order. A normal exit pops
only the most recently initialized local. A callee must return with its own
allocation stack empty, so its cleanup preserves the caller's allocations.
The move and loan checks run before Wasm emission. They prevent descriptor
transfer and reject a live borrow across release, even when release order is
otherwise valid. Two inputs may borrow the same String. Both reads finish
before the result is published, and both copies target new space above all
live allocations. These guarantees assume the generated guest controls its
memory. A host with access to the private outcome memory export must preserve
the guest's descriptors and bytes.

Regression cases exercise aliased input, recursive borrowing of a heap
String, reuse after a callee releases its allocations, and an intentionally
premature exit with a live borrow. Normal return, break and continue also
have page-reuse coverage.

## Progression to arbitrary ownership

1. Keep the lexical gate and change the existing concat allocator and
   release together. The [shared descriptor layout](../../crates/memobits-wasm/src/string_descriptor.rs)
   should distinguish static storage from heap storage and locate the
   allocation record. The record needs the reserved block extent, which
   remains valid when a smaller request reuses it. This lets release put a
   whole block on a private free list without rewinding past live data.
   Check reuse before growing the heap. Publish the descriptor only after
   allocation and copying succeed. Test reuse of a larger free block and
   out-of-order frees alongside the production lexical consumer.
2. Extend cleanup to the next ownership context before admitting its
   transfers. For local moves, transfer the release obligation with the
   descriptor and elaborate each exit from its incoming ownership state.
   Drop available owners, skip moved ones, and use a runtime flag only when
   mixed paths still share a cleanup site. Test a move between scopes where
   the newer allocation survives the older owner's exit.
3. Cover ownership across calls, returns and temporary results before
   permitting those uses. Transfer the result before dropping the callee's
   other owners. Drop discarded temporaries on normal exits. Evaluate a
   replacement before releasing the previous owner, including whole
   replacement through a share. Verify exact returned bytes, mixed ownership
   joins, and bounded memory use under repeated source and standalone Wasm
   execution. A trap still discards the whole instance.

## Allocation and failure

For modules that allocate, compute an aligned heap base after the final
static byte, including the outcome cell when present. Leave the stack limit
fixed. Check size, alignment, address addition and page rounding before any
guest load or store that depends on the allocation. Use widened arithmetic
for the page calculation and keep allocation ranges within the supported
Wasm32 address space. A zero-byte result can use the empty static
representation.

A private guest allocator can start with an end cursor and a free list of
whole blocks. Reuse a fitting aligned block when available and extend the
cursor when necessary. Grow memory only when the requested end lies past
the current page boundary. Preserve live addresses. Check the Wasm
`memory.grow` failure result before publishing an allocation or changing
the cursor or free list. A failed attempt leaves existing owners and free
blocks usable. A later allocator call can retry after space is freed.
Splitting, coalescing and tuning can follow measured need.

Keep allocation and deallocation in generated guest code so source runs
and standalone artifacts use the same mechanism. The runtime enforces the
module and engine memory limits and reports guest failures. For the first
consumer, translate size overflow or allocation failure into a controlled
guest failure with a source span. The caller's borrowed inputs stay intact.
The guest does not resume after a trap. A user retry runs in a fresh
instance, as it does for other [runtime failures](../../crates/memobits-runtime/src/lib.rs).
No host allocator imports or new manifest setting are needed for this slice.

## Ownership and cleanup

Move checking distinguishes definitely available, definitely unavailable and
mixed ownership at reachable block entries. It computes those facts separately
from diagnostic replay. Both run the same block and edge transfers,
including consumption of return values and parallel binding of successor
parameters. This gives cleanup elaboration a common starting point.
Reads require definite availability. A mixed slot owns a value on some
incoming paths, and move diagnostics now say so.
Lowering now emits `EndStringLocal` for owned String bindings and parameters
at normal lexical exits. A String result moves out before its binding ends.
The move checker invalidates the local and the loan checker rejects a live
loan across its exit. The marker accepts a moved local and emits no Wasm
operation for static locals. For a verified concat local, the backend instead
releases the most recent allocation. The move transfer clears the local
after its exit regardless of the incoming state.

For a future heap-backed local, elaborate the exit from its incoming state.
A definitely available local needs a drop, subject to the descriptor's
static/heap distinction. A definitely unavailable local needs no drop.
Use an edge-specific cleanup when the mixed paths are already separate.
Use a runtime flag only for a mixed exit that still shares a cleanup site.
Such a flag is set on successful initialization or reassignment and cleared
on a move or drop. No flags or frees are emitted in the current slice.
Other owner types and temporary cleanup remain separate work.

Extend the private String descriptor so cleanup distinguishes static
literal storage from an owned allocation. Stack cells still hold descriptors.
Moves transfer the obligation to free dynamic storage, while a borrow leaves
it with the owner. Static literals and empty static values require no free.
Releasing a heap allocation makes its block available for guest reuse.

Add a consuming cleanup operation to IR and place it where an initialized
owner is discarded on normal control flow. Use move availability and lexical
scope exits to cover discarded temporaries, fallthrough, return, break and
continue. A return moves its result out before cleanup of remaining owners.
On reassignment, including whole replacement through a share, evaluate the
new value first, then drop the old value if it is initialized and still
owned. At joins, drop only on paths that retain the owner. Borrowed and moved
values must never be freed by the old binding. The existing loan checker must
also reject a drop that would invalidate a live view. Trap and fuel failure
continue to discard the instance without guest unwinding.

## Verification

- Validate emitted Wasm and test region separation with literals and an
  outcome return cell present. Retain the existing stack exhaustion checks.
- Test alignment, exact page boundaries, checked size overflow, and forced
  grow failure using controlled limits in tests. Verify that an unsuccessful
  allocation preserves live data and allocator state, then free a block and
  verify a retry can reuse it.
- Check normal cleanup on scope exits, replacement, branch joins and loop
  exits. Verify transfer through calls and returns frees once, static
  literals are never freed, and live loans block invalidation. Repeat scoped
  allocations under a small test limit to make leaks and missing reuse visible.
- Check concat length and exact bytes for ASCII, multibyte and empty inputs.
  Run the same example from source and from a standalone artifact built into
  a temporary directory. Check that a forced failure has a controlled diagnostic
  and a fresh run still succeeds.
