# Owned heap foundation

This proposal follows the [accepted memory layout and ownership decisions](decisions.md).
Storage placement is private to the backend. Owned aggregate transfers move,
borrows read, and shares grant exclusive mutable access. The heap follows
static data and grows at the end of linear memory.

## Current starting point

The [Wasm backend](../../crates/memobits-wasm/src/lib.rs) reserves the first
16 bytes, then lays out the configured stack, the optional outcome return
cell, and reachable String literal descriptors and bytes. The initial Wasm32
memory covers these regions rounded up to 64 KiB pages. Its maximum equals
its initial size. Frame entry checks the stack bound, and normal return
restores the stack pointer. The [typed IR](typed-ir.md) records consuming
operands, initialization, reassignment, and control-flow edges. It has no
drop operation or cleanup insertion pass.

The [static layout planner](../../crates/memobits-wasm/src/memory.rs) now
places the stack, outcome cell and literal regions using one checked cursor.
It preserves the current memory limit and leaves the cursor unchanged after
a failed reservation. The final static end is where a later heap layout
can start its alignment calculation. Allocation and memory growth are
pending the first guest consumer. Current operations only use stack and
static storage, so there is no production call that can exercise growth yet.

## First consumer

Start with an internal operation that concatenates two borrowed Strings into
one independently owned String. The result has exactly the combined byte
length, and concatenating valid UTF-8 preserves validity. This exercises
allocation, ordinary String reads, moves, returns, and cleanup without also
requiring capacity changes or arbitrary-byte validation. Keep the operation
spelling open. Use scalar results to verify it through the existing runner.
Once the foundation works, List can reuse the byte allocator and owned
cleanup. Element initialization, element drops, and capacity changes belong
to later List work.

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
