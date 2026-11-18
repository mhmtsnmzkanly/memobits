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
A direct move into another immutable local transfers the owning descriptor.
A direct internal call can take multiple owned String arguments in any
parameter position. Arguments evaluate left to right. An earlier move from
a local stages the descriptor in a hidden immutable binding, which gets
lexical cleanup if later evaluation returns, breaks, or continues out of
the call. Invocation transfers the staged descriptors to callee parameters.
A trap discards the instance, including any staged allocations.
A function can return an owning local through a direct internal call whose
result directly initializes a new immutable caller local. Discarded results,
result temporaries, sharing for mutation and replacement require broader drop
elaboration. A nonzero descriptor
provenance field points to the owned block's header. A move clears that
field in the source. Zero provenance covers static bytes and moved slots,
and cleanup skips either.

Guest allocation grows memory only as needed, after checking the widened
exclusive byte end and its page ceiling. A failed grow traps at the concat
call before publishing a descriptor or changing the allocator state.
Scope exit puts the block on a private free list. Concat tries the first
fitting block before extending the heap. Headers are four-byte aligned and
store capacity independently of the String's current byte length, so a
smaller reuse preserves the larger block's capacity. Blocks are reused
whole, and memory pages remain at their high-water mark. The existing
lexical gate still verifies scope exits and prevents unsupported escapes.

Once the foundation works, List can reuse the byte allocator and owned
cleanup. Element initialization, element drops, and capacity changes belong
to later List work.

## Audit of scoped allocation

At each reachable block entry, the IR validator requires every incoming
edge to agree on the heap bindings still in scope, even when their move
states differ. A callee must end all of its heap bindings before returning.
Heap capability propagates through direct arguments and returns, including
forwarding calls. A return stages the descriptor and clears the source
provenance before lexical cleanup. The caller receives the descriptor in its
private result cell and moves it into the new binding after staged argument
cleanup. Calls that may return heap text require this binding even on paths
that return static text. Static-only results retain ordinary String behavior.
The callee copies the incoming descriptor into its owned parameter cell
and clears the caller slot's provenance before executing the body.
Release uses the block address, so it preserves other live allocations
regardless of their order. The move and loan checks run before Wasm emission
and reject a move or release while a borrow remains live. Two inputs may
borrow the same String. Both reads finish
before the result is published. Copies target a freed block or a new extent
disjoint from both live inputs. These guarantees assume the generated guest controls its
memory. A host with access to the private outcome memory export must preserve
the guest's descriptors and bytes.

Regression cases exercise aliased input, recursive borrowing of a heap
String, reuse after a callee releases its allocations, and an intentionally
premature exit with a live borrow. Normal return, break and continue also
have page-reuse coverage.

## Progression to arbitrary ownership

1. The lexical consumer now uses the
   [shared descriptor layout](../../crates/memobits-wasm/src/string_descriptor.rs)
   to locate an allocation record and reuse freed blocks. Tests cover a
   larger block reused for a smaller request, then reused at full size.
2. Local moves now transfer the release obligation with the descriptor.
   Scope exit consults provenance, so mixed paths need no separate flag.
   Tests cover moving an older allocation while a newer allocation remains
   live, and moving on one branch while retaining the original on another.
3. Direct return transfers the result before dropping the callee's other
   owners. Tests cover early returns, a static alternative, forwarding and
   repeated reuse in the same Wasm instance.
4. Extend normal-exit cleanup to discarded results and general temporaries.
   Evaluate a replacement before releasing the previous owner, including whole
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

The private guest allocator uses an end cursor and a free list of
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
operation for static locals. For a heap String local, the backend releases
the allocation if its descriptor still owns a block. The move transfer
clears the source's ownership field, and scope exit marks the local
unavailable regardless of its incoming state. Other owner types and
temporary cleanup remain separate work.

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
