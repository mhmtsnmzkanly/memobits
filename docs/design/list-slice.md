# First executable List slice

[Accepted collection and ownership decisions](decisions.md) define `List<T>`
as a homogeneous dynamic collection and `Array<T, N>` as fixed-length.
A `let` owner cannot mutate its elements. Primitive elements can be read
by value, `get` uses `Option` for absence, and later removal of an owned
element transfers ownership. Keep the existing fixed-array rules, including
the equivalence of `Bytes<N>` and `Array<u8, N>`.
[Fixed arrays](fixed-array-implementation.md)

## Executable checkpoint

`List<u8>` and `List<u32>` support contextual empty `[]`, moves into new
local bindings, non-consuming `.len()` and `.get(index)`, plus `.push(value)`,
`.pop()`, and `.clear()` on whole mutable locals. Empty construction
allocates no heap block. A push evaluates the element once and returns unit.
Moves transfer the block and normal scope exits release the owner. The applied spelling is built in, and bare `List`
can still name a user type. Direct internal calls accept `borrow List<T>`
for these element types. Use `.borrow()` on a whole local to create the
read-only handle. The callee can use `.len()` and `.get()`. A live loan
blocks mutation, moves and cleanup of the owner until its last use.
A direct `share List<T>` parameter accepts an explicit `.share()` from
a mutable owner and supports `push`, `pop`, `clear`, `len` and `get`. Growth
updates the caller descriptor in place, and the caller retains cleanup
responsibility.
A direct internal owned parameter takes a named whole List local by move.
Arguments evaluate left to right. An earlier owned argument is staged
until invocation, and normal exits before the call release it in the caller.
Once invoked, the callee owns and cleans up the block. A direct internal
function can also return a named whole List local. Assign the call result
directly to a new local or to an existing mutable local. The callee stages
the descriptor before ending its local scopes. The receiving binding owns
the block and releases it on a normal exit unless it moves onward.
A direct share parameter or a `var` share handle can also receive a
replacement List. The original owner retains ownership and cleanup.
Discarded or temporary results, indirect calls, nesting, subscript syntax,
and exports remain gated at this checkpoint.
[Runnable guide](../../examples/projects/language-guide/src/main.mb)

## Source scope

Start with `List<u8>` and `List<u32>`. They exercise one-byte and
four-byte element storage and fit the current payload alignment. Both
have existing primitive load/store and `Option` support, and neither
needs per-element cleanup. Additional primitives can follow a consumer
or a coverage need.

- Use `var items: List<u32> = [];` for an empty list. This reuses
  contextual empty-literal syntax. A List annotation selects List, and
  existing array contexts continue to select Array. Defer nonempty List
  literals, repetition, and conversion from arrays.
- Use `items.push(value)` to append one element and return unit. The
  receiver is a whole mutable local, a direct exclusive parameter, or a
  stored mutable share handle.
  Evaluate the element once, before
  allocating, growing, or changing the list. The argument can read the
  receiver's length. A move of the receiver during argument evaluation
  makes the subsequent push invalid.
- Use `items.pop()` to remove the last element as `Some(value)` or return
  `None` when empty. It accepts the same receivers and follows the same loan
  rules as `push`. It keeps the backing block and capacity even when the List
  becomes empty.
- Use `items.clear()` to set the length to zero and return unit, including
  when the List is already empty. It follows the same receiver and loan rules
  as `pop` and retains capacity for subsequent pushes.
- Use `items.len()` for a non-consuming `u32` element count and
  `items.get(index)` for a copied `Option<T>` at a `u32` index. Both work
  on immutable and mutable locals. The index expression runs once before
  the read. An out-of-range `get` returns `None` before computing an
  element address or loading a value. Subscript syntax can follow with
  the accepted checked-indexing behavior.

These proposed spellings follow the familiar `Vec` operations. The
first slice keeps the access rules and types already used in Memobits.
[Rust Vec](https://doc.rust-lang.org/std/vec/struct.Vec.html)

Scope the owner to whole local bindings, including moves from one local
to another. Borrow and share parameters receive the caller's private
descriptor address for the direct call. A share follows the usual
exclusive loan rules. A stored `var` share handle also supports `push`,
`pop`, and `clear`. A live child borrow blocks mutation until its last use, and a stored
`let` handle remains read-only.
An owned parameter receives its own frame descriptor and takes the
allocation from the caller's moved slot. A return clears the moved
callee slot before cleanup and transfers the staged descriptor through
the caller's private aggregate return cell. A direct share parameter or
a stored `var handle := items.share()` can receive an empty List, a moved
List local, or a direct List call result. Stored `let` handles remain
read-only under the existing assignment convention. Defer nested List storage,
aggregate elements, indexed removal, element references, slices, iterators,
capacity controls, and exports. Keep those forms gated until their
ownership or ABI paths are covered. The first consumer can build a list
in a loop and check inserted values, order, and the first absent index
from a primitive-returning entry.

## Private Wasm storage and cleanup

An empty owner needs no heap block. For a nonempty owner, track the
allocation and the initialized element count, with storage capacity kept
private. Read only indices below that count. Compute the required byte
extent from element width and count using widened arithmetic. Check
alignment, address arithmetic, and the existing Wasm32 limit of 65,535
64 KiB pages before growing memory. Keep the private growth policy free
to change.

The [current heap](owned-heap-foundation.md) has a checked cursor,
four-byte-aligned whole blocks and a first-fit free list. Its current
copy helper reads live byte ranges and publishes a String descriptor.
Byte reservation and block release are shared by String and List.
List uses the byte capacity in the allocated block's header. Both
consumers keep their allocation-failure and reuse tests. The four-byte alignment
suffices for the proposed elements. Wider-aligned elements need a separate
layout decision when they are introduced.
[Current Wasm allocator](../../crates/memobits-wasm/src/string_heap.rs)

If existing capacity fits, store the element and then increase length.
Otherwise reserve a block, copy only initialized elements, append the new
element, then install the replacement and release the old block. Keep the
old owner live during allocation and copying. A failed reservation leaves
the descriptor and allocator state intact and uses the existing heap
allocation trap. The runner discards a trapped instance. Normal exits
release the owner once. A move transfers the block and clears the source
ownership marker, so mixed moved/live paths can use the existing cleanup
approach. Freed blocks are reusable, and committed pages stay at their
high-water mark.

Whole mutable local assignment evaluates the RHS before releasing the old
block. The RHS may borrow that List while rebuilding it. Assigning `[]`
releases the old block and installs an empty descriptor. A moved slot has
zero allocation provenance, so the same assignment handles both paths
after a conditional move. Self-assignment keeps the descriptor in place,
with the usual availability and loan checks. Whole replacement through a
direct or stored share uses the same RHS order. It writes the owner's
descriptor and releases the previous block. A live child borrow blocks the write,
and an early exit during RHS evaluation leaves the caller's List intact.

## Implementation and checks

1. Empty local owners, length, push, pop, clear, growth and normal-exit cleanup are
   executable. The language guide runs from source and standalone Wasm.
2. The Wasm test checks both element widths, payload addresses, exact bytes
   after growth, repeated reuse and a forced allocation trap. The CLI
   regressions check copied reads after growth and LIFO removal in source and
   standalone Wasm, along with clear and refill. Wasm tests check that popping
   the last element or clearing retains the backing block.
3. Cover empty reads, both element widths, insertion order, exact values
   after growth, and `get` at length and at a high unsigned index. Check
   single evaluation of push arguments, mutation through a `let`,
   use after move, live-borrow conflicts, successful push and move after
   last use, ownership transfer across arguments and returns, skipped-call
   cleanup, unsupported escapes, and rejected ABI shapes.
4. In one Wasm instance, repeat a fixed workload through fallthrough,
   return, break and continue. Check reuse after the first high-water
   mark, mixed move paths, and preservation of a distinct live list
   across another list's growth and cleanup. Force growth failure under a
   small memory limit and verify the trap. Keep the String reuse and
   allocation-failure tests in the same suite.
