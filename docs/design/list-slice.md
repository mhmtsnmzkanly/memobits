# First executable List slice

[Accepted collection and ownership decisions](decisions.md) define `List<T>`
as a homogeneous dynamic collection and `Array<T, N>` as fixed-length.
A `let` owner cannot mutate its elements. Primitive elements can be read
by value, `get` uses `Option` for absence, and later removal of an owned
element transfers ownership. Keep the existing fixed-array rules, including
the equivalence of `Bytes<N>` and `Array<u8, N>`.
[Fixed arrays](fixed-array-implementation.md)

## Proposed source scope

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
  receiver is a whole mutable local. Evaluate the element once, before
  allocating, growing, or changing the list. Check conflicting access
  with the existing exclusive loan rules.
- Use `items.len()` for a non-consuming `u32` element count and
  `items.get(index)` for a copied `Option<T>` at a `u32` index.
  Both work on immutable and mutable locals. An out-of-range `get`
  returns `None` before any element load. Subscript syntax can follow
  with the accepted checked-indexing behavior.

These proposed spellings follow the familiar `Vec` operations. The
first slice keeps the access rules and types already used in Memobits.
[Rust Vec](https://doc.rust-lang.org/std/vec/struct.Vec.html)

Scope the owner to whole local bindings, including moves from one local
to another. Defer owned call arguments and returns, reference parameters
and explicit shares, whole-local replacement, nested List storage,
aggregate elements, removal, element references, slices, iterators,
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
Extract byte reservation and block release from descriptor publication
when List becomes the second consumer. Keep String on the same allocator
and retain its allocation failure and alias tests. The four-byte alignment
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

## Implementation and checks

1. Implement the bounded local owner path and the shared block reservation
   and release needed by its first allocation. Keep empty construction
   and unsupported shapes under type and IR validation.
2. Exercise push through a growth boundary, copied reads, and normal-exit
   cleanup in a self-checking example. Run it from source and standalone
   Wasm, and add it to the runnable language guide.
3. Cover empty reads, both element widths, insertion order, exact values
   after growth, and `get` at length and at a high unsigned index. Check
   single evaluation of push arguments, mutation through a `let`,
   use after move, unsupported reference or escape forms, and rejected ABI
   shapes.
4. In one Wasm instance, repeat a fixed workload through fallthrough,
   return, break and continue. Check reuse after the first high-water
   mark, mixed move paths, and preservation of a distinct live list
   across another list's growth and cleanup. Force growth failure under a
   small memory limit and verify the trap. Keep the String reuse and
   allocation-failure tests in the same suite.
