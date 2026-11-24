# First executable List slice

[Accepted collection and ownership decisions](decisions.md) define `List<T>`
as a homogeneous dynamic collection and `array<T, N>` as fixed-length.
A `let` owner cannot mutate its elements. Primitive elements can be read
by value, `get` uses `Option` for absence, and later removal of an owned
element transfers ownership. Keep the existing fixed-array rules, including
byte buffers as `array<u8, N>`.
[Fixed arrays](fixed-array-implementation.md)

## General List<T> (E1b)

`List<T>` accepts any admitted element type: primitives of every width,
`bool`, `char`, `string`, owner structs, tuples, enums and fixed arrays.
Internally it is `Type::List(Box<Type>)` with a private 12-byte descriptor
(data address, element count, allocation handle); the element stride comes from
the Wasm layout. Nested `List<List<T>>`, List fields of structs and tuples,
arrays of Lists and List payloads of enums are supported (G1, F2).

- Literals: with an expected `List<T>`, `[a, b, c]` builds the list. Elements
  evaluate once in written order and move in (owner elements are staged like
  array elements). `[]` stays the empty list.
- `push(value)` moves the element in; `pop()` returns `T?` and moves an owner out
  (the shortened list no longer owns the vacated slot).
- Growth reserves a new block, moves the existing element bytes bitwise and
  releases only the old block, never its elements.
- Cleanup is type-directed: drop, `clear`, whole-list reassignment, scope exit
  and early returns walk the initialized elements, release each owned element
  once, then release the block. A moved-from List descriptor is zeroed so a later
  visit of the slot walks nothing.
- `items[i]` is a bounds-checked element place (`ElementAddr` over the List
  descriptor; out of range traps RE007). Primitive elements are copied (and can
  be written on a `var` list). Non-copyable elements are used in place: as
  `borrow`/`share` receiver or argument, in an in-place `match`, or through a
  projection (`items[i].text.len()`). Moving one out and overwriting an owning
  element are TE022 (`replace`/`swap` arrive with R1; `pop` exists). A live
  element loan blocks `push`, `pop`, `clear`, moves and reassignment of the
  list (loan checker, owner granularity, BE005).
- `get(i) -> T?` is for copyable (primitive) elements; other elements get TE022
  pointing at `items[i]`. `contains` and `index_of` accept primitive elements of
  any width; other element types are TE017.
- `loop x in items` binds copies of primitive elements and read-only loans of
  non-copyable elements (`x` behaves like a borrowed parameter: projections and
  in-place use only). The list stays loaned for the whole loop, so mutating it in
  the body is BE005.
- Entry/export ABI is unchanged: Lists are not entry results and cannot cross an
  exported signature.
- Runnable guide: `examples/guide/src/collections.mb`
  (`list_element_types`, `list_of_strings`, `list_of_owner_structs`,
  `list_of_tuples_and_arrays`); stress and negatives in
  `crates/memobits-cli/tests/e1b_lists.rs`.

## Executable checkpoint (original primitive slice)

The rules below were written for `List<u8>` and `List<u32>` and still hold for
every element type unless the E1b section above says otherwise.

`List<u8>` and `List<u32>` support contextual empty `[]`, moves into new
local bindings, non-consuming `.len()`, `.get(index)`, `.contains(value)`,
and `.index_of(value)`, plus `.push(value)`, `.pop()`, and `.clear()` on
whole mutable locals. Empty construction
allocates no heap block. A push evaluates the element once and returns unit.
Moves transfer the block and normal scope exits release the owner. `List<T>` is a compiler-implemented
library type in the Rust-owned virtual module `alloc` and needs
`use alloc::List;` (or `use alloc;` and `alloc::List<T>`); without the import it
is an unknown-type error whose note names the import. The applied spelling is
reserved; a module that does not import it can still declare a bare user type
named `List`. `[build] alloc = false` removes the module (ME012) and the
allocator, so Lists are unavailable there. Direct internal calls accept `borrow List<T>`
for these element types. Use `.borrow()` on a whole local to create the
read-only handle. A direct borrow parameter also accepts `make_list().borrow()`
as the argument itself when the factory is a direct internal call. The caller
evaluates the factory once in argument order and owns the result until the
call finishes. Normal early exits during later arguments release the temporary
through lexical cleanup. Storing that borrow or sharing a temporary is
unsupported. The callee can use `.len()`, `.get()`, `.contains()`, and
`.index_of()`. A live loan blocks mutation, moves and cleanup of the
owner until its last use.
A direct `share List<T>` parameter accepts an explicit `.share()` from
a mutable owner and supports `push`, `pop`, `clear`, `len`, `get`,
`contains`, and `index_of`. Growth updates the caller descriptor in place,
and the caller retains cleanup responsibility.
A direct internal owned parameter takes a named whole List local by move
or a direct internal List call result, as in `consume(make_list())`.
Arguments evaluate left to right. An earlier owned argument is staged
until invocation, and normal exits before the call release it in the caller.
Once invoked, the callee owns and cleans up the block. A direct internal
function can also return a named whole List local. Assign the call result
directly to a new local or to an existing mutable local. The callee stages
the descriptor before ending its local scopes. The receiving binding owns
the block and releases it on a normal exit unless it moves onward.
A direct share parameter or a `var` share handle can also receive a
replacement List. The original owner retains ownership and cleanup.
A standalone direct internal call statement releases its unused List result
immediately via the same lexical cleanup as a named owner. A direct internal
call result can also be the receiver of `.len()`, `.get(index)`,
`.contains(value)`, or `.index_of(value)`. The call runs once before any
argument and its result lives in a temporary owner until the read finishes.
Normal early exits during argument evaluation release it through lexical
cleanup. Other temporary uses, indirect calls, nesting, subscript syntax,
and exports remain gated.
[Runnable guide](../../examples/guide/src/main.mb)

## Source scope

The first slice started with `List<u8>` and `List<u32>` (E1b generalized the
element type). They exercise one-byte and
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
  `items.get(index)` for a copied `T?` at a `u32` index. Both work
  on immutable and mutable locals. The index expression runs once before
  the read. An out-of-range `get` returns `None` before computing an
  element address or loading a value. Subscript syntax can follow with
  the accepted checked-indexing behavior.

- Use `items.contains(value) -> bool` to check membership and
  `items.index_of(value) -> u32?` to get the first zero-based match.
  Both use primitive `==` and require a search value of the element type.
  The methods borrow the receiver before evaluating the value once, then
  scan the initialized elements up to the first match. If no element
  matches, including on an empty List, they return false and `None`,
  respectively.
  Locals, borrow and share bindings or parameters, and direct internal
  List call results are supported.

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

## List iteration

`loop value in items { ... }` supports every List element type (non-copyable
elements are lent, see E1b). The
receiver can be a whole local binding, a borrow or share binding or parameter,
or a direct internal List call. Other List-valued expressions are gated.

The loop evaluates the receiver once and visits elements in insertion order.
Each iteration binds an immutable copy. An empty List skips the body.
A read loan blocks writes and moves of the receiver throughout the body and
ends when the loop exits. `continue` advances to the next element,
`break` exits the loop, and `return` exits the function. A direct call
result stays alive across iterations and is released on exhaustion, break,
or return.

[Runnable language guide](../../examples/guide/src/main.mb)

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

An unshadowed `drop(items)` consumes an available whole owned List local
or parameter and releases its block immediately. A live loan blocks the
drop. The operation clears the allocation marker, so later scope cleanup
can handle both dropped and still-owned paths. Assignment can restore a
dropped mutable binding. The same operation supports owned String locals.

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
   standalone Wasm. They also cover clearing, refilling, and discarding call
   results. Wasm tests check that popping the last element or clearing retains
   the backing block.
3. Cover empty reads, both element widths, insertion order, exact values
   after growth, and `get` at length and at a high unsigned index. Check
   single evaluation of push arguments, mutation through a `let`,
   use after move, live-borrow conflicts, successful push and move after
   last use, ownership transfer across arguments and returns, skipped-call
   cleanup, unsupported escapes, and rejected ABI shapes.
4. In one Wasm instance, repeat a fixed workload through fallthrough,
   return, break and continue. Check reuse after the first high-water
   mark, mixed move paths, and preservation of a distinct live list
   across another list's growth and cleanup. Repeat discards of large direct
   call results in one instance to check storage reuse. Repeat temporary reads
   across successful reads and index return, break, and continue paths.
   Repeat calls with borrowed and owned temporaries across successful calls
   and later argument return, break, and continue paths.
   Force growth failure under a small memory limit and verify the trap.
   Keep the String reuse and allocation-failure tests in the same suite.
