# `Box<T>` implementation notes (H4)

> **Implementation record.** The representation and limits below describe H4
> as shipped. Use the [roadmap](../roadmap.md) and [accepted decisions](decisions.md)
> for current support and open limitations.

`Box<T>` is the alloc layer's single-owner heap box (`use alloc::Box;`). The
language rules are in `decisions.md` ("Stage 4" and "Shipped H4 details"); this
file records how the compiler realizes them.

## Representation

- The checker has its own type, `Ty::Box(T)`, so `Box<T>` and `List<T>` never
  unify and each has its own surface (`Box(v)`, `unbox(b)`, no list methods).
- The IR has its own type `Type::Box(T)` (H4b; H4 lowered a box to a
  one-element `List`). A box is one 4-byte pointer word in its owner; the
  pointer addresses a heap block (the shared 8-byte block header, then one value
  with T's layout). There is no length and no capacity, and an empty (never
  filled, or moved-out) box is the null pointer. A box is a heap leaf in the
  owner predicates (`owns_string_aggregate`, the nominal-owner rule, the tuple
  rule, the analysis `contains_string_owner`) exactly like a List, so the owner
  rules apply unchanged: moves clear the source cell, and scope exit,
  reassignment, `replace`, `swap`, `drop` and early returns release the content
  and then the block exactly once.
- Instructions: a Box local is made with `EmptyList` (null box), filled with
  `ListPush` (reserve one block of T's size, point the cell at it, move the
  value in; the box must be empty), emptied by `ListPop` (move the value into
  the `Option` output, release the block, null the cell) and addressed by
  `ElementAddr` with the constant index 0 (block address plus the header size;
  unchecked). Reusing the owner-slot instructions keeps all validation,
  ownership and loan plumbing shared; the Wasm emitter and the type checks
  branch on `Type::Box`. `Box(v)` is `EmptyList` + `ListPush`; `unbox(b)` moves
  the box into a hidden local, `ListPop`s into an `Option`, extracts the payload
  and lets the emptied hidden box release nothing.
- Layout evidence: `box_cell.rs` fixes `SIZE = 4`, `ALIGN = 4`. The test
  `a_box_occupies_one_pointer_word_where_a_list_occupies_a_descriptor`
  (`memobits-wasm`) lays out `{ Box<i32>, i32 }` (8 bytes vs 16 with a
  `List<i32>`), `[Some(Box<i64>), Nil]` (8 vs 16) and a struct with
  `array<Box<i32>, 4>` (16 vs 48).

## Auto-deref

The checker records, per expression, how many box levels its type has
(`FunctionFacts::box_exprs`). Lowering consults it:

- Field, index and method bases: `Projection::Deref` is an `ElementAddr` of
  element 0 (a checked address that cannot fail), so `b.f`, `b.f = v`,
  `b[i]`, `replace(b.f, v)`, `swap(b.f, c.f)` and method receivers are ordinary
  place chains with loans on the box.
- `match`: an owned box scrutinee is consumed (`take_box_value`, the same
  sequence as `unbox`) unless it is a place; a borrowed one is matched through
  an address of its element. Nested refutable patterns on a payload of type
  `Box<T>` see through it in in-place matches (`decide_match` and
  `bind_in_place` derive the element address); a consuming match does not
  support them (the diagnostic says to bind the box and `unbox` it).
- A `.borrow()` / `.share()` conversion of a box passed where the content type
  is expected lends the content (`FunctionFacts::box_coercions`).
- A by-value method called on a box consumes it (`unbox` of the receiver).

## Recursive types

The by-value recursion check (TE026) only follows struct fields, enum payloads
and arrays, so a `Box`, `List` or `T?` of a box is accepted and direct
recursion is still rejected.

The Wasm backend cannot emit the type-directed release walk of a type that
reaches itself inline. `recursive.rs` finds those types (a cycle through a box
or list element) and emits one `release_T(address)` function per type plus one
shared `drain` function. Releasing is iterative:

1. `release_T` walks the value's own fields inline ("work mode": structs, enums
   and arrays are always inline, which terminates because by-value recursion is
   rejected). A `Box` or `List` position whose element mentions a recursive type
   is not walked; it is *deferred*.
2. Deferring pushes the item on the intrusive worklist of its kind (a Wasm
   global holds each head; a kind is the container, box or list, plus its
   element type). A box item is its block, linked through the free-list word
   of the block header (unused while the block is allocated). A list item is
   its descriptor, linked through the `data` word (a heap List has
   `data == allocation + 8`, restored when the item is popped); an empty list
   is not pushed.
3. `release_T` ends with a call to `drain`, which loops: pop one item of any
   kind, walk its content inline (deferring deeper items), free its block,
   until every worklist is empty.

The call-stack depth is constant: a release site calls `release_T`, which calls
`drain`; neither calls a release function nor itself, and nested kinds are
reached only through the worklists. No memory is needed beyond the structure
because the links live in dead storage (block headers; descriptors inside
blocks that were already freed, whose payload the free list never touches, and
nothing allocates during a release). Types that do not reach themselves keep
their inline release.

User code that builds a deep structure recursively is still limited by the
call stack; only the release is the compiler's responsibility. The allocator
reuses released blocks first-fit from a single free list, so a program that
frees very many blocks of one size and then allocates many larger ones scans
the free list per allocation.

## Limits

- A payload bound by an owned `match` (a `Box` or `List`) cannot be passed
  directly as an owned call argument (`f(rest)`); write `f(unbox(rest))`. This is
  the existing List rule.
- Built-in methods see through a box for named boxes (local, field or element):
  `len`, `get`, `contains`, `index_of`, `is_char_boundary`, `byte_at`,
  `scalar_at`, `push`, `pop` and `clear` (the lowering borrows or shares the
  value through `Projection::Deref`; writes need a `var` box or a `share`
  parameter). `push_str` and `concat` do not, and a box returned by a call must
  be bound first.
- A consuming `match` does not support nested refutable patterns on a box
  payload (TE017): moving owned parts out of a box's content while the block
  stays needs partial-move tracking inside the box. In-place matches do.
- `Box` has no `[prelude]` mapping (the name collides with the virtual `alloc`
  module's own declaration, as for `List`).
- Matching an owned `Box<Box<T>>` consumes one level only.
- `Box<T>` cannot be exported across the entry ABI (own diagnostic).
