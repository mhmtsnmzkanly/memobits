# `Box<T>` implementation notes (H4)

`Box<T>` is the alloc layer's single-owner heap box (`use alloc::Box;`). The
language rules are in `decisions.md` ("Stage 4" and "Shipped H4 details"); this
file records how the compiler realizes them.

## Representation

- The checker has its own type, `Ty::Box(T)`, so `Box<T>` and `List<T>` never
  unify and each has its own surface (`Box(v)`, `unbox(b)`, no list methods).
- The IR lowers `Box<T>` to `Type::List(T)` holding exactly one element. Every
  list owner rule therefore applies to a box without a new IR type: moves clear
  the source descriptor, scope exit, reassignment, `replace`, `swap`, `drop` and
  early returns release the element and then the block exactly once, and a box
  is a heap leaf in the owner predicates (`owns_string_aggregate`, the
  nominal-owner rule, the tuple rule, the analysis `contains_string_owner`).
- Consequence for layout: a box occupies the 12-byte List descriptor in its
  owner, not a single pointer word, and its block is the list block of one
  element (8-byte block header plus the element). A pointer-word box is a
  possible later representation change; it would only touch the Wasm layout,
  the cleanup emitter and the three box instructions it needs.
- `Box(v)` is a one-element list literal (`EmptyList`, `ListPush`). `unbox(b)`
  moves the box into a hidden list, `ListPop`s the element into an `Option`,
  extracts the payload and lets the emptied hidden list release the block.

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
reaches itself inline. `recursive.rs` finds those types (a cycle through a list
element) and emits one release function per type; every release site calls it
and the function calls itself for the recursive positions. Releasing a long
chain recurses once per node, so a chain of several hundred thousand nodes
exhausts the engine's call stack and traps; chains of a few hundred nodes are
tested.

## Limits

- A payload bound by an owned `match` (a `Box` or `List`) cannot be passed
  directly as an owned call argument (`f(rest)`); write `f(unbox(rest))`. This is
  the existing List rule.
- Built-in string and List methods (`len`, `push`, `contains`, ...) do not see
  through a box; bind or `unbox` the contents first. User-defined methods do.
- Matching an owned `Box<Box<T>>` consumes one level only.
- `Box<T>` cannot be exported across the entry ABI (no String/List exports).
