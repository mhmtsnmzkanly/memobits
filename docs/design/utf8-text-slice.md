# UTF-8 text and the first executable slice

[Accepted Memobits decisions](decisions.md) give string literals owned
`String` semantics, require UTF-8, and separate byte length from scalar
iteration. The API and storage choices below are proposals for staging that
design.

## Ownership and validity

Rust `String` owns growable UTF-8 text. Rust `str` is the text slice type,
usually accessed as `&str`. Rust string literals have type `&'static str`.
[Rust String](https://doc.rust-lang.org/std/string/struct.String.html) ·
[Rust str](https://doc.rust-lang.org/std/primitive.str.html) ·
[Rust literal expressions](https://doc.rust-lang.org/reference/expressions/literal-expr.html#string-literal-expressions)

In Memobits, `String` follows existing aggregate move rules. An internal
`borrow String` parameter provides read-only access to the whole owner
under the existing loan rules. A future substring view would play the role
of Rust's borrowed `str` and carry a loan of its source. Its type name and
source annotation remain open. `share String` is exclusive access under
the existing ownership rules. Future text mutations through it must preserve
UTF-8, and require an API of their own.

Every safe string and text view contains valid UTF-8 for Unicode scalar
values. Literal construction establishes the invariant. Later construction
from arbitrary bytes must validate before yielding text. Raw bytes can stay
in byte buffers. The [guest validator](../../examples/projects/utf8-validator/README.md)
already exercises that distinction.

## Proposed first executable slice

- Support single-line, double-quoted literals with direct UTF-8 text,
  including the empty literal. Keep escape grammar, raw literals, and
  interpolation outside this first slice. Accepted interpolation semantics
  remain a separate implementation milestone.
- Support local owned bindings and moves, plus read-only internal parameters
  using `borrow String` and explicit `.borrow()` at the call site. A move
  invalidates the old binding just as it does for other aggregates.
- Expose a non-consuming byte-length operation on an owner or on a whole
  string borrow. Propose `.len()` with a `u32` result for this bounded slice.
  Byte semantics follow Rust, while Memobits uses an existing integer type
  for a portable scalar result. Reject a literal whose encoded length exceeds
  that range. [Rust str::len](https://doc.rust-lang.org/std/primitive.str.html#method.len)
- Immutable Wasm data with a private descriptor is one possible lowering
  because the slice only creates text from literals. A literal still behaves
  as an owned value. Defer heap allocation, capacity, growth, cleanup, and
  representation and ABI commitments. Keep text out of exported signatures.

Verify byte lengths of empty text (0), ASCII `abc` (3), `é` (2), and `😀`
(4). Include a mixed literal and read one value twice through a borrow.
Verify that a move preserves its length and that reading the old binding is
rejected. Cover malformed literals and rejected integer indexing. Run a
self-checking example with a scalar outcome entry both from source and from
a standalone Wasm build in a temporary directory, and assert identical output.

## Later operations

Use Rust's operations as semantic references. Byte traversal or a read-only
byte view exposes the encoded bytes. Scalar traversal yields Unicode scalar
values and can report their starting byte offsets. An individual scalar
may be only part of a user-perceived character. Keep byte/scalar API names,
iterator representation and the scalar type open.
[Rust str::bytes](https://doc.rust-lang.org/std/primitive.str.html#method.bytes) ·
[Rust str::char_indices](https://doc.rust-lang.org/std/primitive.str.html#method.char_indices)

Text slicing should use checked half-open byte ranges. Require
`0 <= start <= end <= byte length` and both endpoints on scalar boundaries.
Zero and the byte length are valid endpoints. In `Aé`, the range `[1, 3)`
yields `é` and `[1, 2)` fails. Prefer a fallible operation for invalid
ranges, along the lines of Rust's `get`. Single-integer string indexing
remains unsupported. A borrowed slice or byte view must stay within its
source loan, so defer these results until reference provenance and escape
checking can support them. The exact return type and range syntax remain
open. [Rust str::get](https://doc.rust-lang.org/std/primitive.str.html#method.get) ·
[Rust str::is_char_boundary](https://doc.rust-lang.org/std/primitive.str.html#method.is_char_boundary)
