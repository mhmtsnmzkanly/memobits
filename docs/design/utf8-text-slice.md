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

## Executable literals and ownership

Single-line double-quoted literals carry direct UTF-8 text, including the
empty literal. The frontend rejects escapes, line breaks (LF and CR), and
unterminated literals. Raw literals and interpolation remain pending.

String literals retain their UTF-8 payload in typed IR. Ownership checks and
execution use the same IR. Owned bindings and internal calls transfer the
whole value, including owned returns. Internal `borrow String` parameters
use the existing last-use loan rules. A whole assignment through a
`share String` replaces the descriptor under the usual exclusive access rules.

Wasm places reachable literal bytes after the guest stack and any outcome
entry return cell. Frame cells carry a private 32-bit address and byte
length. Moving a String copies that descriptor through the aggregate call
and storage paths. Guest code has no operation that writes to the literal
bytes. The descriptor and data layout are private to the backend. For an
outcome entry, the runner's existing memory export still exposes linear
memory to the embedding host. Exported String signatures and embedded
String storage in arrays, structs, or enum payloads are gated.

## Next executable slice

Propose a non-consuming `.len()` on an owner or whole-string borrow,
returning the stored byte length as `u32`. Byte semantics follow Rust.
Heap allocation, capacity, growth, cleanup, and external text ABI remain
later work. [Rust str::len](https://doc.rust-lang.org/std/primitive.str.html#method.len)

Check lengths for empty text (0), ASCII `abc` (3), `é` (2), and `😀` (4).
Include a mixed literal, repeated reads through a borrow, and a move.
Check rejected integer indexing and use after move. Run a scalar outcome
entry from source and as standalone Wasm and assert identical output.

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

## Later String optimization

After the first executable slice, evaluate `smol_str`, `compact_str`,
`smartstring`, `arcstr`, `ecow`, `lasso`, and `string-interner` as design
references from a local note. Compare promising approaches against the
initial representation with representative workloads, measuring allocations
and runtime while preserving owned moves, borrow rules, and valid UTF-8.
