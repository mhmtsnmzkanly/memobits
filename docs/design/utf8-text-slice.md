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
`borrow string` parameter provides read-only access to the whole owner
under the existing loan rules. A future substring view would play the role
of Rust's borrowed `str` and carry a loan of its source. Its type name and
source annotation remain open. `share string` is exclusive access under
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
whole value, including owned returns. Internal `borrow string` parameters
use the existing last-use loan rules. A whole assignment through a
`share string` replaces the descriptor under the usual exclusive access rules.

Wasm places reachable literal bytes after the guest stack and any outcome
entry return cell. Frame cells carry a private 32-bit address and byte
length at offsets 0 and 4, and a heap block header address at offset 8.
Static literal descriptors use zero for the header address.
Literal encoding, descriptor loads and frame
layout share one private Wasm layout definition. Moving a String copies the
descriptor through aggregate call and storage paths. Guest code has no
operation that writes to the literal bytes. For an
outcome entry, the runner's existing memory export still exposes linear
memory to the embedding host. Internal `Result<string, E>` can store a
static String in its `Ok` payload. A heap-backed `Ok` is supported when a
local Result binding is immediately followed by a same-function consuming
match with explicit `Ok(value)` and `Err` arms. A direct internal call can
return a heap-backed Result to the same consuming match shape, with or
without a single intervening binding. Other embedded String storage,
borrowed String payload matches, and exported String signatures remain
gated.

## Byte length

Call `.len()` on a String expression, an owned binding, or a whole-string
reference to read its descriptor's UTF-8 byte length as `u32`. The read
obeys move and loan rules and leaves the receiver available after the call.
Byte semantics follow Rust.
Heap allocation, capacity, growth, cleanup, and external text ABI remain
later work. [Rust str::len](https://doc.rust-lang.org/std/primitive.str.html#method.len)

Call `.is_char_boundary(offset)` with a `u32` byte offset on the same
receivers. It returns `Bool`. Zero and the byte length are boundaries,
including zero for empty text. Within the string, any byte that starts a
scalar is a boundary. Continuation bytes and offsets above the length return
false. The read-only receiver loan stays live while evaluating the offset.
Wasm checks the unsigned offset before reading a byte.
[Rust str::is_char_boundary](https://doc.rust-lang.org/std/primitive.str.html#method.is_char_boundary)

`.byte_at(index: u32)` returns an owned `Option<u8>`. It reads raw UTF-8
bytes, including continuation bytes. An unsigned bounds check returns
`None` at or beyond the byte length before any byte load. The receiver
follows the same loan rules as the boundary check.

`.scalar_at(index: u32)` returns an owned `Option<u32>`. The index is a
UTF-8 byte offset. `Some` contains the scalar's numeric Unicode value, for
example 233 for `é`. The existing `u32` type covers the full scalar range
without introducing a public character type. A continuation byte or an
offset at or beyond the byte length returns `None`. Strings already contain
valid immutable UTF-8. After checking the index, Wasm checks the remaining
length against the lead byte's width before loading any trailing bytes.

The language guide demonstrates scalar traversal with a loop: it reads
`.scalar_at(offset)`, advances by the decoded scalar's UTF-8 width, and counts
visited scalars. This keeps scalar count distinct from `.len()` while
preserving byte-offset access. Empty, ASCII, multibyte and supplementary
examples check both quantities. This bounded source-level traversal does not
add a general iterator or change the existing byte-indexed `.scalar_at` API.

The [runnable guide](../../examples/projects/language-guide/src/main.mb)
checks empty, ASCII, and multibyte text from source and standalone Wasm.
CLI tests cover owner reads during a read-only loan, last-use release,
and rejected reads after a move or during a live exclusive loan.

## Later operations

Use Rust's operations as semantic references. Byte traversal or a read-only
byte view exposes the encoded bytes. Scalar traversal yields Unicode scalar
values and can report their starting byte offsets. An individual scalar
may be only part of a user-perceived character. Keep byte/scalar API names,
iterator representation and the scalar type open.
[Rust str::bytes](https://doc.rust-lang.org/std/primitive.str.html#method.bytes) ·
[Rust str::char_indices](https://doc.rust-lang.org/std/primitive.str.html#method.char_indices)

The runnable guide already walks mixed text with an explicit loop. It reads
each scalar with `scalar_at`, advances by that scalar's UTF-8 width, and
checks the starting byte offsets and final length.

Text slicing should use checked half-open byte ranges. Require
`0 <= start <= end <= byte length` and both endpoints on scalar boundaries.
Zero and the byte length are valid endpoints. In `Aé`, the range `[1, 3)`
yields `é` and `[1, 2)` fails. Prefer a fallible operation for invalid
ranges, along the lines of Rust's `get`. Single-integer string indexing
remains unsupported. A `borrow string` points to the owner's whole descriptor.
A subrange needs its own base address and length while retaining the loan of
the original owner. A borrow of a temporary descriptor would instead track
the temporary's storage. The current local `Option<borrow T>` can carry a
reference to an existing place, but it cannot provide a branch or call result
that ties a newly derived view to the input loan. Loan checking rejects
reference-valued call results, and borrow Options cannot cross IR block edges
or appear in signatures.

A bounded slice therefore needs a view representation, a checked projection
that preserves source provenance, and rules for transporting the fallible
result without letting it outlive its source. A conservative loan of the
whole source is sufficient for a first read-only view. Return types and
syntax remain open. [Rust str::get](https://doc.rust-lang.org/std/primitive.str.html#method.get) ·
[Rust str::is_char_boundary](https://doc.rust-lang.org/std/primitive.str.html#method.is_char_boundary)

## Strict validation of fixed bytes

`bytes.validate_utf8(length)` borrows a fixed `Bytes<N>` or its equivalent
`Array<u8, N>`. It takes an `i32` logical length and returns
`Result<i32, Utf8Error>`. Success gives the number of Unicode scalars.
`Utf8Error` derives from `Error` and adds an `offset: Option<i32>` field,
using the codes and offsets below. The compiler infers the bound from the
receiver. Wasm checks the length before any byte load and validates without
allocating or changing the input. The guest validator uses this operation
for its boundary and malformed-byte fixtures.

## Fallible construction from fixed bytes

`bytes.to_utf8_string(length)` returns `Result<string, Utf8Error>` from
the logical prefix of a fixed byte array. The method sits alongside
`validate_utf8` on the byte receiver. The `to` spelling reflects that it
borrows the input and makes an owned copy. The length is an `i32` and the
receiver supplies the bound. This matches
the [guest validator](../../examples/projects/utf8-validator/README.md)
and keeps the caller's fixed buffer available on either outcome. Success
copies exactly the validated prefix into private String storage. Padding
is ignored, embedded NUL is preserved, and a zero-length prefix yields
empty text.

Rust's `String::from_utf8` takes ownership of a `Vec<u8>` and can reuse its
allocation. A Memobits fixed array has a different layout and no transferable
String allocation. Borrowing the fixed input and copying the prefix gives
the owned result without consuming the buffer. Replacement-character
decoding is outside this strict constructor.
[Rust String::from_utf8](https://doc.rust-lang.org/std/string/struct.String.html#method.from_utf8)

### Outcomes and offsets

Use an internal `Result<string, Utf8Error>` with the validator's error
shape, a derived error carrying `offset: Option<i32>`. Validate the length
before indexing and report the first failing byte. Offsets are zero-based
within the logical prefix.

| Input prefix or length | Outcome |
| --- | --- |
| `[195, 169, 0]`, length 3 | `Ok` with exactly these three UTF-8 bytes |
| Any buffer, length 0 | `Ok` with empty text |
| Length below 0 or above the fixed bound | Code 1, no offset |
| `[128]`, length 1 | Code 2, invalid lead at offset 0 |
| `[195]`, length 1 | Code 3, first missing byte at offset 1 |
| `[226, 65]`, length 2 | Code 4, invalid continuation at offset 1 |

Use the validator's lead-specific ranges for overlong sequences, surrogates
and values above U+10FFFF. A present invalid byte takes precedence over a
later missing byte. Perform the complete validation before requesting heap
storage. Allocation failure then follows the existing guest heap trap and
instance-discard behavior. `Err(Utf8Error)` represents length or encoding
failure. No descriptor is published on allocation failure.
[Heap foundation](owned-heap-foundation.md)

### Compiler prerequisite and implementation order

This internal function with a scalar entry exercises the supported static
case with the application entry ABI left scalar.

```mb
fn construct() -> Result<string, Error> { Ok("é") }

fn main() -> i32 {
    match construct() { Ok(text) => if text.len() == 2 { 0 } else { 1 }, Err(_) => 2 }
}
```

The static case uses the private String descriptor layout in `Ok` and
the existing aggregate return and extraction paths. The descriptor's
allocation field stays zero. Replacing the body with
`let text := "é".concat("!"); Ok(text)` transfers a heap owner through
the same internal ABI to the immediate consuming match. The application
outcome ABI continues to require a primitive success payload.
[Wasm member layout](../../crates/memobits-wasm/src/lib.rs) ·
[Heap String IR validation](../../crates/memobits-ir/src/lib.rs)

1. Implemented internal `Result<string, E>` for static success descriptors,
   including construction, return, receipt and consuming match. A String
   local or internal call result can be used when heap provenance is absent.
   Containers of these results and external signatures remain gated.
2. Implemented same-function heap `Ok` with an immediate consuming match.
   The IR validator requires a named String moved into `Ok`, a Result
   binding, and the very next operation to match that binding. Both arms
   must be explicit and the success arm must bind the String. Packing clears
   the original owner's allocation field. Extraction transfers ownership to
   the arm binding, whose normal-exit cleanup releases or moves it exactly
   once. Tests cover early arm returns and repeated reuse.
3. Implemented ownership transfer across direct internal Result returns.
   The callee packs its String local before lexical cleanup and returns the
   descriptor in the caller's aggregate result cell. The caller immediately
   matches it or binds it and then immediately matches it. Any call to a
   function that can return a heap `Ok` needs explicit `Ok(value)` and
   `Err` arms, including calls that take a static or error path at runtime.
   Argument cleanup may run before the match. Unconsumed results, borrowed
   matches, wildcard discards and forwarding a Result without matching it
   remain gated.
4. The private Wasm allocator now copies byte ranges into a new String
   descriptor. Production concat supplies both ranges from its live
   String inputs. A constructor can supply its logical prefix and an
   empty second range.
5. Implemented the compiler-provided prefix validator and typed error.
   It borrows the input, checks the inferred bound, and reports the
   first malformed or missing byte without allocating.
6. Implemented `to_utf8_string` using the same private validator and
   byte-range allocator. Invalid prefixes return the typed error before
   allocation. A valid prefix is copied directly into the `Ok` descriptor.
   Immediately match the Result with explicit `Ok(value)` and `Err` arms,
   or return it directly from an internal function whose callers do so.

Run the executable slices from source and as standalone Wasm with a
primitive self-checking entry. Verify exact bytes and scalar reads, all
validator error classes and offsets, success and error arms, repeated
same-instance reuse, and a forced heap-growth failure on valid input.
Under the same memory limit, invalid bytes must still return their
validation error.

## Later String optimization

After the first executable slice, evaluate `smol_str`, `compact_str`,
`smartstring`, `arcstr`, `ecow`, `lasso`, and `string-interner` as design
references from a local note. Compare promising approaches against the
initial representation with representative workloads, measuring allocations
and runtime while preserving owned moves, borrow rules, and valid UTF-8.
