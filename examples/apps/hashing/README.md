# Hashing Primitives & Algorithms

This example implements standard non-cryptographic hashing algorithms (**FNV-1a 32-bit**, **DJB2**, and **Adler-32**) over byte arrays (`array<u8, N>`) in Memobits, exploring how to safely implement bitwise operations and wrapping arithmetic on an engine with checked arithmetic.

## Implemented Algorithms

1. **FNV-1a 32-bit (`src/fnv.mb`)**:
   - Initial offset basis: `2166136261` (`0x811c9dc5`)
   - FNV prime: `16777619` (`0x01000193`)
   - Algorithm: For each byte, XOR with current hash, then multiply by the FNV prime modulo $2^{32}$.

2. **DJB2 32-bit (`src/djb2.mb`)**:
   - Initial hash: `5381`
   - Algorithm: For each byte, `hash = ((hash * 33) + byte) mod 2^32`.

3. **Adler-32 (`src/adler.mb`)**:
   - Modulo: `65521` (largest prime smaller than $2^{16}$)
   - Two 16-bit accumulators: $A = 1$, $B = 0$.
   - Algorithm: For each byte, $A = (A + \text{byte}) \pmod{65521}$, $B = (B + A) \pmod{65521}$.
   - Result: $(B \ll 16) \mid A$, combined via bitwise OR and shifting.

## Handling Checked Arithmetic & Bitwise Operations

Memobits enforces runtime bounds checks on primitive integer operations (`+`, `-`, `*`). Any arithmetic overflow triggers a runtime trap (`RE007`). Furthermore, native bitwise operators (`^`, `&`, `|`, `<<`, `>>`) and primitive cast expressions (`as u32`) are not part of the language syntax.

The project provides robust software primitives in `src/bits.mb`:

- **Wrapping Addition (`wrapping_add`)**:
  Calculates $(a + b) \pmod{2^{32}}$ in $O(1)$ without exceeding $2^{32}-1$. By calculating `diff = u32::MAX - a`, if $b > \text{diff}$, the wrapped sum is computed as `(b - diff) - 1`. All intermediate operations strictly remain within $[0, 2^{32}-1]$.
- **Wrapping Multiplication (`wrapping_mul`)**:
  Calculates $(a \times b) \pmod{2^{32}}$ via shift-and-add binary multiplication using `wrapping_add`.
- **Bitwise Logic (`bit_xor`, `bit_and`, `bit_or`)**:
  Performs bitwise logic bit-by-bit using integer division (`/ 2`), remainder (`% 2`), and binary power accumulation.
- **Bitwise Shifts (`shl`, `shr`)**:
  `shl` performs wrapping left shifts via repeated doubling with `wrapping_add`. `shr` performs unsigned right shifts via integer division by 2.
- **Byte to Word Widening (`u8_to_u32`)**:
  Converts `u8` values to `u32` without loops using 8 binary weight threshold comparisons.

## Byte Array Iteration

Memobits supports fixed-size byte buffers (`array<u8, N>`). This project demonstrates two iteration patterns:
- **Whole-Buffer Iteration**: `loop byte in bytes { ... }` iterates over all $N$ elements of a borrowed `array<u8, N>`.
- **Logical Slices**: Passing `bytes: borrow array<u8, N>, length: i32` allows processing arbitrary input lengths up to $N$ with an indexed `loop` breaking at `i == length`.

## Running and Building

From the repository root, run the project directly from source or compile it to WebAssembly:

```sh
# Run from source
cargo run -p memobits-cli -- run --project examples/apps/hashing/project.toml

# Build standalone Wasm artifact
cargo run -p memobits-cli -- build --project examples/apps/hashing/project.toml

# Run compiled Wasm artifact
cargo run -p memobits-cli -- run examples/apps/hashing/target/memobits/app.wasm
```

Both runs print the FNV-1a hash of `"Memobits"`. The `test fn` items verify all test vectors against known reference values (including empty inputs, single-character, and multi-byte inputs such as `"Memobits"`).

## Tests

`test fn` items check this project. `mb test` runs each one in a fresh instance; `mb build` and `mb run` leave them out of the artifact.

```sh
cargo run -p memobits-cli -- test --project examples/apps/hashing/project.toml
```

The report ends with this summary line (checked by `crates/memobits-cli/tests/examples_documented.rs`):

```text
test result: ok. 4 passed; 0 failed; 0 filtered out
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(u32(1774777415))
```
