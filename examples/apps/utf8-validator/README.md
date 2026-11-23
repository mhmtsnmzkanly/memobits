# Guest UTF-8 validator

[The example](src/main.mb) exercises `bytes.validate_utf8(length)`. This
built-in operation borrows the logical prefix of a fixed `array<u8, N>` and
returns `i32 ! Utf8Error` with the Unicode scalar count on success.
The length is an `i32`, and the receiver supplies the bound `N`.
Validation allocates no heap storage and leaves the buffer intact.
Lead-byte and continuation ranges cover one- through four-byte sequences and exclude
overlong encodings, surrogates, and values above U+10FFFF.
[RFC 3629, section 4](https://www.rfc-editor.org/rfc/rfc3629#section-4)

Validation stops at the first error. `Utf8Error` derives from `Error` and
adds `offset: i32?`. Offsets are zero-based byte positions.

| Code | Error | Offset |
| --- | --- | --- |
| 1 | Logical length outside 0–N | None |
| 2 | Invalid lead byte, including a stray continuation | Offending byte |
| 3 | Truncated sequence | First missing byte, equal to the logical length |
| 4 | Invalid continuation, including a byte outside the lead-specific range | Offending byte |

A present invalid continuation is reported before a later missing byte.
The validator ignores bytes beyond the logical length. `main` checks valid
and invalid fixtures, including é, scalar boundaries, and error offsets.
It returns a fixture-group code if a check fails.

From the repository root, run the source and build the standalone artifact
in a temporary directory.

```sh
cargo run -p memobits-cli -- run --project examples/apps/utf8-validator/project.toml
artifact_dir=$(mktemp -d)
cargo run -p memobits-cli -- build --project examples/apps/utf8-validator/project.toml --output "$artifact_dir/utf8.wasm"
cargo run -p memobits-cli -- run "$artifact_dir/utf8.wasm"
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(0))
```
