# Guest UTF-8 validator

[The validator](src/main.mb) checks the logical prefix of a `Bytes<8>` buffer
and returns the number of Unicode scalars on success. Its lead-byte and
continuation ranges cover one- through four-byte sequences and exclude
overlong encodings, surrogates, and values above U+10FFFF.
[RFC 3629, section 4](https://www.rfc-editor.org/rfc/rfc3629#section-4)

Validation stops at the first error. Offsets are zero-based byte positions.

| Code | Error | Offset |
| --- | --- | --- |
| 1 | Logical length outside 0–8 | None |
| 2 | Invalid lead byte, including a stray continuation | Offending byte |
| 3 | Truncated sequence | First missing byte, equal to the logical length |
| 4 | Invalid continuation, including a byte outside the lead-specific range | Offending byte |

A present invalid continuation is reported before a later missing byte.
The validator ignores bytes beyond the logical length. `main` checks valid
and invalid fixtures, including é, scalar boundaries, and error offsets.
It returns a fixture-group code if a check fails.

From the repository root, run the source and build the standalone artifact
in a temporary directory. Both runs print `Result: Ok(i32(0))`.

```sh
cargo run -p memobits-cli -- run --project examples/projects/utf8-validator/project.toml
artifact_dir=$(mktemp -d)
cargo run -p memobits-cli -- build --project examples/projects/utf8-validator/project.toml --output "$artifact_dir/utf8.wasm"
cargo run -p memobits-cli -- run "$artifact_dir/utf8.wasm"
```
