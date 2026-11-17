# First bounded ENF lexer slice

The [accepted decisions](decisions.md) call for a small ENF lexer/parser
consumer and leave protocol-specific numeric limits to libraries. The
[illustrative guide](../../examples/design/language-guide.mb) names an
`enf::Parser` import but gives no wire grammar. No ENF specification or
wire fixtures were found in the repository. The rules below define a
proposed test fixture for the language milestone. ENF token syntax, numeric
limits and conformance remain open until there is a protocol reference.

## Fixture contract

Scan a borrowed `Array<u8, 16>` with an explicit logical length and a byte
cursor starting at zero. Validate that the length is in 0–16 before indexing.
Skip ASCII space, tab, LF and CR. Recognize maximal runs of ASCII digits
`0`–`9` as unsigned decimal integers in 0–4294967295, with leading zeroes
allowed. This range exercises checked `u32` arithmetic in Memobits.

One scan returns `Result<Option<IntegerToken>, LexError>`. `Some` carries
the numeric value and its zero-based, half-open byte span. `None` means end of
input after skipping whitespace. Advance the cursor on success and stop on
the first error. A byte outside a digit run is handled by the next scan.
Before multiplying by ten and adding the next digit, check whether the
accumulator exceeds 429496729, or equals it and the digit exceeds 5.
Report the overflowing digit as a lexer error.
The error code and optional byte offset are part of this fixture.

| Logical input bytes | Expected scans |
| --- | --- |
| Empty, or `09 0D 0A 20` in hex | End of input |
| ASCII ` 007\t42` (with a literal tab) | 7 at [1, 4), 42 at [5, 7), end of input |
| ASCII `4294967295` | 4294967295 at [0, 10), end of input |
| ASCII `4294967296` | Code 3, overflow at byte 9 |
| ASCII `12,` | 12 at [0, 2), then code 2 at byte 2 |
| Hex `C3 A9` or `C3` | Code 2 at byte 0 in either case |
| Length -1 or 17 | Code 1, no byte offset |

Code 2 means unsupported byte. Bytes beyond the logical length are ignored,
including zero padding. Signs, decimals, punctuation and identifiers are
outside this fixture.

## UTF-8 boundary

The Memobits compiler lexer receives Rust `&str`. Guest-side UTF-8 strings
and scalar iteration are still pending. This fixture uses byte arrays and
rejects every non-ASCII byte at its first occurrence. The valid UTF-8 encoding
of U+00E9 and its truncated prefix therefore produce the same fixture error.
Keep offsets in bytes. Once the protocol reference establishes where text
is permitted, define the UTF-8 validation and scalar-handling contract for
those tokens.

## Implementation and verification

The [self-checking project](../../examples/projects/enf-lexer/src/main.mb)
uses guest-side fixed arrays, a mutable cursor passed by `share`, owned
outcomes, and a nominal `LexError` derived from `Error`. Array indexing uses
an owned snapshot from `cursor.copy()` because a shared cursor used directly
as an index produces TE007. Digit conversion counts from ASCII zero with a
`u32` result using the supported typed arithmetic.

The checks cover values, spans, error codes and offsets, and verify that
trailing padding is ignored. Each failed check returns a distinct entry code
from `main`. Both runs print `Result: Ok(i32(0))` on success. From the
repository root, run:

```sh
cargo run -p memobits-cli -- run --project examples/projects/enf-lexer/project.toml
artifact_dir=$(mktemp -d)
cargo run -p memobits-cli -- build --project examples/projects/enf-lexer/project.toml --output "$artifact_dir/enf.wasm"
cargo run -p memobits-cli -- run "$artifact_dir/enf.wasm"
```

The CLI integration test uses this manifest and runs the built artifact from
an isolated temporary directory.
