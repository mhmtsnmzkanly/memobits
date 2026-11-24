# ENF lexer fixture

A bounded byte lexer written in Memobits, checked by `test fn` items. It scans decimal
integer tokens in fixed `array<u8, 16>` buffers, reports byte spans, and
returns owned outcomes with a nominal `LexError` that derives from `Error`.
`main` lexes one input to its end and returns `Ok(0)`, or the lexer's error
code. The tests check the scan table. Scope, limits and
the UTF-8 boundary are described in the
[ENF lexer slice design](../../../docs/design/enf-lexer-slice.md).

From the repository root, run the source and build the standalone artifact in
a temporary directory:

```sh
cargo run -p memobits-cli -- run --project examples/apps/enf-lexer/project.toml
artifact_dir=$(mktemp -d)
cargo run -p memobits-cli -- build --project examples/apps/enf-lexer/project.toml --output "$artifact_dir/enf.wasm"
cargo run -p memobits-cli -- run "$artifact_dir/enf.wasm"
```

## Tests

`test fn` items check this project. `mb test` runs each one in a fresh instance; `mb build` and `mb run` leave them out of the artifact.

```sh
cargo run -p memobits-cli -- test --project examples/apps/enf-lexer/project.toml
```

The report ends with this summary line (checked by `crates/memobits-cli/tests/examples_documented.rs`):

```text
test result: ok. 8 passed; 0 failed; 0 filtered out
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(0))
```
