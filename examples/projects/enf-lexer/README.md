# ENF lexer fixture

A bounded, self-checking byte lexer written in Memobits. It scans decimal
integer tokens in fixed `Array<u8, 16>` buffers, reports byte spans, and
returns owned outcomes with a nominal `LexError` that derives from `Error`.
Each failed check returns a distinct error code from `main`. Scope, limits and
the UTF-8 boundary are described in the
[ENF lexer slice design](../../../docs/design/enf-lexer-slice.md).

From the repository root, run the source and build the standalone artifact in
a temporary directory:

```sh
cargo run -p memobits-cli -- run --project examples/projects/enf-lexer/project.toml
artifact_dir=$(mktemp -d)
cargo run -p memobits-cli -- build --project examples/projects/enf-lexer/project.toml --output "$artifact_dir/enf.wasm"
cargo run -p memobits-cli -- run "$artifact_dir/enf.wasm"
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(0))
```
