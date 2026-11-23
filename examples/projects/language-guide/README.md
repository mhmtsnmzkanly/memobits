# Runnable language guide

[`src/main.mb`](src/main.mb) walks through the executable language with small
checked examples. `main` runs every check, returns `Ok(42)` when all pass, and returns a
distinct `Err` code for each failed check. It is the reference for
current syntax, together with the accepted rules in
[decisions](../../../docs/design/decisions.md).

From the repository root, run the source and build the standalone artifact in
a temporary directory:

```sh
cargo run -p memobits-cli -- run --project examples/projects/language-guide/project.toml
artifact_dir=$(mktemp -d)
cargo run -p memobits-cli -- build --project examples/projects/language-guide/project.toml --output "$artifact_dir/guide.wasm"
cargo run -p memobits-cli -- run "$artifact_dir/guide.wasm"
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(42))
```
