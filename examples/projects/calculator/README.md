# Calculator project fixture

A minimal source project for arithmetic through internal calls. Its application
root is `main::main`; the calculator chains `add`, `subtract`, `multiply` and
`divide` over checked operations.

Project inventory can be inspected with:

```sh
cargo run -p memobits-cli -- project --project examples/projects/calculator/project.toml
```

The calculator chains `add`, `subtract`, `multiply` and `divide` over checked
operations and checks the final total, returning it as `Ok(265)` (`Err` code 1 on
a mismatch).

```sh
cargo run -p memobits-cli -- run --project examples/projects/calculator/project.toml
cargo run -p memobits-cli -- build --project examples/projects/calculator/project.toml
cargo run -p memobits-cli -- run examples/projects/calculator/target/memobits/app.wasm
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(265))
```
