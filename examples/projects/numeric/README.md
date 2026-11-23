# Numeric project fixture

A minimal source project for the new compiler pipeline. Its application root is
`main::main`; its library root exports only `math::add` as `add`.

Project inventory can be inspected with:

```sh
cargo run -p memobits-cli -- project --project examples/projects/numeric/project.toml
```

The application checks the result of `math::add(20, 22)` and returns it as
`Ok(42)`; a failed check returns `Err(Error { code: 1 })`.

```sh
cargo run -p memobits-cli -- run --project examples/projects/numeric/project.toml
cargo run -p memobits-cli -- build --project examples/projects/numeric/project.toml
cargo run -p memobits-cli -- run examples/projects/numeric/target/memobits/app.wasm
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(42))
```
