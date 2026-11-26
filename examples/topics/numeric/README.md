# Numeric project fixture

A minimal source project for the new compiler pipeline. Its application root is
`main::main`; its library root exports only `math::add` as `add`.

Project inventory can be inspected with:

```sh
cargo run -p memobits-cli -- project --project examples/topics/numeric/project.toml
```

The application returns `math::add(20, 22)` as `Ok(42)`; `test fn` items in
`main.mb` and `math.mb` check `add`.

```sh
cargo run -p memobits-cli -- run --project examples/topics/numeric/project.toml
cargo run -p memobits-cli -- build --project examples/topics/numeric/project.toml
cargo run -p memobits-cli -- run examples/topics/numeric/target/memobits/app.wasm
```

## Tests

`test fn` items check this project. `mb test` runs each one in a fresh instance; `mb build` and `mb run` leave them out of the artifact.

```sh
cargo run -p memobits-cli -- test --project examples/topics/numeric/project.toml
```

The report ends with this summary line (checked by `crates/memobits-cli/tests/examples_documented.rs`):

```text
test result: ok. 2 passed; 0 failed; 0 filtered out
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(42))
```
