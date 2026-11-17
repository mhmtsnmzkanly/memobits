# Numeric project fixture

A minimal source project for the new compiler pipeline. Its application root is
`main::main`; its library root exports only `math::add` as `add`.

Project inventory can be inspected with:

```sh
cargo run -p memobits-cli -- project --project examples/projects/numeric/project.toml
```

The application checks the result of `math::add(20, 22)` and returns
`Result: i32(0)` in both source and artifact runs.

```sh
cargo run -p memobits-cli -- run --project examples/projects/numeric/project.toml
cargo run -p memobits-cli -- build --project examples/projects/numeric/project.toml
cargo run -p memobits-cli -- run examples/projects/numeric/target/memobits/app.wasm
```
