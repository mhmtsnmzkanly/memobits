# Computation project fixture

A minimal source project for iterative computation. Its application root is
`main::main`; `factorial` counts down from its argument with a loop.

Project inventory can be inspected with:

```sh
cargo run -p memobits-cli -- project --project examples/projects/computation/project.toml
```

The computation checks `factorial(5) == 120` and the iterative sum
`sum_to(10) == 55`.

```sh
cargo run -p memobits-cli -- run --project examples/projects/computation/project.toml
cargo run -p memobits-cli -- build --project examples/projects/computation/project.toml
cargo run -p memobits-cli -- run examples/projects/computation/target/memobits/app.wasm
```

Both run commands print the same result.

```text
Result: i32(0)
```
