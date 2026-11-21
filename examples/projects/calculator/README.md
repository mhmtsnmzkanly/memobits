# Calculator project fixture

A minimal source project for arithmetic through internal calls. Its application
root is `main::main`; the calculator chains `add`, `subtract`, `multiply` and
`divide` over checked operations.

Project inventory can be inspected with:

```sh
cargo run -p memobits-cli -- project --project examples/projects/calculator/project.toml
```

The calculator chains `add`, `subtract`, `multiply` and `divide` over checked
operations and checks the final total.

```sh
cargo run -p memobits-cli -- run --project examples/projects/calculator/project.toml
cargo run -p memobits-cli -- build --project examples/projects/calculator/project.toml
cargo run -p memobits-cli -- run examples/projects/calculator/target/memobits/app.wasm
```

Both run commands print the same result.

```text
Result: i32(0)
```
