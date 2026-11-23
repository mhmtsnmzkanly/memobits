# Basics project

One small project that covers the first things to learn: arithmetic through
internal calls, loops and `string` operations. Its application root is
`main::main`, which calls one exported `check` function per module and sums
their `Ok` values.

| Module | Shows | `Err` codes | `Ok` value |
|---|---|---|---|
| `src/arithmetic.mb` | `add`, `subtract`, `multiply`, `divide` chained over checked operations | 1 | 265 |
| `src/loops.mb` | `loop`/`break` with `factorial(5) == 120` and `sum_to(10) == 55` | 2, 3 | 175 |
| `src/text.mb` | owned and borrowed `string` operations: concat, borrow, share, push_str and a struct-owned label | 4 to 6 | 22 |

`main` returns `Ok(265 + 175 + 22)`, that is `Ok(462)`, or the first failing
module's `Err` code.

```sh
cargo run -p memobits-cli -- project --project examples/topics/basics/project.toml
cargo run -p memobits-cli -- run --project examples/topics/basics/project.toml
cargo run -p memobits-cli -- build --project examples/topics/basics/project.toml
cargo run -p memobits-cli -- run examples/topics/basics/target/memobits/app.wasm
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(462))
```
