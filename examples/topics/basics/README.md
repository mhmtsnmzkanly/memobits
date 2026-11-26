# Basics project

One small project that covers the first things to learn: arithmetic through
internal calls, loops and `string` operations. Its application root is
`main::main`, which sums one result function per module.

| Module | Shows | Result | Tests |
|---|---|---|---|
| `src/arithmetic.mb` | `add`, `subtract`, `multiply`, `divide` chained into `order_total()` | 265 | 2 |
| `src/loops.mb` | `loop`/`break` with `factorial(5) == 120` and `sum_to(10) == 55` in `combined()` | 175 | 2 |
| `src/text.mb` | owned and borrowed `string` operations: concat, borrow, share, push_str and a struct-owned label in `combined_length()` | 22 | 4 |

`main` returns `Ok(265 + 175 + 22)`, that is `Ok(462)`. The facts that used to
be `Err` codes are `assert` calls in each module's `test fn` items.

```sh
cargo run -p memobits-cli -- project --project examples/topics/basics/project.toml
cargo run -p memobits-cli -- run --project examples/topics/basics/project.toml
cargo run -p memobits-cli -- build --project examples/topics/basics/project.toml
cargo run -p memobits-cli -- run examples/topics/basics/target/memobits/app.wasm
```

## Tests

`test fn` items check this project. `mb test` runs each one in a fresh instance; `mb build` and `mb run` leave them out of the artifact.

```sh
cargo run -p memobits-cli -- test --project examples/topics/basics/project.toml
```

The report ends with this summary line (checked by `crates/memobits-cli/tests/examples_documented.rs`):

```text
test result: ok. 8 passed; 0 failed; 0 filtered out
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(462))
```
