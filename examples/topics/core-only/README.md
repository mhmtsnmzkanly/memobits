# Core-only project

A small program that uses only the **core** layer: `[build] alloc = false` in
`project.toml` removes the guest allocator and the heap from the build. The
artifact has no allocator functions and its memory cannot grow past its
initial size.

| Module | Shows | Result | Tests |
|---|---|---|---|
| `src/checksum.mb` | a loop over a fixed `array<u8, 6>` with `u32` arithmetic | 57895 | 1 |
| `src/text.mb` | read-only `string` operations on literals (`len`, `byte_at`) counting digits | 6 | 1 |
| `src/main.mb` | an enum and `match`, and `main` adding the three results | 57911 | 1 |

With `alloc = false`, these are compile errors that name the setting: `use alloc::List;` (and any other
`alloc` import), `concat`, `push_str` and `to_utf8_string` (TE033 for the string operations, ME012 for the
import). String literals and read-only string operations keep working.

```sh
cargo run -p memobits-cli -- run --project examples/topics/core-only/project.toml
cargo run -p memobits-cli -- build --project examples/topics/core-only/project.toml
cargo run -p memobits-cli -- run examples/topics/core-only/target/memobits/app.wasm
```

## Tests

`test fn` items check this project; `mb test` runs each one in a fresh instance.

```sh
cargo run -p memobits-cli -- test --project examples/topics/core-only/project.toml
```

The report ends with this summary line (checked by `crates/memobits-cli/tests/examples_documented.rs`):

```text
test result: ok. 3 passed; 0 failed; 0 filtered out
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(57911))
```
