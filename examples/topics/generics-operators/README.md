# Generics and operators project

A small program built only from shipped features. It defines
`type Vec2 { x: i32, y: i32 }` and implements the compiler-provided
`core::ops` interfaces `Add`, `Sub` and `PartialEq` for it, so `+`, `-`, `==`
and `!=` work on `Vec2` values. It also declares a user interface `Weigh` and
two generic functions, each with one owned `T` parameter and one interface
bound:

- `weigh_twice<T>(value: T) -> i32 where T: Weigh`
- `combine<T>(left: T, right: T::Rhs) -> T::Output where T: Add`

`main` checks each step with a distinct `Err` code (1 to 5) and returns the final
weight, `Ok(41)`. For the full operator set and generic limits see the
[language guide](../../guide/README.md).

```sh
cargo run -p memobits-cli -- run --project examples/topics/generics-operators/project.toml
cargo run -p memobits-cli -- build --project examples/topics/generics-operators/project.toml
cargo run -p memobits-cli -- run examples/topics/generics-operators/target/memobits/app.wasm
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(41))
```
