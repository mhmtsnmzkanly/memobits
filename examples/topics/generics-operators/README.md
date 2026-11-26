# Generics and operators project

A small program built only from shipped features. It defines
`type Vec2 { x: i32, y: i32 }` and implements the compiler-provided
`core::ops` interfaces `Add`, `Sub` and `PartialEq` for it, so `+`, `-`, `==`
and `!=` work on `Vec2` values. It also declares a user interface `Weigh` and
generic functions: two with one owned `T` parameter and one interface bound,
and two that use several type parameters and a higher-order helper:

- `weigh_twice<T>(value: T) -> i32 where T: Weigh`
- `combine<T>(left: T, right: T::Rhs) -> T::Output where T: Add`
- `weigh_scaled<T, U>(value: T, factor: U) -> i32 where T: Weigh + Scale, U: Scale`
  (two type parameters, two bounds on `T`, one evidence per bound)
- `apply_twice<T>(value: T, step: borrow fn(T) -> T) -> T` (a generic
  higher-order helper called with an anonymous function)

`main` combines the pieces and returns the final weight, `Ok(41)`; `test fn`
items check each step. For the full operator set and generic limits see the
[language guide](../../guide/README.md).

```sh
cargo run -p memobits-cli -- run --project examples/topics/generics-operators/project.toml
cargo run -p memobits-cli -- build --project examples/topics/generics-operators/project.toml
cargo run -p memobits-cli -- run examples/topics/generics-operators/target/memobits/app.wasm
```

## Tests

`test fn` items check this project. `mb test` runs each one in a fresh instance; `mb build` and `mb run` leave them out of the artifact.

```sh
cargo run -p memobits-cli -- test --project examples/topics/generics-operators/project.toml
```

The report ends with this summary line (checked by `crates/memobits-cli/tests/examples_documented.rs`):

```text
test result: ok. 6 passed; 0 failed; 0 filtered out
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(41))
```
