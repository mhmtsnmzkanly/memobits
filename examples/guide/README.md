# Runnable language guide

The guide walks through the executable language with small checked examples,
split into topic modules under [`src/`](src/): `numbers`, `text`, `tuples`,
`aggregates`, `ownership`, `collections`, `enums_outcomes`, `generics` and
`operators`. Each topic documents its feature in comments and checks it with
`test fn` items that use `assert`. [`src/main.mb`](src/main.mb) holds `main`, a
small program that combines a few guide features and returns `Ok(42)`. The
guide is the reference for current syntax, together with the accepted rules in
[decisions](../../docs/design/decisions.md).

From the repository root, run the source and build the standalone artifact in
a temporary directory:

```sh
cargo run -p memobits-cli -- run --project examples/guide/project.toml
artifact_dir=$(mktemp -d)
cargo run -p memobits-cli -- build --project examples/guide/project.toml --output "$artifact_dir/guide.wasm"
cargo run -p memobits-cli -- run "$artifact_dir/guide.wasm"
```

## Source-level tests

A top-level `test fn name() { ... }` is a test: no parameters, no result, never
`pub`, and checked like an ordinary function in its module (so it can call that
module's private items). Tests are excluded from the application artifact.
`assert(condition)` takes a `bool` and traps with `assertion failed` and its
source location when the condition is false; it works in ordinary code too, and
a function, import or value named `assert` takes precedence. Each guide fact is
a separate `assert`, so a failure points at the specific line, for example
`test text::text_concat ... FAILED` with the failing `assert` highlighted.

## Running the guide's tests

```sh
cargo run -p memobits-cli -- test --project examples/guide/project.toml
```

The report lists every test as `test <module>::<name> ... ok` and ends with the
summary line below (checked by `crates/memobits-cli/tests/examples_documented.rs`):

```text
test result: ok. 109 passed; 0 failed; 0 filtered out
```

`mb test` runs each test in a fresh instance and exits 1 if any fails. Add a
substring filter to select tests by qualified name (`... test --project
examples/guide/project.toml text::`). `mb build --tests --output
guide-tests.wasm` writes the test artifact and `mb test guide-tests.wasm` runs
it with the same report. `mb check` type-checks every module and every test;
`mb build` and `mb run` ignore tests.

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(42))
```
