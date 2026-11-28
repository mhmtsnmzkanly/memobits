# Scalar component

This example has a scalar application entry. Build a component and execute it
with Wasmtime from the repository root:

```sh
artifact_dir=$(mktemp -d)
target/debug/mb build --component --project examples/topics/component/project.toml --output "$artifact_dir/component.wasm"
target/debug/mb exec "$artifact_dir/component.wasm"
```

The same project exports a zero-argument scalar library function. Build the
library component and select the normalized WIT export:

```sh
target/debug/mb build --lib --component --project examples/topics/component/project.toml --output "$artifact_dir/library.wasm"
target/debug/mb exec "$artifact_dir/library.wasm" --entry library-answer
```

This component slice accepts application entries and explicitly
exported library functions with scalar parameters and scalar or Unit results.
The CLI runner only calls zero-argument exports; other hosts can call functions
with parameters. Application entries may return `T?` with bool, char, integer
or float `T`, producing `Some(value)` or `None`, and may return `T ! Error` or `T ?! Error`
(equivalent to `T? ! Error`) when `T` is bool, char, integer or float, and the error
is exactly the root `Error` type. The optional form supports `Ok(Some(value))`,
`Ok(None)` and `Err(error)`; executable facts are in
[`enums_outcomes.mb`](../../guide/src/enums_outcomes.mb). Nested options, aggregate option payloads, derived errors, Unit
outcome payloads, library functions with option or outcome signatures, and
other aggregate signatures remain gated. The CLI console capability
can also be imported through WIT; see [the host example](../host-capability/README.md). `mb run` and `mb test` continue to use core Wasm.
Recognized compiler-generated traps retain source diagnostics; unrecognized
component traps use the generic Wasmtime diagnostic.

## Tests

```sh
cargo run -p memobits-cli -- test --project examples/topics/component/project.toml
```

```text
test result: ok. 1 passed; 0 failed; 0 filtered out
```

## Expected output

Source, core Wasm and component execution print:

```text
Result: i32(42)
```
