# CLI host capability

This project declares `memobits:console.write_i32(i32) -> unit` in its CLI
host profile and binds it from Memobits source with `extern fn write_i32(value:
i32);`. The declaration is checked against the manifest before lowering.

From the workspace root, run the source, build it, then run the artifact with
the same profile:

```sh
target/debug/mb run --project examples/topics/host-capability/project.toml
target/debug/mb build --project examples/topics/host-capability/project.toml --output target/host-capability.wasm
target/debug/mb run target/host-capability.wasm --project examples/topics/host-capability/project.toml
```

Each invocation calls the typed host import, prints `Host i32: 42`, and reports
`Result: i32(7)`. This project is exempt from the `i32 ! Error` convention
used by the other examples: `main` returns a bare `i32` because the H1 host
capability acceptance evidence pins that exact `Result: i32(7)` output. The current source declaration supports this one owned `i32`
argument and unit result. The CLI profile rejects undeclared, unknown, or
signature-mismatched imports before guest code starts. Both the source run and the artifact run (with `--project` for the profile) print the output below. Other hosts, reference
parameters, and source-level multi-module host declarations are not supported.

## Tests

This project has no `test fn` items: its only function is the host-import call, which needs the CLI host profile that `mb run` selects from the manifest. `mb test` still compiles the project and reports zero tests.

```sh
cargo run -p memobits-cli -- test --project examples/topics/host-capability/project.toml
```

The report ends with this summary line (checked by `crates/memobits-cli/tests/examples_documented.rs`):

```text
test result: ok. 0 passed; 0 failed; 0 filtered out
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Host i32: 42
Result: i32(7)
```
