# CLI host capability

This project declares `memobits:console.write_i32(i32) -> unit` in its CLI
host profile and binds it from Memobits source with `extern fn write_i32(value:
i32);`. The declaration is checked against the manifest before lowering.

From the workspace root, run the source, build it, then run the artifact with
the same profile:

```sh
target/debug/mb run --project examples/projects/host-capability/project.toml
target/debug/mb build --project examples/projects/host-capability/project.toml --output target/host-capability.wasm
target/debug/mb run target/host-capability.wasm --project examples/projects/host-capability/project.toml
```

Each invocation calls the typed host import, prints `Host i32: 42`, and reports
`Result: i32(7)`. The current source declaration supports this one owned `i32`
argument and unit result. The CLI profile rejects undeclared, unknown, or
signature-mismatched imports before guest code starts. Other hosts, reference
parameters, and source-level multi-module host declarations are not supported.
