# Primitive analysis example

Run from the repository root:

```sh
cargo run -p memobits-cli -- analyze examples/analysis/numeric.mb
```

The example exercises typed parameters, branches, integer limits, mutation,
shadowing, and function calls. Analysis currently checks primitive types and
loop-control placement; it does not check ownership or produce Wasm.

For project-wide imports and library roots, use `examples/projects/numeric`:

```sh
cargo run -p memobits-cli -- analyze-project --project examples/projects/numeric/project.toml
cargo run -p memobits-cli -- analyze-project --project examples/projects/numeric/project.toml --lib
```

The owned primitive move example exercises transfer, reinitialization during
argument evaluation, repeated arithmetic reads, and shadowing:

```sh
cargo run -p memobits-cli -- ownership examples/analysis/ownership.mb
```

`ownership` lowers one module to IR and checks move availability. Borrow/share
lifetimes, aggregate ownership, and Wasm execution are not implemented yet.

`references.mb` exercises primitive share updates, borrow reads, and last-use
release. Check it with `mb ownership examples/analysis/references.mb`; reference
programs are not yet executable by the Wasm backend.
