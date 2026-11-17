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

The ownership example moves an array into a call, reinitializes it during
argument evaluation, and shows that primitive reads are copied implicitly (they
never move):

```sh
cargo run -p memobits-cli -- ownership examples/analysis/ownership.mb
```

`ownership` lowers one module to IR. Its output reports that owned moves and
primitive loans were checked and that internal primitive references are
supported. External reference signatures are not supported, and a passing check
is not a complete borrow-safety guarantee. Copied to `src/main.mb` of a project
whose manifest has `entry = "main::main"`, `mb run --project PATH` prints
`Result: i32(82)`.

`references.mb` exercises primitive share updates, borrow reads, and last-use
release. Check it with `mb ownership examples/analysis/references.mb`. Internal
primitive references also compile and run: copied to `src/main.mb` of a project
whose manifest has `entry = "main::main"`, `mb run --project PATH` prints
`Result: i32(64)`.
