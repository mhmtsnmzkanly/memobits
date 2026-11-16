# Fixed arrays project

A buildable project that uses fixed arrays of primitive elements as local
variables. `main::main` fills an 8-element `i32` array with squares in a loop,
updates one element, sums the array, and returns the sum.

It covers the supported array subset: literals `[1, 2, 3]`, repetition
`[0; 8]`, the `Array<i32, 8>` annotation, element assignment and compound
updates (`a[i] = v`, `a[i] += v`), element reads inside arithmetic, `loop` with
`if cond { break; }`, and whole-array moves (`let b := a;`). This example
keeps its arrays local; see `docs/design/implementation-plan.md` for the full
supported subset.

```sh
cargo run -p memobits-cli -- run --project examples/projects/arrays/project.toml
cargo run -p memobits-cli -- build --project examples/projects/arrays/project.toml
cargo run -p memobits-cli -- run examples/projects/arrays/target/memobits/app.wasm
```

Observed output of each command (the build path is shown relative to the repository root):

```text
Result: i32(352)
Built examples/projects/arrays/target/memobits/app.wasm: 1 export(s), 1253 bytes
Result: i32(352)
```

The sum is 140 (squares 0 to 49) plus 100 added to `squares[3]`, plus
`copy[3]` (109) and `seed[2]` (3).
