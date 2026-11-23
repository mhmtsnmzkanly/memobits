# Fixed arrays project

A buildable project that uses fixed arrays of primitive elements as local
variables, through functions, and as a small nested array. `main::main` fills
an 8-element `i32` array with squares in a loop, updates one element, sums the
array, moves it, then combines that with array calls and a 2 x 3 nested array.

It covers the supported array subset: literals `[1, 2, 3]`, repetition
`[0; 8]`, the `Array<i32, 8>` annotation, element assignment and compound
updates (`a[i] = v`, `a[i] += v`), element reads inside arithmetic, `loop` with
`if cond { break; }`, and whole-array moves (`let b := a;`). Through functions:
a `borrow Array<i32, 3>` parameter (`sum`), a `share Array<i32, 3>` parameter
that the caller observes (`scale`), and an array result (`make`). Nested:
`[[0; 3]; 2]`, `grid[r][c]` reads and writes, whole-row replacement
`grid[1] = [4, 5, 6];` and lending a row with `grid[1].borrow()`. A primitive
element is copied implicitly into a binding (`let peak := squares[7];`, with
`squares` staying whole); extracting a row (`let r := grid[0];`) is TE022, and
arrays or rows cannot be copied yet. See
`docs/design/implementation-plan.md` for the full supported subset.

```sh
cargo run -p memobits-cli -- run --project examples/projects/arrays/project.toml
cargo run -p memobits-cli -- build --project examples/projects/arrays/project.toml
cargo run -p memobits-cli -- run examples/projects/arrays/target/memobits/app.wasm
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(493))
```

The `Ok` value is the sum of three parts: 401 from the first section (140 for the
squares 0 to 49, plus 100 added to `squares[3]`, plus `moved[3]` (109),
`seed[2]` (3) and `peak`, a copy of `squares[7]` (49)); 72 from `sum` over `make(10)` doubled by `scale` (11, 12, 13
become 22, 24, 26); and 20 from the nested array (`grid[0][1]` is 5 and the
replaced row `[4, 5, 6]` sums to 15).
