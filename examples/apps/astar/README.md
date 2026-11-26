# Fixed-grid A* search

Run from the repository root.

```sh
cargo run -p memobits-cli -- run --project examples/apps/astar/project.toml
cargo run -p memobits-cli -- build --project examples/apps/astar/project.toml
cargo run -p memobits-cli -- run examples/apps/astar/target/memobits/app.wasm
```

`main` searches a wall with one gap. The only gap
in the wall is on the bottom row, so the shortest route takes four steps down,
four across, and four up. `main` returns that cost, or error code 1 if the
search finds no route. The `test fn` items check the cost of 12 and that
closing the gap leaves the goal cell open but unreachable.

[The search](src/grid.mb) uses four orthogonal neighbors on a 5 × 5 grid.
Each move costs one. It scans the fixed-size frontier for the lowest sum of
distance traveled and Manhattan distance to the goal. It returns an
`i32?` containing the optimal cost or `None` when the frontier is
exhausted or an endpoint is invalid. The example returns the cost only.

## Tests

`test fn` items check this project. `mb test` runs each one in a fresh instance; `mb build` and `mb run` leave them out of the artifact.

```sh
cargo run -p memobits-cli -- test --project examples/apps/astar/project.toml
```

The report ends with this summary line (checked by `crates/memobits-cli/tests/examples_documented.rs`):

```text
test result: ok. 2 passed; 0 failed; 0 filtered out
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(12))
```
