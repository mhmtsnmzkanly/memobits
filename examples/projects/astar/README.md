# Fixed-grid A* search

Run from the repository root.

```sh
cargo run -p memobits-cli -- run --project examples/projects/astar/project.toml
cargo run -p memobits-cli -- build --project examples/projects/astar/project.toml
cargo run -p memobits-cli -- run examples/projects/astar/target/memobits/app.wasm
```

Both runs print `Result: Ok(i32(12))` after checking two layouts. The only gap
in the wall is on the bottom row, so the shortest route takes four steps down,
four across, and four up. Closing that gap leaves the goal cell open while
making it unreachable. Error code 1 means the first search found no route,
code 2 means its cost was wrong, and code 3 means the second search found a
route through the closed wall.

[The search](src/grid.mb) uses four orthogonal neighbors on a 5 × 5 grid.
Each move costs one. It scans the fixed-size frontier for the lowest sum of
distance traveled and Manhattan distance to the goal. It returns an
`Option<i32>` containing the optimal cost or `None` when the frontier is
exhausted or an endpoint is invalid. The example returns the cost only.
