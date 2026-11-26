# Binary tree with `Box`

Run from the repository root.

```sh
cargo run -p memobits-cli -- run --project examples/apps/tree/project.toml
cargo run -p memobits-cli -- build --project examples/apps/tree/project.toml
cargo run -p memobits-cli -- run examples/apps/tree/target/memobits/app.wasm
```

`main` builds a binary search tree of five values (8, 4, 12, 2, 6), keeps it
in a struct behind a `Box`, and returns `sum * 100 + depth * 10 + count`:
the values add up to 32, the tree is three levels deep and the holder counts
5, so the result is 3235.

[The tree module](src/tree.mb) shows the pieces of `Box<T>` (alloc layer,
`use alloc::Box;`):

- `type Tree [Leaf, Node(Box<Tree>, i32, Box<Tree>)]` is recursive. A type may
  contain itself only through a `Box` (directly, in a `T?` of a box, in a
  `List` of boxes), never by value.
- `Box(value)` moves a value to the heap; `unbox(b)` moves it back out and
  releases the box. `insert` takes a tree by value and `unbox`es the child it
  grows.
- Walks that only read (`sum`, `depth`) take `borrow Tree` and recurse with
  `child.borrow()`, which lends the tree inside the bound box.
- A pattern in an in-place `match` sees through a box: `leftmost_pair` matches
  `Node(Node(_, inner, _), item, _)` without binding the child boxes.

Every box and everything it owns is released exactly once, on every path.

## Tests

`test fn` items check this project. `mb test` runs each one in a fresh instance; `mb build` and `mb run` leave them out of the artifact.

```sh
cargo run -p memobits-cli -- test --project examples/apps/tree/project.toml
```

The report ends with this summary line (checked by `crates/memobits-cli/tests/examples_documented.rs`):

```text
test result: ok. 4 passed; 0 failed; 0 filtered out
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: i32(3235)
```
