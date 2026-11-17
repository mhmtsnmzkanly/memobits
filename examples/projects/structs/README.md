# Structs project

A buildable project for the struct slices A1, A2 and A3. `main::main` declares a
`Size` struct with `i32`, `Bool` and `u8` fields, and uses `Point` from
`src/geom.mb`, whose fields are all `pub`, through `use geom::Point;`.

It demonstrates:

- a constructor function, `make_size(width, height) -> Size`: a struct result is
  an owned value written into storage the caller provides;
- a function that mutates its argument, `grow(s: share Size, by: i32)`: the call
  site writes `grow(s.share(), 2)` and `s` must be a `var`; the caller observes
  the field writes (`s.width += by;`);
- a function that only reads, `area(s: borrow Size) -> i32`: the call site writes
  `area(s.borrow())`, the struct stays usable afterwards, and fields are read
  through the reference;
- `var` struct bindings and a direct field write (`s.scale = 2;`);
- literals whose fields are written in a different order from the declaration,
  field reads inside arithmetic and `if` conditions, and a public struct from
  another module;
- nesting (A3): `Segment { from: Point, to: Point }` holds structs by value,
  `seg.to.x += 1;` writes a field of a field, `seg.from = Point { .. };`
  replaces a whole sub-struct, `manhattan(seg.to.borrow())` lends a
  sub-struct, and `Array<Size, 2>` is an array of structs built from a call and
  a literal, written with `sizes[1].width = 3;` and read through the
  `borrow` parameter of `total_area(sizes.borrow())`.

Still gated: moving a sub-aggregate out (`let q := seg.to;`, TE022, partial
moves are deferred), destructuring, references to primitive fields
(`s.width.share()`), whole-struct
`.copy()`, field access on a call result (`make_size(1, 2).width`) and structs in
`main` or `[export]` signatures. See `docs/design/struct-implementation.md` for
the A1, A2 and A3 checkpoints.

```sh
cargo run -p memobits-cli -- run --project examples/projects/structs/project.toml
cargo run -p memobits-cli -- build --project examples/projects/structs/project.toml
cargo run -p memobits-cli -- run examples/projects/structs/target/memobits/app.wasm
```

Observed output of each command, from the repository root (the absolute prefix
of the built path is shortened to the repository root):

```text
Result: i32(59)
Built examples/projects/structs/target/memobits/app.wasm: 1 export(s), 2102 bytes
Result: i32(59)
```

The result is 31 + 10 + 9 + 9. `make_size(3, 4)` builds a 3 by 4 `Size`, `grow`
adds 2 to both sides through the `share` parameter, so `area` sees a 5 by 6
square: `5 * 6` plus a bonus of 1 because `scale == 2`, gives 31. `p.x * p.y` is
`2 * 5 = 10`. The segment ends at `(3, 5)` after the write and starts at
`(1, 1)`, so `manhattan(seg.to.borrow()) + seg.from.x` is `8 + 1 = 9`. The two
sizes are 1 by 1 and 3 by 2, whose areas (with the scale bonus) are `2 + 7 = 9`.
