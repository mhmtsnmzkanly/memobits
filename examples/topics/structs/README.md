# Structs project

A buildable project for the struct slices A1 to A4. `main::main` declares a
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

- disjoint loans (A4): `let first := seg.from.borrow(); seg.to.y += 1;` writes
  one field while a borrow of another is live, which the loan checker accepts
  because the two locations cannot overlap;
- destructuring (A4): `let Segment { from: start, to: end } := seg;` consumes
  `seg` and binds every field (here two structs) to a new local.

Still gated: moving a sub-aggregate out (`let q := seg.to;`, TE022, implicit
partial moves are deferred), nested or partial destructuring patterns,
references to primitive fields (`s.width.share()`), whole-struct `.copy()`,
field access on a call result (`make_size(1, 2).width`) and structs in `main`
or `[export]` signatures. See `docs/design/struct-implementation.md` for the
A1 to A4 checkpoints.

```sh
cargo run -p memobits-cli -- run --project examples/topics/structs/project.toml
cargo run -p memobits-cli -- build --project examples/topics/structs/project.toml
cargo run -p memobits-cli -- run examples/topics/structs/target/memobits/app.wasm
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(63))
```

The `Ok` value is 31 + 10 + 9 + 9 + 2 + 2. `make_size(3, 4)` builds a 3 by 4 `Size`, `grow`
adds 2 to both sides through the `share` parameter, so `area` sees a 5 by 6
square: `5 * 6` plus a bonus of 1 because `scale == 2`, gives 31. `p.x * p.y` is
`2 * 5 = 10`. The segment ends at `(3, 5)` after the write and starts at
`(1, 1)`, so `manhattan(seg.to.borrow()) + seg.from.x` is `8 + 1 = 9`. The two
sizes are 1 by 1 and 3 by 2, whose areas (with the scale bonus) are `2 + 7 = 9`.
After the write, `first` still reads the unchanged `from` point `(1, 1)`, so
`flat` is `1 + 1 = 2`. Destructuring `seg` leaves `start = (1, 1)` and
`end = (3, 6)`, so `spread` is `3 - 1 = 2`.
