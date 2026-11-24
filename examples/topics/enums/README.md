# Enums project

A buildable project for the enum packages B1 to B3. `src/main.mb` declares a
`Shape` enum and a `Job` state-machine enum and inspects them with `match`.

It demonstrates:

- unit and payload variants (`Shape::Empty`, `Shape::Circle(r)`,
  `Job::Running(n)`) and an alias of an enum type (`type Figure = Shape;`,
  then `Figure::Rect(2.0, 4.0)`);
- `match` as an expression: every arm yields the same type (`f64` in `area`,
  `i32` in `corners`), an arm is `Pattern => expr,` or `Pattern => { block }`
  (the comma after a block is optional), `_` ignores one payload slot and a
  bare `_` arm matches every remaining variant (`total`);
- exhaustiveness: every variant must be matched or a `_` arm must exist;
- ownership: matching an owned enum consumes it and each bound payload is an
  owned local, so `advance(j: Job) -> Job` builds the next state in each arm and
  the loop writes `job = advance(job);`;
- borrowing matches (B3): a scrutinee that cannot be moved is matched in place.
  `is_wide(s: borrow Shape)` matches its reference parameter, and
  `count_corners` matches `tiles[i]` in a loop, an element of a `borrow` array.
  Nothing is consumed, so the array stays whole and the same element can be
  matched again; primitive payloads are copied, aggregate payloads would be
  read-only borrows (writing through a match is not allowed).

Patterns nest to any depth (`Ok(Some(v))`, `Shape::Pair(Point::Origin, other)`, tuples
in payloads); see the guide's `nested_patterns` check.

Still gated: literal patterns, guards, `==` on enums (use `match`), and
user-defined enums in Wasm entry or library export signatures. The separate
[application outcome adapter](../../../docs/design/outcome-implementation.md)
supports compiler-known `T ! E` and `T ?! E` entries with primitive success
payloads. See the [enum checkpoints](../../../docs/design/enum-implementation.md).

```sh
cargo run -p memobits-cli -- run --project examples/topics/enums/project.toml
cargo run -p memobits-cli -- build --project examples/topics/enums/project.toml
cargo run -p memobits-cli -- run examples/topics/enums/target/memobits/app.wasm
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(1094300))
```

The `Ok` value is 300 + 4000 + 0 + 1090000. The rectangle `2 x 4` has area 8 and the circle
of radius 2 has area `3 * 2 * 2 = 12`, so the two areas sum to 20 and `shapes`
is `corners(Shape::Rect(..))`, 4. The job starts `Waiting`, runs `Running(1)`,
`Running(2)`, `Running(3)`, then the fourth step finishes it with
`Finished(3 * 100)` and the fifth step keeps it finished, so `total(job)` is
300. `corners(Shape::Empty)` is 0.
The `tiles` array holds `Rect(3, 2)`, `Empty`, `Circle(1)` and `Rect(1, 5)`, so
`count_corners` adds 4 + 0 + 1 + 4 = 9 and `is_wide(tiles[0].borrow())` is
true (3 > 2) and adds 100, giving `borrowed = 109`, which contributes
`109 * 10000 = 1090000`.
