# Enums project

A buildable project for the enum packages B1 and B2. `src/main.mb` declares a
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
  the loop writes `job = advance(job);`.

Still gated: matching a `borrow`/`share` enum, a field or an element (B3),
nested patterns, literal patterns, guards, `==` on enums (use `match`), and
enums in `main` or `[export]` signatures. See
`docs/design/enum-implementation.md`.

```sh
cargo run -p memobits-cli -- run --project examples/projects/enums/project.toml
cargo run -p memobits-cli -- build --project examples/projects/enums/project.toml
cargo run -p memobits-cli -- run examples/projects/enums/target/memobits/app.wasm
```

Observed output of each command, from the repository root (the absolute prefix
of the built path is shortened to the repository root):

```text
Result: i32(4300)
Built examples/projects/enums/target/memobits/app.wasm: 1 export(s), 3539 bytes
Result: i32(4300)
```

The result is 300 + 4000 + 0. The rectangle `2 x 4` has area 8 and the circle
of radius 2 has area `3 * 2 * 2 = 12`, so the two areas sum to 20 and `shapes`
is `corners(Shape::Rect(..))`, 4. The job starts `Waiting`, runs `Running(1)`,
`Running(2)`, `Running(3)`, then the fourth step finishes it with
`Finished(3 * 100)` and the fifth step keeps it finished, so `total(job)` is
300. `corners(Shape::Empty)` is 0.
