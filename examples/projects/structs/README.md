# Structs project

A buildable project for the first struct slice (A1). `main::main` declares two
struct types: `Size` in the application module, with `i32`, `Bool` and `u8`
fields, and `Point` in `src/geom.mb`, whose fields are all `pub` and which
`main` uses through `use geom::Point;`.

It covers the supported A1 subset: type declarations `type Size { .. }` with
trailing commas, literals whose fields are written in a different order from
the declaration, `let` bindings of struct values, primitive field reads inside
arithmetic (`s.width * s.height`) and in an `if` condition on a `Bool` field,
implicit copies of a field into a binding (`let width := s.width;`,
`let level: u8 = s.scale;`), and the `main() -> i32` entry point.

Structs cannot be moved, passed, returned or assigned as whole values; reading a
primitive field copies it implicitly and leaves the struct whole. See `docs/design/struct-implementation.md` for the checkpoint.

```sh
cargo run -p memobits-cli -- run --project examples/projects/structs/project.toml
cargo run -p memobits-cli -- build --project examples/projects/structs/project.toml
cargo run -p memobits-cli -- run examples/projects/structs/target/memobits/app.wasm
```

Observed output of each command, from the repository root:

```text
Result: i32(26)
Built examples/projects/structs/target/memobits/app.wasm: 1 export(s), 782 bytes
Result: i32(26)
```

The result is 12 (`s.width * s.height`) + 10 (`p.x * p.y`) + 3 (the copied
`width`) + 1 (the `bonus` from `scale == 2`), since `square` is true.
