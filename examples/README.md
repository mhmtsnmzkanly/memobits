# Examples

Every example is a Memobits project with its own `project.toml` and a README
whose `## Expected output` section documents the exact stdout.

## Layout

```text
examples/
  guide/      the runnable language guide, one project split into topic modules
  topics/     small projects that each teach one area
  apps/       larger programs built from several features
  analysis/   single-file inputs for the analyze and ownership commands
```

## Catalog

| Example | Topic | Command | Expected output |
|---|---|---|---|
| [guide](guide/README.md) | Whole language, one module per topic | `cargo run -p memobits-cli -- run --project examples/guide/project.toml` | `Result: Ok(i32(42))` |
| [basics](topics/basics/README.md) | Arithmetic, loops and `string` basics as modules of one project | `cargo run -p memobits-cli -- run --project examples/topics/basics/project.toml` | `Result: Ok(i32(462))` |
| [arrays](topics/arrays/README.md) | Fixed arrays: locals, calls, results, nested arrays | `cargo run -p memobits-cli -- run --project examples/topics/arrays/project.toml` | `Result: Ok(i32(493))` |
| [enums](topics/enums/README.md) | Variants, `match`, exhaustiveness, aliases, state machine | `cargo run -p memobits-cli -- run --project examples/topics/enums/project.toml` | `Result: Ok(i32(1094300))` |
| [generics-operators](topics/generics-operators/README.md) | `core::ops` Add/Sub/PartialEq on a `Vec2` and a bounded generic function | `cargo run -p memobits-cli -- run --project examples/topics/generics-operators/project.toml` | `Result: Ok(i32(41))` |
| [host-capability](topics/host-capability/README.md) | CLI host import declared in the manifest, bound with `extern fn` | `cargo run -p memobits-cli -- run --project examples/topics/host-capability/project.toml` | `Host i32: 42` and `Result: i32(7)` |
| [module-imports](topics/module-imports/README.md) | Direct module imports and extension activation | `cargo run -p memobits-cli -- run --project examples/topics/module-imports/project.toml` | `Result: Ok(i32(42))` |
| [numeric](topics/numeric/README.md) | Minimal project with a library `[export]` | `cargo run -p memobits-cli -- run --project examples/topics/numeric/project.toml` | `Result: Ok(i32(42))` |
| [structs](topics/structs/README.md) | Constructors, `share`/`borrow` parameters, nesting, disjoint loans | `cargo run -p memobits-cli -- run --project examples/topics/structs/project.toml` | `Result: Ok(i32(63))` |
| [astar](apps/astar/README.md) | Fixed-grid A* search with an unreachable-goal case | `cargo run -p memobits-cli -- run --project examples/apps/astar/project.toml` | `Result: Ok(i32(12))` |
| [enf-lexer](apps/enf-lexer/README.md) | Bounded ENF byte lexer fixture | `cargo run -p memobits-cli -- run --project examples/apps/enf-lexer/project.toml` | `Result: Ok(i32(0))` |
| [hashing](apps/hashing/README.md) | FNV-1a, DJB2 and Adler-32 over `array<u8, N>` | `cargo run -p memobits-cli -- run --project examples/apps/hashing/project.toml` | `Result: Ok(u32(1774777415))` |
| [utf8-validator](apps/utf8-validator/README.md) | Unicode scalar validation with byte offsets | `cargo run -p memobits-cli -- run --project examples/apps/utf8-validator/project.toml` | `Result: Ok(i32(0))` |

`host-capability` needs the CLI host profile declared in its manifest; the
others run with the default profile.

## How examples are verified

`crates/memobits-cli/tests/examples_documented.rs` discovers every
`project.toml` under `guide/`, `topics/*/` and `apps/*/`. For each project it
runs `mb check`, `mb build`, a source `mb run` and a standalone Wasm `mb run`,
requires empty stderr, and compares both stdout streams to the first ```` ```text ````
block after `## Expected output` in the project README. A project whose README
lacks that block fails the test. The CLI integration tests additionally run the
guide, `astar`, `enf-lexer` and `utf8-validator` in both modes.

When a supported language feature changes, update the guide in the same change
(see `AGENTS.md`).
