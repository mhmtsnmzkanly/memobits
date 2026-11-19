# Memobits

Memobits is an experimental statically typed language with ownership-based
memory safety, compiled to portable WebAssembly. The compiler is a Rust
workspace under `crates/`. It is developed incrementally: the executable
subset is small and the output ABI is not stable.

## Workspace

| Crate | Role |
| --- | --- |
| `memobits-project` | `project.toml` loading and module discovery |
| `memobits-diagnostics` | Source locations, diagnostic codes, rendering |
| `memobits-syntax` | Lexer, parser, syntax tree |
| `memobits-resolve` | Modules, imports, names, visibility |
| `memobits-analysis` | Type and control-flow analysis, lowering to IR |
| `memobits-ir` | Typed control-flow IR and validation |
| `memobits-ownership` | Move, borrow, and share checking |
| `memobits-wasm` | Wasm emission |
| `memobits-entry-abi` | Private metadata format for Wasm outcome entries |
| `memobits-runtime` | Wasm execution host |
| `memobits-cli` | The `mb` command |

## Usage

```sh
cargo run -p memobits-cli -- run --project examples/projects/numeric/project.toml
cargo run -p memobits-cli -- build --project examples/projects/numeric/project.toml
cargo run -p memobits-cli -- run examples/projects/numeric/target/memobits/app.wasm
```

Source and artifact execution use the same Wasm runtime. Standalone scalar
artifacts display raw Wasm numeric types. Application entries returning
`Result` or `Attempt` with a primitive success payload display the same
variant, typed payload, or concrete error in both modes. This uses a private
Wasm adapter for `main`. Function-local `Option<borrow T>` supports explicit
construction, local moves and consuming matches. See the [outcome implementation notes](docs/design/outcome-implementation.md).

Inspection commands:

```sh
cargo run -p memobits-cli -- project --project examples/projects/numeric/project.toml
cargo run -p memobits-cli -- syntax examples/projects/numeric/src/main.mb
cargo run -p memobits-cli -- analyze examples/analysis/numeric.mb
cargo run -p memobits-cli -- resolve --project examples/projects/numeric/project.toml [--lib]
```

See `crates/memobits-cli/README.md` for all commands.

## Development

```sh
cargo test --workspace
cargo clippy --workspace --all-targets
```

Code, diagnostics, and documentation are written in English.

## Design and status

- [Accepted decisions](docs/design/decisions.md) — the target language.
- [Implementation plan](docs/design/implementation-plan.md) — milestones and
  the current implemented subset.
- [Fixed arrays](docs/design/fixed-array-implementation.md) — array
  implementation sequence and checkpoints.
- [Structs](docs/design/struct-implementation.md) — struct implementation
  sequence through destructuring and disjoint field loans.
- [Enums](docs/design/enum-implementation.md) — enum implementation sequence
  through enum values, owned `match`, and borrowing `match`.
- [Outcome types](docs/design/outcome-implementation.md) — compiler-known
  templates and remaining implementation gates.
- [Illustrative syntax guide](examples/design/language-guide.mb) (not executable).

## Examples

- [Runnable language guide](examples/projects/language-guide/src/main.mb)
  walks through the executable language. Both runs below print
  `Result: Ok(i32(42))`.

```sh
cargo run -p memobits-cli -- run --project examples/projects/language-guide/project.toml
cargo run -p memobits-cli -- build --project examples/projects/language-guide/project.toml
cargo run -p memobits-cli -- run examples/projects/language-guide/target/memobits/app.wasm
```

- `examples/projects/` — buildable projects with a `project.toml`.
- [A* grid search](examples/projects/astar/README.md) checks the optimal cost
  around a wall and verifies that closing the gap makes the goal unreachable.
- [Bounded ENF lexer fixture](docs/design/enf-lexer-slice.md) checks decimal
  tokens, byte spans and error outcomes.
- [Guest UTF-8 validator](examples/projects/utf8-validator/README.md) checks
  Unicode scalar encodings and reports byte offsets for malformed input.
- `examples/projects/arrays/` — fixed arrays: locals, calls, results and nested arrays.
  Use `Bytes<N>` as a built-in spelling for `Array<u8, N>`.
- The language guide demonstrates `contains(value) -> Bool` and
  `index_of(value) -> Option<u32>` on fixed arrays of numbers or `Bool`,
  including `Bytes<N>`, and on `List<u8>` and `List<u32>`.
  It also demonstrates [`loop value in items`](docs/design/fixed-array-implementation.md#fixed-array-iteration) over those fixed arrays.
  [Runnable language guide](examples/projects/language-guide/src/main.mb)
- `examples/projects/structs/` — structs: a constructor function, a share-mutating
  function, a borrow-reading function, literals, field reads and a two-module use of
  public fields.
- `examples/projects/enums/` — enums: variants, `match` with exhaustiveness, aliases of
  enum types and a state machine stepped in a loop.
- `examples/analysis/` — single files for the analysis and ownership commands.
- `examples/design/` — illustrative target syntax.
