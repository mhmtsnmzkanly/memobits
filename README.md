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
Wasm adapter for `main`. Function-local `(borrow T)?` supports explicit
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
- [Historical language proposal](docs/design/proposed-language-guide.mb) (not executable; superseded by the decisions and the runnable guide).

## Examples

Every project under `examples/projects/` has a README with an "Expected output"
section; `crates/memobits-cli/tests/examples_documented.rs` runs each project
from source and as standalone Wasm and compares the output to it. Run any of
them with:

```sh
cargo run -p memobits-cli -- run --project examples/projects/language-guide/project.toml
cargo run -p memobits-cli -- build --project examples/projects/language-guide/project.toml
cargo run -p memobits-cli -- run examples/projects/language-guide/target/memobits/app.wasm
```

- [language-guide](examples/projects/language-guide/README.md) — the runnable
  walkthrough of the executable language; prints `Result: Ok(i32(42))`.
- [arrays](examples/projects/arrays/README.md) — fixed arrays: locals, calls,
  results and nested arrays.
- [astar](examples/projects/astar/README.md) — fixed-grid A* search with a
  checked optimal cost and an unreachable-goal case.
- [calculator](examples/projects/calculator/README.md) — arithmetic over
  internal calls chained into a checked total.
- [computation](examples/projects/computation/README.md) — iterative
  computation with loops: `factorial` and an iterative sum.
- [enf-lexer](examples/projects/enf-lexer/README.md) — bounded ENF byte lexer
  fixture (see the [design note](docs/design/enf-lexer-slice.md)).
- [enums](examples/projects/enums/README.md) — variants, `match` with
  exhaustiveness, enum aliases and a state machine.
- [hashing](examples/projects/hashing/README.md) — FNV-1a, DJB2 and Adler-32
  over `Array<u8, N>` with software wrapping arithmetic.
- [host-capability](examples/projects/host-capability/README.md) — a CLI host
  import declared in the manifest and bound with `extern fn`.
- [module-imports](examples/projects/module-imports/README.md) — direct module
  imports and extension activation across modules.
- [numeric](examples/projects/numeric/README.md) — minimal project with a
  library `[export]`.
- [strings](examples/projects/strings/README.md) — owned and borrowed `string`
  operations: `concat`, `borrow`, `share` and `push_str`.
- [structs](examples/projects/structs/README.md) — constructors, `share` and
  `borrow` parameters, nesting, disjoint loans and destructuring.
- [utf8-validator](examples/projects/utf8-validator/README.md) — Unicode scalar
  validation of byte buffers with byte offsets for malformed input.
- `examples/analysis/` — single files for the analysis and ownership commands.

## Language notes

- The language guide demonstrates `contains(value) -> Bool` and
  `index_of(value) -> u32?` on fixed arrays of numbers or `Bool`
  (including `Array<u8, N>`) and on `List<u8>` and `List<u32>`.
  It also demonstrates `loop value in items` over those fixed arrays and Lists.
  [Fixed array iteration](docs/design/fixed-array-implementation.md#fixed-array-iteration)
  · [List iteration](docs/design/list-slice.md#list-iteration)
  · [Runnable language guide](examples/projects/language-guide/src/main.mb)
- `drop(value)` consumes a whole named owned `string`, `List<u8>`, or
  `List<u32>` local or parameter and releases any heap storage it owns.
  Any live borrow or share prevents the drop. The binding is unavailable on
  every path that drops it until it is assigned again, if mutable.
  An in-scope function, import, or value named `drop` takes precedence over the
  built-in. [Runnable example](examples/projects/language-guide/src/main.mb)
