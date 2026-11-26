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
cargo run -p memobits-cli -- run --project examples/topics/numeric/project.toml
cargo run -p memobits-cli -- build --project examples/topics/numeric/project.toml
cargo run -p memobits-cli -- run examples/topics/numeric/target/memobits/app.wasm
```

Source and artifact execution use the same Wasm runtime. Standalone scalar
artifacts display raw Wasm numeric types. Application entries returning
`T ! E` or `T ?! E` with a primitive success payload display the same
variant, typed payload, or concrete error in both modes. This uses a private
Wasm adapter for `main`. Function-local `(borrow T)?` supports explicit
construction, local moves and consuming matches. See the [outcome implementation notes](docs/design/outcome-implementation.md).

Inspection commands:

```sh
cargo run -p memobits-cli -- project --project examples/topics/numeric/project.toml
cargo run -p memobits-cli -- syntax examples/topics/numeric/src/main.mb
cargo run -p memobits-cli -- analyze examples/analysis/numeric.mb
cargo run -p memobits-cli -- resolve --project examples/topics/numeric/project.toml [--lib]
```

See `crates/memobits-cli/README.md` for all commands.

## Development

```sh
cargo test --workspace
cargo clippy --workspace --all-targets
```

Code, diagnostics, and documentation are written in English.

## Design and status

- [Roadmap and status](docs/roadmap.md) — what is done, what is next, known open items.
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

Examples live under `examples/`: the runnable [guide](examples/guide/README.md),
small [topics](examples/topics), larger [apps](examples/apps) and single-file
[analysis](examples/analysis) inputs. Each project README has an "Expected
output" section; `crates/memobits-cli/tests/examples_documented.rs` runs every
project from source and as standalone Wasm and compares the output to it. See
[examples/README.md](examples/README.md) for the layout and verification.

| Example | Topic | Command | Expected output |
|---|---|---|---|
| [guide](examples/guide/README.md) | Whole language, one module per topic | `cargo run -p memobits-cli -- run --project examples/guide/project.toml` | `Result: Ok(i32(42))` |
| [basics](examples/topics/basics/README.md) | Arithmetic, loops and `string` basics as modules of one project | `cargo run -p memobits-cli -- run --project examples/topics/basics/project.toml` | `Result: Ok(i32(462))` |
| [arrays](examples/topics/arrays/README.md) | Fixed arrays: locals, calls, results, nested arrays | `cargo run -p memobits-cli -- run --project examples/topics/arrays/project.toml` | `Result: Ok(i32(493))` |
| [core-only](examples/topics/core-only/README.md) | `[build] alloc = false`, literals, arrays, `match`, and core string operations | `cargo run -p memobits-cli -- run --project examples/topics/core-only/project.toml` | `Result: Ok(i32(57911))` |
| [enums](examples/topics/enums/README.md) | Variants, `match`, exhaustiveness, aliases, state machine | `cargo run -p memobits-cli -- run --project examples/topics/enums/project.toml` | `Result: Ok(i32(1094300))` |
| [generics-operators](examples/topics/generics-operators/README.md) | `core::ops` Add/Sub/PartialEq on a `Vec2`, multi-bound and higher-order generic functions | `cargo run -p memobits-cli -- run --project examples/topics/generics-operators/project.toml` | `Result: Ok(i32(41))` |
| [host-capability](examples/topics/host-capability/README.md) | CLI host import declared in the manifest, bound with `extern fn` | `cargo run -p memobits-cli -- run --project examples/topics/host-capability/project.toml` | `Host i32: 42` and `Result: i32(7)` |
| [module-imports](examples/topics/module-imports/README.md) | Direct module imports and extension activation | `cargo run -p memobits-cli -- run --project examples/topics/module-imports/project.toml` | `Result: Ok(i32(42))` |
| [numeric](examples/topics/numeric/README.md) | Minimal project with a library `[export]` | `cargo run -p memobits-cli -- run --project examples/topics/numeric/project.toml` | `Result: Ok(i32(42))` |
| [structs](examples/topics/structs/README.md) | Constructors, `share`/`borrow` parameters, nesting, disjoint loans | `cargo run -p memobits-cli -- run --project examples/topics/structs/project.toml` | `Result: Ok(i32(63))` |
| [astar](examples/apps/astar/README.md) | Fixed-grid A* search with an unreachable-goal case | `cargo run -p memobits-cli -- run --project examples/apps/astar/project.toml` | `Result: Ok(i32(12))` |
| [enf-lexer](examples/apps/enf-lexer/README.md) | Bounded ENF byte lexer fixture | `cargo run -p memobits-cli -- run --project examples/apps/enf-lexer/project.toml` | `Result: Ok(i32(0))` |
| [hashing](examples/apps/hashing/README.md) | FNV-1a, DJB2 and Adler-32 over `array<u8, N>` | `cargo run -p memobits-cli -- run --project examples/apps/hashing/project.toml` | `Result: Ok(u32(1774777415))` |
| [tree](examples/apps/tree/README.md) | Binary search tree through `Box<T>` | `cargo run -p memobits-cli -- run --project examples/apps/tree/project.toml` | `Result: i32(3235)` |
| [utf8-validator](examples/apps/utf8-validator/README.md) | Unicode scalar validation with byte offsets | `cargo run -p memobits-cli -- run --project examples/apps/utf8-validator/project.toml` | `Result: Ok(i32(0))` |

Build and run a standalone artifact, for example the guide:

```sh
cargo run -p memobits-cli -- build --project examples/guide/project.toml
cargo run -p memobits-cli -- run examples/guide/target/memobits/app.wasm
```

The default CLI also runs a built core Wasm artifact with Wasmtime:

```sh
cargo run -p memobits-cli -- exec examples/guide/target/memobits/app.wasm
```

`mb run` and `mb test` use Wasmi. `mb exec` accepts core Wasm artifacts, with
`--entry`, `--project`, and the same fuel options as artifact `run`. Build the
CLI with `--no-default-features` to omit Wasmtime and `mb exec`.

## Language notes

- The guide's [collections module](examples/guide/src/collections.mb) demonstrates `contains(value) -> bool` and
  `index_of(value) -> u32?` on fixed arrays of numbers or `bool`
  (including `array<u8, N>`) and on `List<u8>` and `List<u32>`.
  It also demonstrates `loop value in items` over those fixed arrays and Lists.
  [Fixed array iteration](docs/design/fixed-array-implementation.md#fixed-array-iteration)
  · [List iteration](docs/design/list-slice.md#list-iteration)
  · [Runnable language guide](examples/guide/src/collections.mb)
- `drop(value)` consumes a whole named owned `string`, `List<u8>`, or
  `List<u32>` local or parameter and releases any heap storage it owns.
  Any live borrow or share prevents the drop. The binding is unavailable on
  every path that drops it until it is assigned again, if mutable.
  An in-scope function, import, or value named `drop` takes precedence over the
  built-in. [Runnable example](examples/guide/src/ownership.mb)
