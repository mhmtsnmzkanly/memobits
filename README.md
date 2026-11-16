# Memobits

Memobits is an experimental statically typed language implemented in Rust.
The existing implementation is an AST-walking interpreter. A new Wasm compiler
architecture is being developed incrementally in the `crates/` workspace.
An initial experimental Wasm backend and `mb build` command are available for
the supported primitive subset. Runtime integration and language features are
still being developed.

## Existing interpreter

```bash
cargo run -- examples/simple/18_property.mb
cargo run -- examples/complex/05_validation_suite.mb
```

Performance measurements:
```bash
cargo run -- --performance examples/complex/05_validation_suite.mb
```

## Development

```bash
cargo test --workspace
```

New crates have their own tests. The existing interpreter remains available as
a reference while the replacement is developed. Legacy code and examples may
still contain historical syntax and Turkish text; new code and documentation
use English.

## Design

- [Accepted decisions](docs/design/decisions.md)
- [Implementation plan](docs/design/implementation-plan.md)
- [Illustrative syntax guide](examples/design/language-guide.mb) (not executable)

`DOCS.md` documents the legacy implementation and is not the new language specification.

## New compiler tools

```sh
cargo run -p memobits-cli -- project --project examples/projects/numeric/project.toml
cargo run -p memobits-cli -- syntax examples/projects/numeric/src/main.mb
cargo run -p memobits-cli -- analyze examples/projects/numeric/src/math.mb
cargo run -p memobits-cli -- resolve --project examples/projects/numeric/project.toml
cargo run -p memobits-cli -- resolve --project examples/projects/numeric/project.toml --lib
```

`project` inventories module candidates. `syntax` parses one file and reports
source diagnostics. `resolve` checks reachable local modules, names, and import
visibility. `analyze FILE` checks standalone primitive types and loop control.
These commands do not perform full type or ownership checking.
The primitive subset supports `mb build` and `mb run`.

```sh
cargo run -p memobits-cli -- run --project examples/projects/numeric/project.toml
cargo run -p memobits-cli -- build --project examples/projects/numeric/project.toml
cargo run -p memobits-cli -- run examples/projects/numeric/target/memobits/app.wasm
```

Source and artifact execution use the same Wasm runtime. Artifact results use raw
Wasm numeric representations; source execution can display source type names.
