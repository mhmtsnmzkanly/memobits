# Numeric project fixture

A minimal source project for the new compiler pipeline. Its application root is
`main::main`; its library root exports only `math::add` as `add`.

Project inventory can be inspected with:

```sh
cargo run -p memobits-cli -- project --project examples/projects/numeric/project.toml
```

Wasm execution and semantic checking will be added in subsequent milestones.
