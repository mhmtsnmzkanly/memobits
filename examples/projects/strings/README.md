# Strings project fixture

A minimal source project for owned and borrowed `string` operations. Its
application root is `main::main`; concat, borrow, share and push_str are checked
over a literal, a concat result and an owned binding.

Project inventory can be inspected with:

```sh
cargo run -p memobits-cli -- project --project examples/projects/strings/project.toml
```

The string fixture checks the length of the original literal and of the suffixed
concat result, and a struct-owned label built through concat.

```sh
cargo run -p memobits-cli -- run --project examples/projects/strings/project.toml
cargo run -p memobits-cli -- build --project examples/projects/strings/project.toml
cargo run -p memobits-cli -- run examples/projects/strings/target/memobits/app.wasm
```

Both run commands print the same result.

```text
Result: i32(0)
```
