# Repository guidance

Write code, diagnostics, comments, and documentation in English.

When adding or changing a supported language feature, update the runnable
guide in `examples/guide/` in the same change: put the check in the matching
topic module under `examples/guide/src/` as a `test fn` that uses `assert`
(one `assert` per fact). `main` in `examples/guide/src/main.mb` stays a small
program that returns `Ok(42)`; do not route checks through it.
Show executable behavior with a small example checked by `test fn` and
`assert`. For features that require multiple modules or CLI setup, point to an
existing runnable example and explain the setup and current limits in the
guide's comments.
Verify the guide with `mb test --project examples/guide/project.toml`, update
the expected test count in `examples/guide/README.md`, and verify the
documented source and standalone Wasm runs. Check any changed documentation
links and commands.
