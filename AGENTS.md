# Repository guidance

Write code, diagnostics, comments, and documentation in English.

When adding or changing a supported language feature, update the runnable
guide in `examples/projects/language-guide/src/main.mb` in the same change.
Show executable behavior with a small checked example. For features that
require multiple modules or CLI setup, point to an existing runnable example
and explain the setup and current limits in the guide's comments.
Verify the documented source and standalone Wasm runs and check any changed
documentation links and commands.
