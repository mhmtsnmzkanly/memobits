# memobits-runtime

`run(bytes, export)` validates a Wasm binary, rejects modules that require
imports, instantiates it, and calls a zero-parameter function export. The
result is `Unit`, `I32`, `I64`, `F32`, or `F64`, matching the Wasm representation.
Signedness and source-level narrow integer types are unavailable in a Wasm
artifact, so the runner does not reinterpret integer results.

`run_with(bytes, export, &RunOptions { fuel })` takes the same inputs with an
explicit budget. `RunOptions::fuel` is `Some(n)` for `n` fuel units of metered
execution, or `None` for unlimited execution, which does not enable fuel
metering at all. `run` uses `RunOptions::default()`, which is metered with
`DEFAULT_FUEL` (ten billion units). The `mb` CLI exposes this as `--fuel N` and
`--no-fuel-limit`.

Errors distinguish invalid modules, unsupported imports, instantiation failures,
missing exports, unsupported signatures, traps, fuel exhaustion, and stack
overflow. A checked failure (integer overflow, division by zero, array bounds)
is `RunError::Checked` with a `TrapReason` and, when the module carries the
`memobits.traps` custom section, a `SourceLocation`; `TrapTable` and
`with_trap_table` write and read that section. Modules without it keep the
generic `RunError::Trap`. This is a small execution
API for the compiler pipeline; it does not claim a complete sandbox or host
ABI.

Run tests with `cargo test --offline -p memobits-runtime`.
