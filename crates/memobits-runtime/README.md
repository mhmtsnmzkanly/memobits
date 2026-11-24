# memobits-runtime

`run(bytes, export)` validates a Wasm binary, rejects modules that require
imports, instantiates it, and calls a zero-parameter function export. The
scalar result is `Unit`, `I32`, `I64`, `F32`, or `F64`, matching the Wasm
representation. Standalone scalar results carry no source-level signedness
or narrow integer type.

For `main` with a `memobits.entry` custom section, the runner validates the
private adapter and decodes its return cell as `RunValue::Outcome(EntryOutcome)` (`Ok`, `OkSome`, `OkNone` or `Err`).
Success payloads retain their Memobits primitive types. `Err`
carries the qualified concrete error name (or `Error` for the root) and its
`u32` code. Malformed adapter metadata, signatures, or return cells report
`RunError::EntryAbi`. See the [outcome ABI notes](../../docs/design/outcome-implementation.md).

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
