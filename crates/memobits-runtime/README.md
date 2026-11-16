# memobits-runtime

`run(bytes, export)` validates a Wasm binary, rejects modules that require
imports, instantiates it, and calls a zero-parameter function export. The
result is `Unit`, `I32`, `I64`, `F32`, or `F64`, matching the Wasm representation.
Signedness and source-level narrow integer types are unavailable in a Wasm
artifact, so the runner does not reinterpret integer results.

Execution uses a fixed fuel budget to stop unbounded loops. Errors distinguish
invalid modules, unsupported imports, instantiation failures, missing exports,
unsupported signatures, traps, and fuel exhaustion. This is a small execution
API for the compiler pipeline; it does not claim a complete sandbox or host
ABI.

Run tests with `cargo test --offline -p memobits-runtime`.
