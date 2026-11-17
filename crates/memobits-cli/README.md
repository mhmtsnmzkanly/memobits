# mb

`cargo run -p memobits-cli --bin mb -- project [--project PATH]` loads a
`project.toml` manifest and prints its metadata and deterministic module inventory.
The override is a manifest file, resolved relative to the current directory;
source paths are resolved relative to that manifest. No source parsing,
dependency loading, compilation, or execution is performed.

`cargo run -p memobits-cli --bin mb -- resolve [--project PATH] [--lib]`
resolves reachable local modules from `package.entry` by default, or from
the manifest's exports with `--lib`. It parses those modules and checks local
imports, visibility, and names. Unreachable source files are not parsed.
Successful output lists the reachable modules in sorted order. Source errors
include diagnostic codes and source locations; project errors use the PE codes
below. Resolution does not check further semantics, types or ownership, load external dependencies,
compile, or execute code.

`mb syntax FILE` parses one source file without semantic checking.
`mb --help` documents the supported interface. `check` explicitly fails as
unsupported. The existing `memobits` binary is unchanged.

Errors use the shared diagnostics renderer with these stable project codes:

| Code | Meaning |
| --- | --- |
| PE001 | Project filesystem I/O failure, including a missing manifest/source root |
| PE002 | TOML deserialization failure, including unknown or missing fields |
| PE003 | Manifest validation or module discovery validation failure |
| PE004 | Invalid command-line usage |
| PE005 | Explicitly unsupported check command |
| PE006 | Unsupported build target or export |
| PE007 | Invalid `[build]` setting, such as a `stack_size` out of range or not a multiple of 16 |

Successful commands exit 0 and write stdout; failures exit 1 and write stderr.
Tests launch the real `mb` executable with isolated temporary directories and
require no network access: `cargo test --offline -p memobits-cli`.

`mb analyze FILE` parses and checks standalone types and loop control. It does
not perform ownership checking; standalone imports require project resolution.
Structs, enums, aliases, arrays, matches, and supported references are covered
within the implemented subset.

`mb ownership FILE` checks supported typed IR moves and loans for one source
file. `mb analyze-project` and `mb ownership-project` apply the corresponding
checks across reachable local modules after project resolution. These commands
report successful completion of their implemented subset, not a proof of safety
for every possible language feature.

`mb build [--project PATH] [--lib] [--output PATH]` lowers the selected
application entry or library exports to WebAssembly. The implemented subset
includes primitives, fixed arrays, structs, enums, internal calls, and internal
primitive/aggregate references. External imports and aggregate/reference export
signatures remain unsupported. Application builds export the manifest entry as
`main`; library builds preserve export aliases. Type exports are currently
unsupported. The output is replaced atomically only after resolution, checking,
lowering, and backend compilation succeed. By default, application builds write
`target/memobits/app.wasm` and library builds write
`target/memobits/library.wasm` relative to the manifest; `--output` is relative
to the current directory.

`mb run [--project PATH]` lowers and compiles the selected application entry in
memory, then executes its `main` WebAssembly export. `mb run FILE.wasm
[--entry NAME]` runs an existing artifact's export, defaulting to `main`. Both
forms use the same fuel-limited Wasm runtime; source execution does not use a
separate interpreter.

Both forms accept `--fuel N` to set the execution budget to `N` fuel units, a
positive integer. The default is 10000000000 (ten billion), which ordinary
programs never reach while runaway loops still end. `--no-fuel-limit` disables
metering entirely, so loops run until they finish or trap; it cannot be combined
with `--fuel`. Invalid values, including `0`, negative or non-integer numbers,
and repeated or conflicting options, are usage errors (PE004). Successful calls print `Result: ...` and exit 0. A guest
numeric result is not used as the process exit code. Source runs can label scalar
results with their Memobits type; artifact runs only know the Wasm scalar type
because artifacts do not include source type metadata. Unit functions print
`Result: Unit`. Runtime failures use RE diagnostics and exit nonzero. The runtime
currently supports zero-argument exports, scalar results, and modules without
host imports.

Runtime diagnostic codes are `RE001` invalid Wasm, `RE002` unsupported host
import, `RE003` instantiation error, `RE004` missing export, `RE005` unsupported
signature, `RE006` fuel exhaustion (raise the budget with `--fuel N` or use
`--no-fuel-limit`), `RE007` guest trap, and `RE008` stack overflow. A checked failure (integer
overflow, division by zero, array index out of bounds) is an RE007 that names the
reason and shows the source line and column, for source runs and built artifacts
alike; an artifact without the `memobits.traps` section reports the generic trap.

`[build].stack_size` (bytes, default 1048576, multiple of 16, 4096 to 268435456)
sets the stack used by `mb build` and `mb run`. A function frame larger than the
stack is an LE900 compile error; exhausting the stack at run time reports RE008.
