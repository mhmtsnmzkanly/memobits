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

`mb analyze FILE` runs standalone primitive type and loop-control checks after
successful parsing. It reports source diagnostics and rejects unsupported imports,
enum types, and borrow/share parameters (struct and alias declarations are supported). Ownership is not checked. This
command is an incremental compiler tool, not a project build or safety guarantee.

`mb ownership FILE` parses and type-checks a standalone source file, lowers it to
typed IR, and checks owned primitive move availability. Repeated arithmetic reads
are allowed, while reading a local after moving it reports a source diagnostic.
Borrow/share parameters remain unsupported (currently rejected by the type pass).
A successful result is limited to this owned primitive move analysis and is not
a safety guarantee.

`mb analyze-project [--project PATH] [--lib]` resolves the selected project roots
and checks primitive function signatures across local modules, including imports,
prelude aliases, and qualified calls. Loop control is checked in loaded modules.
User-defined types and ownership remain unsupported by this analysis path.

`mb ownership-project [--project PATH] [--lib]` resolves application entry modules
or library exports, lowers the supported typed primitive subset, and checks owned
primitive move availability across reachable modules. Source diagnostics are
rendered with their originating file and span. A successful check is limited to
that supported primitive subset and does not guarantee borrow safety.

`mb build [--project PATH] [--lib] [--output PATH]` lowers the selected
application entry or library exports to the supported primitive IR and compiles
them to WebAssembly. Application builds export the manifest entry as `main`;
library builds preserve export aliases. Type exports are currently unsupported.
The backend reports unsupported Wasm instructions as source diagnostics. By
default, application builds write `target/memobits/app.wasm` and library builds
write `target/memobits/library.wasm`, relative to the selected manifest's
directory. `--output` selects another path relative to the current directory.
The output is replaced atomically only after resolution, type and ownership
checks, lowering, and backend compilation all succeed, so a failed build leaves
an existing artifact intact.

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
`--no-fuel-limit`), `RE007` guest trap, and `RE008` stack overflow.

`[build].stack_size` (bytes, default 1048576, multiple of 16, 4096 to 268435456)
sets the stack used by `mb build` and `mb run`. A function frame larger than the
stack is an LE900 compile error; exhausting the stack at run time reports RE008.
