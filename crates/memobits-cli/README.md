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
The ownership commands check owned `String` transfers and internal loans.

`mb build [--project PATH] [--lib] [--output PATH]` lowers the selected
application entry or library exports to WebAssembly. The implemented subset
includes primitives, fixed arrays, structs, enums, internal calls, and internal
primitive/aggregate references. `List<u8>` and `List<u32>` support
contextual empty `[]`, local moves, and non-consuming `.len()`.
`.push(value)` appends through a whole mutable local. Empty construction
allocates no heap block. Element access and List call signatures remain
gated in this slice. Ordinary UTF-8 `String` literals execute
with owned transfers and internal references. Use `.len()` for the UTF-8
byte length, `.is_char_boundary(offset)` to test a byte offset, and
`.byte_at(index)` to read a raw byte as `Option<u8>`. Use `.scalar_at(index)`
to decode a Unicode scalar at a byte offset as `Option<u32>`.
`bytes.validate_utf8(length)` borrows a fixed `Bytes<N>` prefix and returns
a scalar count or a typed error with a byte offset.
`bytes.to_utf8_string(length)` validates the same prefix and copies it
into an owned String on success. Its Result uses the immediate consuming
match rules for heap Strings. See the
[UTF-8 validator](../../examples/projects/utf8-validator/README.md).
`let joined := left.concat(right);` borrows its inputs and allocates owned
text for that binding. The result can be read, borrowed, or moved to
another local. A whole mutable String local can be replaced. The RHS runs
before the previous allocation is released. A direct internal call can take multiple owned
String arguments, evaluated left to right. Scope exit releases it from the binding that
still owns it. An internal function can return an owning local when the
direct call initializes or replaces a whole caller local. Standalone concat
and direct call statements release discarded results. The four read-only
methods above can also read an immediate concat or direct call result.
An explicit `.borrow()` on either result can supply a `borrow String`
argument to a direct internal call. The owner is released after the call
or on an earlier normal exit during argument evaluation. Owned String
parameters can receive those results directly. The callee takes ownership
when invoked. A direct `share String` parameter can replace a mutable
caller local passed as `text.share()`. The caller owns the replacement.
`text.push_str(suffix)` borrows a String suffix, appends it to a mutable
whole local or direct `share String` parameter, and returns unit. It uses
checked concat followed by replacement.
Installing heap text through forwarded shares or share aliases, other
nested heap uses and exported String signatures are gated. An internal
`Result<String, E>` can return a static String to a consuming match.
A heap-backed `Ok` can be bound and immediately matched in the same
function with explicit `Ok(value)` and `Err` arms. A direct internal call
can also return a heap-backed Result to an immediate consuming match, with
an optional binding. Ignoring the success owner, forwarding the Result
without matching it, and other nested String storage are gated. Application
builds export the manifest entry as
`main`. A zero-argument application entry can return `Result<T, E>` or
`Attempt<T, E>` with `Bool`, an integer, or a float as its success payload.
The private adapter applies to `main` and uses the `memobits.entry` custom
section. Library builds preserve export aliases and support scalar function
signatures.
External imports and type exports remain unsupported. The output is replaced atomically only after resolution, checking,
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
and repeated or conflicting options, are usage errors (PE004). Normal returns
print `Result: ...` to stdout and exit 0. Source runs label scalar results with
their Memobits type. Standalone scalar artifacts display the Wasm scalar type.
Unit functions print `Result: Unit`.

Outcome entries display the same result in both modes, such as
`Result: Ok(u32(7))`, `Result: Done(Bool(true))`, `Result: Skipped`, or
`Result: Failed(pkg::parser::ParseError, code=5)`. Both `Err` and `Failed`
return the concrete error type and its `u32` code. The builtin root is printed
as `Error`. Guest traps and other runtime failures use RE diagnostics and exit
nonzero. The runtime accepts zero-argument exports from modules without host
imports.

Runtime diagnostic codes are `RE001` invalid Wasm, `RE002` unsupported host
import, `RE003` instantiation error, `RE004` missing export, `RE005` unsupported
signature, `RE006` fuel exhaustion (raise the budget with `--fuel N` or use
`--no-fuel-limit`), `RE007` guest trap, `RE008` stack overflow, and `RE009`
invalid outcome entry adapter. A checked failure (integer overflow, division by zero, array index out of bounds) is an RE007 that names the
reason and shows the source line and column, for source runs and built artifacts
alike; an artifact without the `memobits.traps` section reports the generic trap.

`[build].stack_size` (bytes, default 1048576, multiple of 16, 4096 to 268435456)
sets the stack used by `mb build` and `mb run`. A function frame larger than the
stack is an LE900 compile error; exhausting the stack at run time reports RE008.
