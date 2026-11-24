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
`mb --help` documents the supported interface. `mb check [--project PATH] [--lib]`
runs every build stage (resolution, types, lowering, IR validation and the Wasm
layout gates) with the same diagnostics as `build`, but writes no artifact. The existing `memobits` binary is unchanged.

Errors use the shared diagnostics renderer with these stable project codes:

| Code | Meaning |
| --- | --- |
| PE001 | Project filesystem I/O failure, including a missing manifest/source root |
| PE002 | TOML deserialization failure, including unknown or missing fields |
| PE003 | Manifest validation or module discovery validation failure |
| PE004 | Invalid command-line usage |
| PE005 | Unused (formerly the unsupported check command) |
| PE006 | Unsupported build target or export |
| PE007 | Invalid `[build]` setting, such as a `stack_size` out of range or not a multiple of 16 |

The `MW` prefix is reserved for non-failing warnings, which render as
`warning[MWnnn]: message` with the same file, line, column and caret layout as
errors. The channel is wired through the parser, resolver and every source
command (warnings print to stderr as soon as the source is parsed, before any
error, and never change the exit status or suppress an error), but no warning
is currently emitted: MW001 to MW003 and the old type spellings they covered
were removed, and a removed spelling is now an error. Removed spellings fail
with TE001 and name the replacement: `Option<T>` becomes `T?`, `Result<T, E>`
becomes `T ! E`, `Attempt<T, E>` becomes `T ?! E`, `Bool` becomes `bool`,
`Char` becomes `char` and `Array<T, N>` becomes `array<T, N>`. `Bytes` no longer
exists and is an ordinary unknown type; use `array<u8, N>`. A unit test in
`memobits-syntax` keeps the channel itself covered. Running a prebuilt `.wasm`
artifact has no source and prints no warnings.

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
primitive/aggregate references. `List<T>` (after `use alloc::List;`) holds any
admitted element type (primitives of every width, `bool`, `char`, `string`,
structs, tuples, enums and arrays). Nested lists (`List<List<T>>`) work:
`outer.push(inner)` moves a List in, `outer[i]` is a List place (`outer[i][j]`
reads, `outer[i].push(x)`, `.pop()`, `.clear()`, `.len()`, `.get()`,
`.borrow()` / `.share()`, `replace`, `swap` and `outer[i] = v` all work through
the element place), `outer.pop()` moves an inner List out, and the outer List
releases every inner List exactly once. Arrays of Lists, Lists inside structs
or user enums, and `Some(list)` stay gated.
An `if`/`match` expression may produce a `string`, List or String-owning
aggregate anywhere a value is accepted (binding, argument, assignment, tail
result): each branch moves its value into one hidden destination before the
join, and the unchosen branch's inputs are released with their own scopes. A
struct literal may be a function's tail expression. A branch that cannot fall
through (`return`, `break`, `continue`) joins with the other branch's type.
`try expr else [name] { handler }` unwraps a `T ! E` or `T?` (the `!` layer of
`T ?! E`): the handler yields the success type or exits, and an `Err` payload
binds as an owned `name`. `target = try expr;` leaves the target unchanged on a
failure and `try expr;` discards one; `try` without `else` anywhere else is
SE002, a non-fallible operand is TE029, a name on a `T?` is TE030, and a
handler of the wrong type is TE013.
`loop i in a..b` (half-open) and `loop i in a..=b` (inclusive) iterate an integer
range: the bounds share one integer type (an untyped literal takes the other
bound's type, otherwise `i32`; a mismatch is TE002, a non-integer bound TE017),
are evaluated once, left to right, before the first iteration, and `i` is
immutable. An empty range runs zero times; `..=` ending at the type's maximum
terminates without overflow. A range outside a `loop ... in` header is SE002.
A string literal may interpolate identifiers: `"x = {x}"` reads the in-scope
local or parameter `x` without moving it (a `string` is borrowed, a number,
`bool` or `char` is copied, and the usual loan rules apply: BE005 while it is
exclusively shared, BE001 after a move). `{{` and `}}` write literal braces;
a lone `}`, an unterminated or empty `{` and anything but one identifier inside
the braces (expressions, field access, calls, format specifiers) is SE001.
Integers of every width format in decimal (`-` for negatives, exact at the
64-bit extremes), `bool` as `true`/`false`, `char` as its UTF-8 bytes and
`string` as its bytes; floats are TE017 "not supported yet" and every other
type TE017 "cannot interpolate a value of type". An interpolating literal is an
owned heap `string` built with one length pass and one allocation, valid in
any position that accepts a String value; under `[build] alloc = false` it is
TE033. A literal without placeholders stays a static literal.
Contextual empty `[]` and non-empty `[a, b, c]` literals build a List (elements
run once in written order and move in). `items[i]` is a bounds-checked element
place: primitives are copied, other elements are used in place (borrow/share
receiver or argument, in-place `match`, projections); moving one out is TE022 (use `replace`, `swap` or `pop`); an owning
element is overwritten with `items[i] = v` (the old value is released once),
`replace(items[i], v)` (returns the old value) or `swap(a, b)`; a live element
loan blocks `push`,
`pop`, `clear`, moves and reassignment (BE005). `.get(i)` is primitive-only
(TE022 points to `items[i]` otherwise), `.contains`/`.index_of` need primitive
elements (TE017 otherwise), `.pop()` moves an owner out, and `loop x in items`
binds copies of primitive elements and read-only loans of other elements (the
same holds for `loop x in array` over non-copyable array elements). The
List releases every owned element exactly once on `clear`, reassignment, drop
and scope exit. A List supports local moves, and non-consuming `.len()`.
`.push(value)` appends through a whole mutable local. Empty construction
allocates no heap block. `.get(index)` copies an element into `T?`
and returns `None` when the `u32` index is outside the List. Direct internal
`borrow List<T>` parameters accept explicit read-only borrows and support
`.len()` and `.get()`. Direct `share List<T>` parameters and stored `var`
share handles support the same mutations as whole mutable locals.
`.pop()` returns the last element as `Some(value)` or `None` if empty.
`.clear()` sets the length to zero and returns unit. Both retain backing storage. A direct internal owned List parameter
takes a named local by move or a direct internal List result, as in
`consume(make_list())`. Arguments run left to right. The caller releases the
owned temporary on a normal early exit from a later argument, and the callee
owns it once invoked. A direct internal List return moves a named
callee local into a new or mutable caller binding. Whole mutable local
replacement releases the previous block after evaluating the RHS.
A String-owning struct, record, tuple or array temporary (a literal
or a direct call result) can be passed straight to an owned parameter: it is
staged in a hidden local, so the callee receives a named owner and an early
exit from a later argument releases it. `replace(place, value)` accepts an `if`
or `match` expression of owners as `value`: each branch moves its value into the
replacement slot. A struct literal may mix a String field with owner and
owner-array fields. A type derived from `Error` cannot own heap Strings, directly or through a nested owner (LE900:
"Error-derived type 'T' cannot own heap Strings yet"). A BE005 overlap
reported for `swap(a, b)` notes that swap needs two disjoint places and that
dynamic indices into one collection are not provably disjoint.
A direct share parameter or a stored `var` share handle can also replace
the owner's List. A standalone direct internal call statement releases its
unused List result. Use `make_list().len()` or `make_list().get(index)` to
read a direct internal List result. The receiver runs once before the index,
which also runs once. The temporary is released after the read or on a
normal early exit from the index. A direct internal `borrow List<T>` parameter
also accepts `make_list().borrow()` when the factory is a direct internal call.
Arguments run left to right, and the caller releases the temporary after the
call or on a normal early exit from a later argument. Storing that borrow,
sharing a temporary, other temporary uses, subscript syntax,
indirect calls, and exported List signatures remain gated. Ordinary UTF-8 `String` literals execute
with owned transfers and internal references. Use `.len()` for the UTF-8
byte length, `.is_char_boundary(offset)` to test a byte offset, and
`.byte_at(index)` to read a raw byte as `u8?`. Use `.scalar_at(index)`
to decode a Unicode scalar at a byte offset as `u32?`.
`bytes.validate_utf8(length)` borrows a fixed `array<u8, N>` prefix and returns
a scalar count or a typed error with a byte offset.
`bytes.to_utf8_string(length)` validates the same prefix and copies it
into an owned String on success. Its Result uses the immediate consuming
match rules for heap Strings. See the
[UTF-8 validator](../../examples/apps/utf8-validator/README.md).
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
`String ! E` can return a static String to a consuming match.
A heap-backed `Ok` can be bound and immediately matched in the same
function with explicit `Ok(value)` and `Err` arms. A direct internal call
can also return a heap-backed Result to an immediate consuming match, with
an optional binding. Ignoring the success owner, forwarding the Result
without matching it, and general nested String storage are gated.
A plain local struct can contain String fields alongside primitive fields.
A new local struct can initialize a String field with a literal, a named
heap String move, direct concat, or a direct internal String-returning call.
The whole struct can move into another new local, whose scope exit releases
any owned String allocations. Direct internal calls can take a read-only
borrow of a named struct owner and read its fields. The caller retains
cleanup. String fields support borrowed reads and
replacement on a mutable local using a named owned String, a literal, a
direct concat, or a direct internal String-returning call. See the
[local struct example](../../examples/guide/src/main.mb)
and its [Wasm limits](../../docs/design/owned-heap-foundation.md#local-structs-with-string-fields).

Application builds export the manifest entry as
`main`. A zero-argument application entry can return `T ! E` or `T ?! E`
(that is, `T? ! E`) with `bool`, an integer, or a float as `T`.
The private adapter applies to `main` and uses the `memobits.entry` custom
section. Library builds preserve export aliases and support scalar function
signatures.
The CLI host profile supports the single typed declaration
`extern fn write_i32(value: i32);`, backed by the matching manifest capability.
Other source-declared imports and type exports remain unsupported. The output is replaced atomically only after resolution, checking,
lowering, and backend compilation succeed. By default, application builds write
`target/memobits/app.wasm` and library builds write
`target/memobits/library.wasm` relative to the manifest; `--output` is relative
to the current directory.

`mb run [--project PATH]` lowers and compiles the selected application entry in
memory, then executes its `main` WebAssembly export. `mb run FILE.wasm
[--entry NAME] [--project PATH]` runs an existing artifact's export, defaulting
to `main`. A project manifest can enable `memobits:console.write_i32(i32) ->
unit` with `[host] profile = "cli"` and one `[[host.imports]]` declaration.
In project source, declare it with `extern fn write_i32(value: i32);` and call
`write_i32(42)`. The host prints the supplied integer. Imports must match the
declared module, name, and signature; undeclared and unsupported imports fail
before guest execution. Both forms use the same fuel-limited Wasm runtime;
source execution does not use a separate interpreter. See the
[host capability example](../../examples/topics/host-capability/README.md).

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
`Result: Ok(u32(7))` for `T ! E`, and `Result: Ok(Some(bool(true)))`,
`Result: Ok(None)` or `Result: Err(pkg::parser::ParseError, code=5)` for
`T ?! E`. `Err` returns the concrete error type and its `u32` code. The builtin root is printed
as `Error`. Guest traps and other runtime failures use RE diagnostics and exit
nonzero. Without a project profile, the runtime accepts zero-argument exports
from modules without host imports.

Runtime diagnostic codes are `RE001` invalid Wasm, `RE002` unsupported host
import, `RE003` instantiation error, `RE004` missing export, `RE005` unsupported
signature, `RE006` fuel exhaustion (raise the budget with `--fuel N` or use
`--no-fuel-limit`), `RE007` guest trap, `RE008` stack overflow, and `RE009`
invalid outcome entry adapter. A checked failure (integer overflow, division by zero, array index out of bounds, a false `assert`) is an RE007 that names the
reason and shows the source line and column, for source runs and built artifacts
alike; an artifact without the `memobits.traps` section reports the generic trap.

`[build].stack_size` (bytes, default 1048576, multiple of 16, 4096 to 268435456)
sets the stack used by `mb build` and `mb run`. A function frame larger than the
stack is an LE900 compile error; exhausting the stack at run time reports RE008.

`[build] alloc = true|false` (default `true`) selects the alloc layer. `List<T>`
lives in the compiler-provided virtual module `alloc` and must be imported with
`use alloc::List;` (a direct or grouped symbol import, or `use alloc;` with the
path `alloc::List<T>`); without the import `List` is an unknown type (NE003) and
a note names the import. Renaming it (`use alloc::List as X;`) is not supported.
With `alloc = false` the build is core-only: any `alloc` import is ME012 and
every heap-producing string operation (`concat`, `push_str`, `to_utf8_string`)
and every interpolating string literal is TE033, both naming `[build] alloc`; string literals and read-only string
operations (`len`, `byte_at`, `scalar_at`, `is_char_boundary`, `validate_utf8`)
keep working, and the emitted module contains no allocator function, no
`memory.grow` and a memory whose maximum equals its minimum. The setting
applies to `check`, `build`, `run` and `test` and is independent of
`[host] profile`. See `examples/topics/core-only`.

## Source-level tests

A top-level `test fn name() { ... }` declares a test: no parameters, no result
(or `Unit`), no generic parameters, and is never `pub`. Violations are
syntax errors (SE002). Tests are checked like ordinary functions with their
module's visibility, so a test can call the private items of its own module,
but nothing can call a test (`unknown name ... (test functions cannot be
called)`). Test names share the module's namespace, so a test cannot reuse the
name of another item.

`assert(condition)` is a built-in taking a `bool`; it works in ordinary code
and in tests. A false condition is a controlled trap with the reason
`assertion failed` (trap code 12) and the source location of the call, and
discards the instance like every other trap. A function, import or value named
`assert` in scope takes precedence, as with `drop`. A wrong argument count is
TE010 and a non-`bool` argument is TE002.

- Tests are excluded from `mb build` and `mb run` artifacts and from
  reachability: a normal artifact is byte-identical with or without tests, and
  modules used only by tests are not loaded. `mb build` and `mb run` check only
  the modules reachable from the application or library roots and ignore tests
  (a broken test or an unreachable broken module does not fail them).
  `mb check` is the whole-project check: it always checks the roots and then
  every project module and every test, reporting errors in unreachable modules
  and in tests (it never writes an artifact).
- `mb test [--project PATH] [--fuel N | --no-fuel-limit] [FILTER]` compiles the
  test artifact from every module of the project (including modules the
  application does not import), runs each test in a fresh instance under the
  normal fuel and `stack_size` limits, and prints a report to stdout. The
  FILTER is a substring of the qualified name `module::name`.
- `mb build --tests [--project PATH] [--output PATH]` writes the test artifact
  (default `target/memobits/tests.wasm`). It exports each test as
  `test::<module>::<name>`. `mb check --tests` compiles it without writing.
- `mb test FILE.wasm [FILTER]` runs an existing test artifact and prints the
  same report as the source form (`--project` supplies host capabilities, as
  for `run`; trap locations come from the artifact's `memobits.traps` section).
- Exit status: 0 when every selected test passes (including zero tests), 1 when
  any test fails or the project does not compile (compile errors go to
  stderr; the report goes to stdout).

```text
running 3 tests
test main::also_passes ... ok
test main::fails ... FAILED
    assertion failed
     --> src/main.mb:8:5
     8 |     assert(value == 5);
       |     ^^^^^^^^^^^^^^^^^^
test main::passes ... ok

test result: FAILED. 2 passed; 1 failed; 0 filtered out
```

Tests are listed in qualified-name order. A project without tests prints
`running 0 tests` and `test result: ok. 0 passed; 0 failed; 0 filtered out`.
