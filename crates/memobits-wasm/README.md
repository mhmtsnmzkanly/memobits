# memobits-wasm

This crate contains an experimental Wasm backend for the validated primitive
IR. `compile(&Program, &BTreeMap<String, FunctionId>)` first validates IR and
rejects move-analysis errors, then emits a Wasm module. The caller chooses the
application entry export or library export aliases; the backend does not infer
project visibility or roots.

The current backend supports primitive signatures, constants, captures,
assignments, direct calls, returns, branches, and arbitrary basic-block edges.
It uses a dispatcher loop for control flow and stages edge arguments before
copying block parameters. Integer arithmetic checks overflow, division by zero,
and signed minimum divided by negative one. Floating operations use Wasm IEEE
behavior. Invalid Bool, Unit, and narrow integer parameters trap at function
entry. Indirect calls and non-primitive types are reported with LE900.

The current ABI is experimental: Bool and 8/16/32-bit integers use Wasm i32;
64-bit integers use i64; f32/f64 map directly; Unit has no external result.
Internal Unit values use a zero-valued i32 slot. No ABI stability or source
mapping guarantee is implied.

Runtime checks currently trap with Wasm `unreachable`; mapping those traps to
source-aware Memobits runtime diagnostics is pending. Source spans are retained
in backend compile diagnostics, but no runtime source map is emitted.

Internal primitive references execute using private linear-memory addresses.
Address-taken owner locals use authoritative frame cells for reads and writes;
reference reborrows reuse addresses. Typed loads preserve integer signedness and
width. Per-invocation frames are restored on normal and early returns. The fixed
private stack occupies addresses [16, 65536); exhaustion traps. Traps do not
unwind frames; the current runtime discards its instance after execution.

Reference parameters are supported only for internal calls. Fixed arrays of
primitive elements and nested arrays execute as locals, as owned, `borrow` and
`share` parameters of internal calls (an owned array is copied from caller
storage into the callee's own frame cell; a reference is the owner's cell
address), as array-valued `if`/block results (array block parameters are frame
cells; a join edge copies the argument) and as call results (struct-return: a
hidden trailing pointer parameter addresses the call's own cell in the caller's
frame, and `return` copies into it). Element access is bounds-checked on every
index and traps out of range. Exported signatures that use arrays or references
(parameters or results), reference returns, and indirect calls remain
unsupported. The private pointer representation is not a stable ABI.

A struct local or value also owns an inline frame cell. Fields are laid out in
declaration order at natural alignment (size and alignment of the struct are those of
its largest field, size rounded up) using checked arithmetic; the cell shares the
configured stack size (`[build].stack_size`) limit with arrays, and an oversized struct is a backend diagnostic.
`StructNew` stores each field at its offset, in place in the destination local's cell
when it is bound immediately (the array construction mechanism), and `FieldAddr` adds
the constant field offset to the cell address (a struct owner's cell or a struct
reference's pointer), so `Load` is unchanged. Structs reuse the array aggregate paths:
owned struct parameters are copied into the callee's cell, `borrow`/`share` parameters
are the owner's address, results go through the hidden trailing pointer, struct block
parameters are frame cells, and whole-struct `Assign`/`Capture`/`Store` are
`memory.copy`. `main` and `[export]` signatures with structs or struct references are
rejected with LE900 (no external struct ABI). Aggregates nest (A3): a struct or array field
is stored inline at its own natural alignment (written with `memory.copy` from the field
operand's cell), arrays of structs stride by the struct size, and layout is computed
dependencies first with checked arithmetic (overflow is a diagnostic, an oversized frame
the usual stack-size diagnostic). Chained `ElementAddr`/`FieldAddr` add runtime-checked
element offsets and constant field offsets to the root cell address. `Extract` (A4
destructuring) loads a primitive field at its constant offset, or `memory.copy`s an
aggregate field into the output value's own frame cell.

`cargo test --offline -p memobits-wasm` validates generated modules with
wasmparser and executes representative exports with wasmi.
