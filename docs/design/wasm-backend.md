# Initial Wasm backend

The first backend consumes validated typed IR after successful move checking.
It must not infer types or resolve source names. Its output is an experimental
core Wasm artifact; a stable cross-language ABI is a later design milestone.

## Control flow and values

An explicit program-counter dispatcher loop can encode arbitrary IR control
flow, including graphs that are not reducible to nested source constructs.
Short-circuit expressions retain their existing branches. Edge arguments are
parallel transfers: evaluate into scratch locals before updating target block
parameters. Sequential copies would corrupt swaps and some loop backedges.

Primitive representations use Wasm integer or floating-point types. Function
values require table indices and signature-checked indirect calls, or explicit
unsupported diagnostics until implemented. Unit needs a consistent representation
at calls, locals, and return boundaries. Unsupported IR must never be silently
reinterpreted.

## Numeric behavior

Default integer operations are checked in all profiles. Native Wasm wrapping
instructions alone do not implement the language contract. Narrow integers need
range checks as well as the correct signed/unsigned comparison and division.
Zero divisors, signed division overflow, and negation of the signed minimum need
explicit treatment. Floating-point operations retain IEEE behavior.

Explicit `as` casts cover every pair among the supported integer and
floating-point types. The IR retains both source and target types so Wasm can
select signed or unsigned conversion instructions. Integer narrowing keeps the
low bits; integer widening extends according to source signedness. Float to
integer conversion truncates toward zero, saturates, and maps NaN to zero.
Float-width conversions use Wasm's IEEE conversion instructions. The
`u8.to_u32()` convenience method lowers to the same typed cast. Assignment
does not perform implicit numeric conversion.

Dynamic failure is a Wasm trap preceded by a trap record (see "Trap reporting"
below); this is not a stable error ABI. Statically proven failures should be
diagnosed before encoding.

## Trap reporting

Every checked failure (integer overflow, division by zero, array bounds, input
range checks) must name its reason and source location instead of surfacing as a
bare `unreachable`.

**Record.** The module exports one mutable `i32` global, `__mb_trap` (global 2
when the module has frames, otherwise its only global). Immediately before a
checked trap, generated code stores `(location_id << 8) | reason_code` into it
and executes `unreachable`; that is one `i32.const` plus one `global.set` per
check site, inside the already-failing branch, so the success path is unchanged.
Location id 0 means unknown; ids are allocated per trapping instruction in
program order, starting at 1 (at most 2^23 - 1).

| Code | Reason | Message |
|---|---|---|
| 1 | Add | integer overflow in addition |
| 2 | Subtract | integer overflow in subtraction |
| 3 | Multiply | integer overflow in multiplication |
| 4 | Negate | integer overflow in negation |
| 5 | Division | native division site, see below |
| 6 | Remainder | native division site, see below |
| 7 | DivisionOverflow | integer overflow in division (narrow `MIN / -1`) |
| 8 | IndexOutOfBounds | array index out of bounds |
| 9 | ArgumentRange | argument out of range for its parameter type |
| 10 | HeapAllocation | guest heap allocation failed |
| 11 | ShiftCount | shift count must be less than 32 |
| 12 | AssertionFailed | assertion failed (`assert(false)`) |

Codes 5 and 6 are stored *before* a native Wasm division, which traps by itself.
The host refines them by the native trap kind: divide-by-zero gives "division by
zero" or "remainder by zero"; integer overflow gives "integer overflow in
division". After an `unreachable` trap these two codes are ignored (they may be
left over from an earlier successful division). Stack exhaustion keeps its own
flag, `__mb_stack_overflow`, and `RE008`.

**Location table.** The backend returns the span of each location id
(`compile_traced` -> `Compiled::trap_sites`; `compile_with` drops them). It has
no source text, so the driver resolves spans to file, line, column, caret width
and the source line, and appends them as a Wasm custom section named
`memobits.traps`: UTF-8 text, first line `memobits-traps 1`, then one line per
id (id = line number - 1): `file<TAB>line<TAB>column<TAB>width<TAB>text`. The
section is appended to the module for `mb build` and equally to the in-memory
module for `mb run`, so source runs and artifacts report identically, and an
artifact is self-describing (the line text is included so no source is needed).
`memobits-runtime` reads `__mb_trap` after a trap and returns
`RunError::Checked { reason, location }`; the CLI renders it as `RE007` with a
caret snippet. A module without the `memobits.traps` section (stripped, or built
by an older compiler) keeps the generic `RunError::Trap` message.

## Memory layout and stack

The target memory layout places 16 reserved bytes first, followed by the
configured stack, static data, and the heap. Address zero is unused.
`static_data_start(stack_size)` in `crates/memobits-wasm/src/lib.rs` marks the
first address after the stack. The private [outcome entry adapter](outcome-implementation.md)
places its caller-owned return cell there. Reachable String literal data
follows that cell, or starts just after the stack when the cell is absent.
The checked static layout planner places these regions and rounds the
final end up to 64 KiB pages. The
[owned heap proposal](owned-heap-foundation.md) places growable storage
after the literal data.

The stack size is the build setting `[build].stack_size` (bytes, default 1 MiB,
a multiple of 16 between 4 KiB and 256 MiB), passed to the backend as
`CompileOptions::stack_size` (`compile` uses the default; `compile_with` takes
options). Frames grow upward, 16-byte aligned, with the stack pointer in
global 0. There is no per-function frame limit: a frame larger than the
configured stack is an LE900 diagnostic naming the frame size and the stack
size, with a hint to raise `[build].stack_size`; layout arithmetic is checked.
At run time, entering a frame that does not fit sets the exported flag global
`__mb_stack_overflow` and traps with `unreachable` before the stack pointer is
touched; `memobits-runtime` reports that as `RunError::StackOverflow`
(`RE008`). Storage placement is a backend decision; language rules, IR and
ownership do not depend on it. Memory, flag and layout remain experimental ABI.

## Verification

Independent Wasm validation checks binary structure. Execution tests must also
check numerical results, branches, loops, call evaluation order, parallel edge
arguments, and dynamic failures. Test expected language behavior directly: the
removed AST interpreter never defined the semantics and is not a conformance oracle.

Backend output is not evidence of a stable ABI, complete borrow safety, or
full language support. These remain separate verification gates.

## Numeric execution gate

Runtime tests must pass operands as exported function parameters so literal
folding cannot hide missing dynamic checks. For each signed and unsigned width,
exercise valid boundaries and overflow for addition, subtraction, multiplication,
and negation where defined. Division requires zero checks and signed minimum
divided by minus one handling. Signed remainder for minimum modulo minus one
returns zero; it must not inherit the division overflow rejection.

Narrow integer parameters cross a wider Wasm i32 boundary. Reject external
values outside their declared source range before executing the body. Bool inputs
must obey the experimental representation contract. Arithmetic checks must run
in release builds as well as debug builds.

Float tests cover NaN, infinities, signed zero, comparisons, and division by zero
according to IEEE semantics. Exported unsigned 32/64-bit values preserve bits
through Wasm signed host integer APIs; host tests must interpret those bits as
unsigned when comparing expected results.

A constant-only test or a Wasm validator pass is insufficient evidence for these
runtime rules. Generated modules must execute with assertions on results and
error paths. Indirect calls and unsupported types require explicit diagnostics
until implemented.

`u32.wrapping_add` and `u32.wrapping_mul` are explicit modulo-2^32 operations.
They emit Wasm i32 add and multiply directly, while ordinary `+` and `*` retain
the checked numeric path.

`u32` bitwise operators and `bit_and`, `bit_xor`, and `bit_or` use Wasm i32
operations. Unsigned shifts accept `u32` counts below 32; constant invalid
counts fail analysis, and dynamic invalid counts trap with their source site.
The right-shift instruction is unsigned, so it fills high bits with zero.
