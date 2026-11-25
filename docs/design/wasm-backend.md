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

## Function values

A function value is one `i64`: the low 32 bits are its slot in the module's
function table, the high 32 bits an environment pointer (always 0 until closures
exist). Before encoding, the backend erases every function type to `u64`
(`function_values.rs`), so locals, fields, array and List elements, enum
payloads and call arguments need no special case. The heap-ownership facts are
computed on the typed program first, because they follow a call through a
function value to every address-taken function of the same signature.

The table has one slot per function that is used as a value and reachable, plus
slot 0, which stays empty; an active element segment at offset 1 fills the rest.
A function used as a value is `i64.const <slot>`. A call through a value pushes
the arguments (and the hidden result pointer of an aggregate result), checks
`slot - 1 < slots` (otherwise trap reason 13, below), and `call_indirect`s with the
Wasm type of the callee's signature (signatures are deduplicated with the
functions' own types). Modules without function values have no table or element
section. Function values cannot be exported or returned by the entry function.

### Owned closures (H5)

A function type that has an owned closure with captures somewhere in the program
is represented as a wrapper struct `{ call, env }` (a tuple-like IR struct named
after the function type): `call` is the function value above, `env` a `Box` of a
compiler-made enum with one variant per closure literal (plus `Plain`). The
variant holds the captured values. `ClosureOwned` builds `call` for a box: the
environment word is the address of the enum value inside the heap block (box
block + content offset). The table thunk of an owned closure computes each
capture address as `env + payload offset of the variant field` and calls the
lifted function with those addresses (a frame closure's thunk loads addresses
from its frame record instead). Release is ordinary struct/enum/box release: no
special code. A closure that mutates its environment is flagged by bit 31 of the
slot word (`ClosureOwned { mutating }`); when the program has such a closure,
every indirect call masks the bit before the table check and `ClosureReadOnly`
(emitted before calls through immutable places) traps with reason 14 when it is
set. Modules without owned closures are unchanged.

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
| 11 | ShiftCount | shift count must be less than the bit width |
| 12 | AssertionFailed | assertion failed (`assert(false)`) |
| 13 | InvalidFunction | call through an invalid function value (outside the function table) |
| 14 | MutatingClosure | a closure that mutates its environment was called through an immutable place |

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

Integer widths keep their value in a normalized Wasm local: `i8`, `i16`, `i32`
as sign-extended `i32`, `u8`, `u16`, `u32` as zero-extended `i32`, and `i64`,
`u64` as `i64`. The `wrapping_*`, `saturating_*` and `checked_*` methods, the
bitwise operators (and `bit_and`, `bit_xor`, `bit_or`) and the shifts exist for
all eight widths (`memobits-wasm/src/numerics.rs`):

- Wrapping `add`, `sub`, `mul` use the native instruction and re-normalize the
  8- and 16-bit results (mask or sign-extend). `wrapping_neg` is `0 - x`.
- Saturating `add`, `sub`, `mul` compute the exact result in `i64` for the
  narrow widths and clamp it; the 64-bit widths use the same overflow tests as
  the trapping operators and select the minimum or maximum.
- Checked operations produce the scalar option `T?` in a frame cell. The
  overflow flag is the option tag (Some = 0, None = 1); a zero divisor, the
  signed `MIN / -1`, and a shift count at or above the width are `None`.
  `MIN % -1` is `Some(0)`. `checked_neg` is `0 - x`.
- Shifts take a `u32` count. `<<` and `>>` trap when the count is at or above
  the width (a constant count is a compile error); `wrapping_shl`/`wrapping_shr`
  mask the count with `width - 1`; `checked_shl`/`checked_shr` return `None`.
  `<<` discards the high bits (re-normalized for narrow widths) and `>>` is
  arithmetic for signed types (`shr_s`) and zero-filling for unsigned types.

## Guest allocator (BK1)

`string_heap.rs` holds the private whole-block allocator shared by String,
List and Box. A block is an 8-byte header (`capacity` at offset 0, `next` at
offset 4) followed by `capacity` payload bytes; a descriptor's data pointer is
`block + 8`. `next` is only meaningful while the block is on a free list, which
is why the iterative release worklists (see below) may borrow it while the
block is still allocated; `capacity` is never touched by them.

Free blocks live in segregated size classes. A small static table (bitmap word
plus one list head per class, `TABLE_BYTES` = 216 bytes, reserved beside the
other static regions and zero-initialised by fresh memory) holds 52 classes:
exact four-byte steps from 4 to 32 bytes, then four classes per octave
(40, 48, 56, 64, 80, 96, ... up to 65,536 bytes). A request up to 65,536
bytes is rounded up to its class size, so a block's capacity is always an exact
class size, and the request pops the head of the lowest non-empty class at or
above its own (one `ctz` over the bitmap). `release` recomputes the class from
the block's capacity and pushes it; both are O(1). Blocks above the limit stay
on the single exact-size list (`FREE_GLOBAL`, global 4), searched first-fit; a
small request that finds no small class reuses that list's head before the heap
grows. There is no splitting or coalescing. Failure semantics are unchanged: a
reservation that cannot grow memory returns zero without touching any list.
Programs that never use the heap emit no allocator (byte-identical Wasm); heap
programs grow by about 450 bytes of code plus the 216-byte table.

## Recursive owner release (H4, H4b)

A type that reaches itself through a `List` or `Box` element cannot have its
type-directed release walk emitted inline. `crates/memobits-wasm/src/recursive.rs`
finds those types and appends one `(i32) -> ()` release function per type plus
one shared `() -> ()` `drain` function after the thunks. The release emitter
calls `release_T` with the address of the value. `release_T` walks the value's
own fields inline and defers every box or list position whose element mentions a
recursive type onto an intrusive worklist (one global head per kind, after the
five fixed globals); `drain` pops and processes items in a loop, so the call
depth is constant and no memory is needed beyond the structure. A box item
links through its block header's free-list word, a list item through its
descriptor's data word. See `docs/design/box.md`.

A `Box` is a one-pointer cell (`box_cell.rs`, 4 bytes): the address of a block
holding one value at `CONTENT_OFFSET` (8), or 0 when empty.
