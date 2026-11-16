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

A first artifact may use a Wasm trap for dynamic failure while the host error
protocol is being developed. The limitation must be documented; it is not a
stable error ABI. Statically proven failures should be diagnosed before encoding.

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
