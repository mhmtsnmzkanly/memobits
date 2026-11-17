# memobits-ownership

`check_moves(&Program)` performs a first-stage availability check over a valid
typed IR control-flow graph. Each parameter, including a reference handle, begins available. Other
locals become available after assignment or initialization. A `Consume` makes
a local or temporary unavailable; `Read`, `Borrow`, and `Share` require availability without consuming the source. Assignment
evaluates its value before restoring the target, including `x = x`. Lowering
never emits `Consume` for primitive values (it emits `Copy`, a `Read`), so only
aggregates and reference handles become unavailable after a use; the pass itself
is type-agnostic.

At joins, a value is available only if every incoming path has it available.
Loops are iterated to a fixed point. Unreachable blocks are ignored. The pass
reports BE001 at the original operand use, BE003 for malformed IR, and BE004 when an
assignment marks an immutable local as a reassignment rather than an
initialization.

This pass does not prove borrow lifetimes, mutable sharing, dominance, or all
language ownership rules. Call it only on IR produced after successful name
and type analysis.

`check_loans(&Program)` is a separate experimental pass over validated typed
IR. Run it alongside `check_moves` when both availability and loan checks are
needed. It tracks reference provenance through captures, reborrows, assignments,
and block parameters; reference liveness ends after its last use. It checks
owner writes and consumes, overlapping `Share` access, call argument loans,
and repeated live `Share` loan sites in loops. BE005 reports loan conflicts.
Invalid IR is rejected with BE003, and reference-valued function returns are
currently unsupported and reported with BE006. This pass is conservative at
control-flow joins and does not yet model returned-reference provenance or
implement complete language-level borrow semantics. The backend also does not
support reference returns.

Struct owners follow the array rules: `StructNew` consumes its field operands,
`FieldAddr` reads (not consumes) its owner and creates a loan, and any field loan
overlaps the whole struct (no field-disjoint reasoning yet).

Run tests with `cargo test --offline -p memobits-ownership`.

`check_ownership(&Program)` combines availability and loan analysis and is used
by CLI and backend gates. Reference availability covers locals, temporary handles,
and block arguments; joins require availability on every incoming path. Edge
arguments bind target parameters simultaneously without making an unavailable
argument available. This IR support does not enable source or Wasm references.

Reference transport through Capture, assignment, and CFG arguments requires
Consume. Explicit Borrow instructions create reborrows with a fresh loan site;
nonconsuming handle duplication reports BE002. Relocation is rejected while
conflicting descendant loans remain live. Store through a local share handle
requires a mutable binding; incoming share parameters retain write permission
without `var`. Scalar Load instructions produce snapshots, not memory views.
