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
and repeated live `Share` loan sites in loops. BE005 reports loan conflicts in source terms (for example "cannot write `l.a.x`
while it is shared") with notes at the place where the live loan began and where
it is used later; identical diagnostics (same code and span) are reported once.
Invalid IR is rejected with BE003, and reference-valued function returns are
currently unsupported and reported with BE006. This pass is conservative at
control-flow joins and does not yet model returned-reference provenance or
implement complete language-level borrow semantics. The backend also does not
support reference returns.

Struct owners follow the array rules: `StructNew` consumes its field operands,
`FieldAddr` reads (not consumes) its owner (a struct local or a reference to one) and
creates a loan. `Extract` (destructuring) reads or, last, consumes its owner like any
other owner operand. Whole structs move like arrays (`Assign`, `Capture`, call arguments,
returns, join arguments); a field write or a move while a borrow of the struct is live
is BE005, and two `Share` arguments of one struct in a call are BE005. A2 and A3
(nested structs, array fields, arrays of structs; mixed `FieldAddr`/`ElementAddr` chains)
needed no new rules beyond the paths below.

Enums (B1) need no new rules: `EnumNew` consumes its payload operands, an enum owner moves
as a whole value (BE001 afterwards), and a `Borrow` of an enum owner is a loan rooted at its
place. With no projection into an enum yet, every access overlaps the whole enum
(BE005 for an assignment, move or conflicting reference while one is live).

Owned `match` (B2): `EnumTag` is a read and `VariantExtract` follows `Extract` (a read, or the
consuming use on the last payload of an arm). `Switch` is a branching terminator like
`Branch`: its tag and edge arguments are operands, and availability and liveness flow along
each edge, so a payload move is legal only on its arm's path and an enum consumed in some
arms is unavailable after the join (BE001). Lowering moves the scrutinee into a hidden local
first, which is the single consume of the source value.

Borrowing `match` (B3): `VariantAddr` is an address instruction like `FieldAddr` whose loan
path step is `Step::Variant(variant, field)`. Different variants of one enum overlap (shared
storage); the same variant's different payload fields are disjoint. A live payload borrow
therefore blocks writes to the scrutinee place or its enclosing places (BE005, with the place
rendered as `` `l.a::Rect.0` `` in the "borrowed here" label) and allows disjoint places.

Field-disjoint loans (A4). Provenance and loans track *places*: a root (local, temporary,
reference parameter, or external) plus a projection path of steps `Field(i)`,
`Const(n)` (an index that is an integer `Constant` instruction) and `Dynamic` (any other
index). `Borrow` keeps the owner's path; `FieldAddr` and `ElementAddr` extend it by one
step (a path below an external root is not extended). Two places overlap when they have the
same root and every step of the shorter path may equal the corresponding step of the longer
one: distinct fields never overlap, distinct constant indices never overlap, a dynamic index
may equal any index, and a prefix (a parent) overlaps everything below it. External roots
overlap each other. This rule is applied to loan creation, loads, stores, owner moves and
assignments, terminator operands and call arguments (`f(l.a.share(), l.b.share())` and
`f(m[0].share(), m[1].share())` pass; `f(m[i].share(), m[j].share())` does not). Two
refinements keep chains precise: an address value used exactly once as the base of another
address instruction (`g.rows` in `g.rows[0]`) is path computation, so its creation is not
checked as an access of its own place; and a loan that is live only as an ancestor of a live
reference does not conflict by itself, the live descendants cover the memory still
reachable. When in doubt, places overlap.

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
