> Historical working document, moved from the local design folder on 2026-11-26.
> This is a dated snapshot, not a current work plan. Its task queues, pending
> items, approval requests, paths, commands, and status describe earlier
> checkpoints; do not treat them as current instructions. Current rules are in
> [../design/decisions.md](../design/decisions.md) and status in [../roadmap.md](../roadmap.md).

# Archived work-plan snapshot — D2 closure, phase 1

Written 2026-11-23 by the architect (Claude Opus). At the time, this file
replaced `next-agent-handoff.md` and `transfer-handoff.md`. Its acceptance
criteria and work packages record that checkpoint only; later evidence is
recorded in `launch-progress.md`. Historical logs and superseded notes live in
`archive/` and are not evidence for current code.

## Roles

- **Architect / reviewer (Opus):** owns this plan, design decisions and final
  acceptance. Reviews every report before a work package is marked done.
- **Contractor (Sonnet):** executes this plan, owns code changes that need
  judgment, owns the Cargo lock, and delegates mechanical work to Haiku.
- **Subcontractors (Haiku):** run one given command and report, apply an exact
  text edit, fix links, summarize a log. Haiku never designs, never edits
  compiler logic, never runs Cargo unless the contractor gave it the lock.

## Hard rules

1. **One Cargo command at a time, always `-j1`.** The contractor serializes;
   never run two agents that use Cargo concurrently. Haiku agents doing
   non-Cargo work may run in parallel.
2. Save every Cargo run to `.local-design/logs/<wp>-<short-name>.log`
   (`2>&1 | tee`). Report the exact command, pass/fail counts and the first
   failure's assertion text.
3. Preserve all existing WIP. No `git commit`, `git stash`, `git checkout --`,
   reset, or deletion of tracked files. No edits under `legacy/` or protected
   example dirs other than `examples/projects/language-guide/src/main.mb`.
4. Code, comments, diagnostics and docs in English (see `AGENTS.md`). A
   supported-language change must update the runnable guide in the same change
   and re-verify source + standalone Wasm.
5. Do not widen an ownership or ABI gate unless the WP explicitly says so and
   the required evidence is produced.
6. If blocked, stop that WP and report: minimal example, diagnostic, what was
   tried, exact question. Continue independent WPs.

## Current state (verified facts only)

- Working directory: `/root/memobits/memobits`, HEAD `c41b624`, large
  uncommitted WIP across `crates/` and the guide.
- `memobits-cli --test d1_anonymous_shapes`: 13/13 pass (after direct-String
  enum payload ownership transfer fix).
- `memobits-cli --test cli wasm_gates_string_exports_and_nested_storage`
  FAILS: case expecting LE900 "nested Result<String, E> storage" now builds
  with exit 0. Two such cases (test at `crates/memobits-cli/tests/cli.rs:2468`):
  - `type Box { text: Result<string, Error> } fn main() {}`
  - `let result: Result<string, Error> = Ok("é"); let items := [result];`
- Still correctly rejected: direct `Array<String>`, String-owning struct nested
  in a struct, exported String signatures.
- Unverified since the last full run (1,127/1,129): aggregate-parameter
  prologue now clears moved String descriptors recursively by type and active
  enum tag (`crates/memobits-wasm/src/lib.rs`); IR `owns_string_storage`
  exception accepts direct `String` enum payloads
  (`crates/memobits-ir/src/lib.rs`); new direct-String enum variant in
  `tuple_destructure_memory_stress.rs` and in the guide.

## Work packages

### WP0 — Archive link repair (Haiku, no Cargo, parallel-safe)

Files moved to `.local-design/archive/superseded/`: `devir-notu.md`,
`struct-enum-plan.en.md`, `previous-workbook.en.md`, `experimental-findings.md`,
`audit-examples.md`, `audit-source-code.md`, `d1-generic-inherent-checkpoint.md`,
`transfer-verification.md`, `transfer-handoff.md`, `next-agent-handoff.md`.
All `*.log` moved to `.local-design/archive/logs/`.

Task: in `.local-design/*.md` (top level only) rewrite relative links to those
files so they point into `archive/superseded/` or `archive/logs/`. Change only
link targets. Report each file and count of rewritten links.
Done when `grep` finds no link to a moved file at its old path.

### WP1 — Nested `Result<String, E>` storage decision (Sonnet)

Architect decision: D2 requires enum payloads and nested aggregates with exact
move/drop, and `Result` is an enum. **Preferred outcome: accept** nested
`Result<String, E>` storage in struct fields and fixed-array elements — but only
if cleanup is proven. Otherwise restore an LE900 gate with a specific message.

Steps:
1. Read the Wasm layout/cleanup path that now admits these shapes and the IR
   heap-owner propagation for struct fields/array elements holding a Result.
   Confirm: active-tag dispatch (Ok payload released, Err payload per its
   type), moved-source clearing, and no release of inactive payload bytes.
2. Write positive source + standalone Wasm tests (new file
   `crates/memobits-cli/tests/d2_nested_result_storage.rs`, mirror helpers in
   `tuple_nested_arrays.rs`): a struct field holding `Ok(heap string)` and an
   `Err`, an array of Results, each read back through `match` with exact bytes
   or length; move out of the owner and use it.
3. Add a capped-memory stress case (normal + early return, repeated on one
   instance) next to the existing ones in `tuple_destructure_memory_stress.rs`.
4. Remove only the two nested-Result cases from
   `wasm_gates_string_exports_and_nested_storage`; keep every other case.
5. Add a small checked guide example.
If any step shows unsound cleanup, instead restore the gate and report why.

### WP2 — Safety review of unverified edits (Sonnet, read-only)

Review the aggregate-parameter prologue change and the `owns_string_storage`
exception against the checklist:
- incoming pointer still valid after the aggregate copy; correct callee scratch
  locals per nested array depth;
- active enum tag payloads with direct String, tuple and nested fixed array are
  cleared exactly once; inactive payload bytes never released;
- source-side ownership propagation for every construction and return path
  after the new exception (not just the tested path).
Report findings with file:line. Fix only confirmed defects, each with a test.

### WP3 — Focused verification (Haiku runner, Cargo lock from Sonnet)

Run strictly in order, one at a time, after WP1/WP2 edits are in:
1. `cargo test -j1 -p memobits-cli --test d1_anonymous_shapes`
2. `cargo test -j1 -p memobits-cli --test tuple_nested_arrays`
3. `cargo test -j1 -p memobits-cli --test tuple_destructure_memory_stress`
4. `cargo test -j1 -p memobits-cli --test d2_nested_result_storage`
5. `cargo test -j1 -p memobits-cli --test cli wasm_gates`
On failure: stop, report log path and assertion; Sonnet fixes, then rerun
from the failing step.

### WP4 — Full verification (Haiku runner, Cargo lock)

```sh
cargo test -j1 --workspace --no-fail-fast -- --test-threads=1
cargo build -j1 -p memobits-cli
mkdir -p target/plan-check
target/debug/mb run --project examples/projects/language-guide/project.toml
target/debug/mb build --project examples/projects/language-guide/project.toml --output target/plan-check/guide.wasm
target/debug/mb run target/plan-check/guide.wasm
```
Expected: all tests pass; both guide runs print `Result: Ok(i32(42))`.
Also run `cargo fmt --check` and `git diff --check`; report, don't auto-fix
format across unrelated files.

### WP5 — Records (Haiku with exact text from Sonnet)

Append one section to `launch-progress.md` ("D2 nested Result storage and
prologue verification") with commands, counts, log paths and decisions. Update
the D2 paragraph in `implementation-requirements.md` "Preparation status" to
match verified facts. Do not alter manifest rows.

## Phase 1 status — ACCEPTED by architect (2026-11-23)

Verified: workspace 1,133 passed / 0 failed (`logs/wp4-workspace-test.log`),
guide source and standalone Wasm `Result: Ok(i32(42))`. Nested
`Result<String, E>` storage accepted for literal `Ok` and `Err` payloads only;
heap Ok payloads stay rejected by IR (TE018). `cargo fmt --check` differs in
17 files of pre-existing WIP — not addressed (needs owner decision before a
format sweep over WIP).

## Phase 2 — D2 owner transport (phase 2a: hardening + design, no gate widening)

Remaining D2 manifest work: by-value nominal String-owner transport (owned
struct arguments/results), nested String-owning structs, consuming reads of
heap payloads from nested storage, complete tuple placement coverage. Other
open rows (M1, I1, G1, G2, OP1, D1 limit, D3, C1, H1) are not in scope.

### WP6 — IR `VariantExtract` hardening (Sonnet, code)

Phase-1 review found two weaknesses in `crates/memobits-ir/src/lib.rs`
(`VariantExtract` validation, ~lines 3470-3550):
1. For a non-local base, `variant_owns_heap_string` is false so `transferred`
   becomes true and the read-only `report` path is skipped; safety currently
   relies on an unrelated TE018 check downstream.
2. `extracted_owned_payload` scans the whole block instead of the extraction's
   own successor statements.
Make each check local and explicit so it does not rely on a later gate. Add
negative tests proving the IR validator itself (not only a later check)
rejects a borrowed / field / array-element heap payload extraction. Behavior
of accepted programs must not change: rerun the focused D2/D1 targets and the
full workspace (Haiku runner, Cargo lock rules as in phase 1).

### WP7 — Design proposal for by-value String-owner transport (Sonnet, NO code)

Write a section "Phase 2b design proposal" at the end of this file covering:
- Owned internal arguments/results of a flat String-owning nominal struct:
  where the current LE900 gate lives, how IR heap-owner propagation and Wasm
  descriptor clearing (reuse the type-directed cleanup from D2) would apply,
  caller/callee cleanup on normal and early return, temporaries.
- Nested String-owning nominal structs (struct inside struct, struct in
  array/tuple/enum payload): which existing gates must lift and in what order.
- Consuming `match` of heap payloads read from nested storage (field / array
  element) — what move-out semantics would be needed; if it needs implicit
  partial moves, mark it as a **blocker** per the requirements' escalation rules
  instead of designing it.
- Minimal test matrix for each (positive source/Wasm, capped stress, negative).
- Exact file:line touch points and an ordered slice list, smallest first.
The architect reviews and approves slices before any gate is widened.

## Report format (contractor → architect)

Per WP: status (done / blocked / failed), files changed, commands + log paths,
counts, decisions taken and why, open risks. Keep it under one screen.

## Phase 2b design proposal (WP7, contractor draft, no code written)

Status: proposal for architect review. No gate has been widened. All line
numbers refer to the working tree at the time of writing (WIP on top of
`c41b624`) and will drift.

### Baseline: what tuples already do and nominal structs do not

String-owning **tuples** (`module == "\0tuple"`) already travel by value. The
tuple exemption is spread over five independent gates, each keyed on the
`"\0tuple"` module name, which is exactly the set of places a nominal struct
would have to be admitted:

| # | Gate | Location | Tuple exemption |
|---|------|----------|-----------------|
| G-A | Signature gate "structs with String fields can cross internal calls only as borrow or share parameters" (the user-visible LE900) | `crates/memobits-wasm/src/lib.rs:425-433` (`validate_string_struct_borrows`, `is_string_tuple` at :411) | `!is_string_tuple(..)` on params and result |
| G-B | Owned-argument shape "an owned String tuple argument must move directly from a named tuple local" | `memobits-wasm/src/lib.rs:455-479` | only checked for tuples; nominal never reaches it because G-A fires first |
| G-C | Layout: struct with String fields may only hold String/primitive fields | `memobits-wasm/src/lib.rs:1110-1121` (`struct_layouts`) | `!is_tuple &&` |
| G-D | Nested String-owning struct field / array element | `memobits-wasm/src/lib.rs:1062-1070` (`member_layout`, flag `allow_nested_string_tuple`), `:1285-1290` (`type_layout`, `layout.is_tuple`) | `is_tuple_definition` |
| G-E | Ownership root for borrows of String-owning aggregates | `memobits-wasm/src/lib.rs:494-523` (`type_owns_string_storage`: tuples recurse into any field, nominal only into tuple-typed fields) | `is_tuple` |

Analysis-side tuple-only logic: `memobits-analysis/src/types.rs:1270`
(`contains_string_owner`), `:1314` (`tuple_has_unsupported_nested_string_owner`,
"other than tuples in this slice" at :1795 and :5336),
`memobits-analysis/src/lower.rs:579-600` (`supported_nested_string_tuple`),
and the free function `is_string_tuple_type` (`types.rs` ~:1325) which is
`"\0tuple"`-only.

IR side is already type-generic: `scoped_string::owns_string_aggregate`
(`memobits-ir/src/scoped_string.rs:841`) covers any `Struct`/`Enum`/`Array`.
Tuple-specific IR spots: `tuple_owns_string` (:819), `tuple_destructure_extractions`
(:975, requires `tuple_owns_string` at :1003), `direct_string_tuple_return`
(:1072; already type-generic through `owns_string_aggregate`),
`memobits-ir/src/lib.rs:3619` (`nested_tuple_move` in `StructNew`) and
`:3820` (`tuple_move` on `Return`). Wasm cleanup/prologue: type-directed and
active-tag aware (`emit_string_storage_cleanup` :2907, `clear_moved_heap_source`
:3074, owned-tuple Extract clearing :4526-4540); it keys on layout facts
(`has_string_fields`) rather than the tuple module, except line 4531.

### Slice 1 (smallest): owned flat String-owning nominal struct as internal argument

Scope: `type Label { text: string }` (fields only String and primitives, no
nesting) passed as an owned parameter from a **named local** moved with a
consuming use, internal functions only. No result transport yet.

Changes:
1. G-A (`memobits-wasm/src/lib.rs:419-433`): split the parameter and result
   clauses. Allow owned *parameters* of nominal String structs; keep the result
   clause and `is_string_struct_ref` clause untouched. Define
   `is_string_owner_struct = is_string_tuple || flat nominal` once and use it in
   G-B (`:463-478`) so the "must move directly from a named local" check covers
   nominal arguments too (it keys on `is_string_tuple(&parameter.ty)`; it must
   become the new predicate or temporaries slip through).
2. Analysis: `types.rs` call checking at :5320-5340 currently only polices
   tuples via `tuple_has_unsupported_nested_string_owner`; add a nominal flat
   check so nested nominal owners stay rejected with a TE017 message (the gate
   moves from LE900 late to TE017 early for the unsupported shapes; cases that
   remain LE900 stay LE900).
3. Wasm callee: the aggregate-parameter prologue already clears moved String
   descriptors by type and active tag (WP2 review); it must be confirmed to run
   for `Type::Struct` of a non-tuple definition (check the `guard_parameter`
   path at :3173 and the owned-aggregate parameter copy). Callee scope exit
   already releases an owned parameter local (same path as tuples).
4. IR heap-owner propagation: `StructNew` (`memobits-ir/src/lib.rs:3606-3625`)
   and `feeds_owned_call_argument` (:3382-3400, uses `owns_string_aggregate`
   and `parameter.ty == *source_ty`) are already generic. The new facts to add:
   a consuming call argument whose source is a heap struct local retires that
   local from `in_scope` in `scoped_string::validate` (verify the tuple path at
   :1070-1100 and :1405-1410 is not tuple-gated; `direct_string_tuple_return`
   is not).
5. Caller cleanup: normal and early return release the struct local only if it
   was not moved; the moved-source clearing (`clear_moved_heap_source`) must
   zero the descriptor at the call site, exactly like the tuple call path.

Tests (new file `crates/memobits-cli/tests/d2_owned_struct_transport.rs`,
mirror `tuple_nested_arrays.rs` helpers):
- positive source + standalone Wasm: pass a heap String struct by move, callee
  reads length via `borrow` and drops it; caller continues; literal-field and
  heap-field variants;
- capped-memory stress (normal and early return in caller and callee, 8,192
  iterations on one instance, as in `tuple_destructure_memory_stress.rs`);
- negative: use after move (TE0xx from ownership), direct temporary
  `take(Label { text: x })` stays LE900 ("must move directly from a named
  local"), non-String-owning flat struct unaffected, owned result still LE900,
  exported signature still LE900.
Guide: add a small checked function to `examples/projects/language-guide`.
Update the stale cases in `wasm_gates_unsupported_string_struct_uses`
(`crates/memobits-cli/tests/cli.rs:2554-2557`: `take(label: Label)` case).

### Slice 2: owned result of a flat String-owning nominal struct

Same predicate for the result clause of G-A (`:424-426`). Callee: `return
local` is a consuming move; `direct_string_tuple_return` already tolerates it
and `Return` at `memobits-ir/src/lib.rs:3816-3825` (`tuple_move`) must be
generalized from `tuple_owns_string` to the nominal predicate. Caller: the call
result must bind directly to a new local (`let l := make();`), the same
"direct new local binding" shape as tuple results; a call result used as a
temporary field/argument stays rejected (TE018/LE900 as today). Tests: result
bound and read; result discarded by scope exit releases once; early return
between call and use; stress with allocation inside the callee before return;
negatives: result stored to a field/array element, result used as a bare
temporary receiver, `var` reassignment.

### Slice 3: owned struct transported inside `Option`/`Result`-free containers (struct in array/tuple)

Admit a flat String-owning nominal struct as (a) a tuple element and (b) a
fixed-array element, reusing the type-directed cleanup that already scales with
type depth for arrays of String-owning tuples. Gates, in order:
1. `member_layout`/`type_layout` G-D (`:1062-1070`, `:1285-1290`): replace
   `is_tuple_definition`/`layout.is_tuple` by "flat String owner"; keep the
   nested-struct-in-struct rejection.
2. Analysis: `supported_nested_string_tuple` (`lower.rs:579`) and
   `contains_string_owner`/`tuple_has_unsupported_nested_string_owner`
   (`types.rs:1270-1330`) to accept nominal flat owners.
3. IR: `feeds_owned_array_element` (`lib.rs:3405-3425`) is generic; the
   array-literal construction path and `scoped_string::array_binding` (:913)
   need a test per placement. `ArrayNew` repeat form (`[Label{..}; N]`) must stay
   rejected (copy of owner); only element lists with distinct moved sources.
Tests: array of two labels with heap fields built from named locals, read via
index borrow (`a[0].text.len()`); drop on normal/early return; stress 8,192
iterations; negative: `[l; 3]` repeat of an owner, array element move-out
(see slice 5 blocker).

### Slice 4: String-owning nominal struct nested in a nominal struct, and in an enum payload

Order matters; each step lifts one gate and adds one test file:
1. Layout G-C (`:1110-1121`): allow `Struct` fields whose type is itself a
   flat String-owning struct; keep a visited-set so recursive types stay out.
2. G-D struct-in-struct branch of `member_layout` (`:1066-1070`).
3. G-E `type_owns_string_storage` (`:494-523`): drop the `!is_tuple` restriction
   so ownership roots recurse.
4. Cleanup: `emit_string_storage_cleanup` (:2907) must descend into the nested
   struct (offset arithmetic by field layout); `max_string_array_depth` (:2871)
   gives the callee scratch-local count per nested depth. Verify the same code
   path is already taken for tuple-in-tuple (it is: nested tuple tests exist).
5. Enum payload: add a flat String-owning struct as a payload via
   `scoped_string::enum_variant_owns_string_storage` (generic) and the
   `EnumNew` payload ownership check (`lib.rs:~3612`), which currently has a
   String-and-tuple special case.
6. Move-in only: `Outer { inner: label }` from a named local through
   `nested_tuple_move`-style rule generalized (`lib.rs:3606-3625`).
Negative: `Outer { inner: Label {..} }` direct literal stays rejected until
slice 4 explicitly lifts it; inherited-Error String structs stay rejected
(`:1112`).

### Slice 5 (BLOCKER, not designed): consuming `match`/read of heap payloads from nested storage

Reading a `String` or String-owning aggregate out of a struct field, array
element, or enum payload held in nested storage by value (`let s := outer.inner.text`,
`match arr[0] { Wrapped(text) => .. }` moving `text` out) requires either
(a) an implicit partial move out of a still-live owner (the owner would be left
with a hole whose cleanup must be tracked per field), or (b) a whole-heap
reference escape (a loan on a heap payload that outlives the match arm). Both
are excluded by `implementation-requirements.md` ("New ownership-bearing
shapes ... if a narrow exact option still needs reference escape, implicit
partial moves, whole heap transport ... Keep those operations rejected until
proven"). Evidence that the IR already treats it as a hard boundary:
`VariantExtract` of a heap payload is now rejected locally for borrowed, field
and array-element sources (WP6), TE018 "String enum payloads require a
consuming match" (`memobits-ir/src/lib.rs:2467`, `:2683`), and the Extract
contract at `lib.rs:427-433` only allows whole-value extraction of an owner
consumed in the same block. Possible narrow options for the architect to decide
(none implemented): (i) consuming `match` of a whole *local* enum only (already
supported), (ii) explicit swap/replace-with-default API for a field/element
(needs a default heap value; outside D2), (iii) destructuring of the whole
nested owner into locals (already works for tuples, see `bind_tuple_patterns`).
Recommended resolution: keep D2 acceptance at (i) and (iii); record (ii) as a
post-launch row. Question for the architect: confirm that D2 is accepted
without partial moves out of nested storage.

### Architect decisions on the proposal (2026-11-23)

- Phase 2a ACCEPTED: workspace 1,137 passed / 0 failed
  (`logs/wp6-workspace-test.log`), guide source + Wasm `Result: Ok(i32(42))`.
- Proposal ACCEPTED with slices 1–4 in the given order.
- **Slice 5 decision:** D2 is accepted without partial moves out of nested
  storage. Narrow options (i) consuming match of a whole local enum and (iii)
  whole-owner destructuring are the supported paths. Option (ii)
  (swap/replace API) is recorded as a post-launch candidate, not D2 work. All
  nested move-out forms stay rejected and must keep negative tests. This
  follows the requirements' own scope note (partial destructuring is outside
  the D2 acceptance row); the user may override.
- Mandatory constraint for slices 1–4: introduce ONE shared predicate for
  "String-owning aggregate admitted for transport" (in `memobits-ir`, reused by
  analysis and Wasm) instead of editing each `"\0tuple"` check ad hoc. Line
  `memobits-wasm/src/lib.rs:4526-4531` (moved-source clearing) must switch to
  it in slice 1.
- Phase 2b = slice 1 then slice 2, sequentially. Stop after slice 2 for
  architect review. Slices 3–4 are phase 2c.
- Follow-up from WP6 risk: add one probe test where a borrowed heap-payload
  enum crosses a block boundary (e.g. via `if`/`else` join) before extraction;
  if only TE018 catches it, record it — do not redesign now.

### Ordered slice list and dependencies

1. Slice 1: owned flat nominal struct argument (G-A param clause, G-B).
2. Slice 2: owned flat nominal struct result (G-A result clause, IR `Return`).
3. Slice 3: flat nominal struct as tuple element / fixed-array element (G-D).
4. Slice 4: nested nominal String structs and enum payload structs (G-C, G-D, G-E).
5. Slice 5: BLOCKER, needs architect decision (no design).
Each slice ships with its own positive source+Wasm test, capped-memory stress
(normal and early return, repeated on one instance), at least three negative
tests that name the still-rejected neighbours, a guide example, and the full
workspace run. Slices 1-2 are independent of 3-4. Risks: (a) the five tuple-keyed
gates are duplicated across crates and must change together per slice, with a
predicate shared via `memobits-ir` rather than re-derived; (b) the Wasm
`owned_string_tuple` check at `:4526-4531` is the one place still keyed on the
tuple module and must be generalized in slice 1 or the moved-source clearing
silently skips nominal structs (leak/double free risk: stress tests are
mandatory); (c) `wasm_gates_unsupported_string_struct_uses` currently pins
the LE900 messages, so each slice must edit exactly its own cases.

## Queued after phase 2b review (architect, 2026-11-23)

User approved the architect's recommendations. Decisions are recorded in
`docs/design/decisions.md` ("Ownership direction after the D2 aggregate
work"): composition allowed by default via one shared predicate; references
stay second-class; no implicit partial moves (explicit replace/swap instead);
`Array<T, N>` is the target spelling and `array(T; N)` is withdrawn;
String-owning anonymous records go through the same predicate.

### WP10 — Documentation consistency fixes (Haiku, no Cargo, after 2b)

Exact edits, each verified by grep afterwards:
1. Guide `examples/projects/language-guide/src/main.mb` (~line 250): the
   comment "Reference-bearing payloads are rejected, and Wasm String payload
   storage remains unsupported." → "Reference-bearing payloads are rejected;
   String payloads are supported (see the enum-array example)."
2. `implementation-requirements.md` D1 "Preparation status" paragraph and D1
   manifest row: replace "Wasm String payload storage remains unsupported" /
   "Payload reference and Wasm String-storage gates remain enforced" with text
   saying reference payloads stay rejected and String payloads are supported
   through D2 type-directed cleanup.
3. `implementation-requirements.md` line "Scope discrepancy to reconcile ..."
   (operator matrix): delete it — matrix row 92 already records `u32 &=`,
   `|=`, `^=`, `<<=`, `>>=` as enabled, so the discrepancy is resolved.
4. `implementation-requirements.md` "Routine defaults": "Recommend
   `array(T; N)` over the existing fixed-array representation" → "Keep
   `Array<T, N>` as the target spelling (decision 2026-11-23)".
Guide edit is comment-only; still rerun guide source + Wasm (Cargo lock).

### WP11 — Inventory refresh (Haiku, no Cargo, can run now)

See the explicit edit list given in the dispatching prompt; status changes
only, no new features.

### WP12 — `mb check` command (Sonnet, small)

`mb check [--project path]` runs parse/resolve/analysis/ownership/IR
validation and the Wasm layout gates without writing an artifact; exit 0 on
success, same diagnostics as `build`. CLI test: success, a type error, an
LE900 gate error, and no `target/` artifact written. README/CLI help update.
Inventory TOOL-01 updated to Shipped for `check`.

### Phase 2c — slices 3–4 + anonymous records

Slices 3 and 4 of the proposal, plus String-owning anonymous records admitted
through the same shared predicate (positive source/Wasm, capped stress,
negatives). Stop for architect review after each slice.

## Roadmap after launch (architect recommendation, approved)

1. Finish launch rows: D2 (2b/2c), D3, C1, remaining M1/I1/G1/G2/OP1/H1.
2. Ownership model: general owned-element model (`Array<String>`, `List<T>`
   for all element types, non-empty list literals, `list[i]`), explicit
   replace/swap, aggregate `.copy()` for primitive-only aggregates.
3. Ergonomics: `try … else`, ranges with `loop i in 0..n`, string
   interpolation (basic types), compile-time `const`, `checked_*` /
   `saturating_*` and all-width bitwise/signed arithmetic shift, nested and
   literal patterns then guards, `~`, `Self` in extensions.
4. Abstraction: non-capturing function values, then move-capturing closures;
   multiple generic parameters/bounds; owned `Box<T>`.
5. Outside world: WIT / Component Model canonical ABI for exports and host
   capabilities, packages, formatter then LSP.
Not planned: overloading, `**`/`++`, properties/getters, `loop when`/`after`,
named lifetimes, tasks/parallelism, panic hook (revisit only with a concrete
consumer).

## Phase 2b status — ACCEPTED by architect (2026-11-23)

Verified: workspace 1,146 passed / 0 failed (`logs/wp9-workspace-test.log`),
guide source + Wasm `Result: Ok(i32(42))`. Shared predicate
`is_string_owner_transport` (memobits-ir `scoped_string.rs`) covers String-owning
tuples and flat nominal String structs; owned arguments (named local only) and
owned results (direct new local binding) work with capped stress and
mutation-checked leak/double-release coverage. WP11 inventory refresh done.
Follow-ups carried into the next run:
- IR diagnostics that say "heap String tuple ..." also fire for nominal
  structs; reword to "String-owning aggregate" (update test expectations).
- The generalized Extract clearing for nominal structs is unreachable today
  (TE022 blocks field move-out); keep it, note it, add coverage when
  slice 3/4 makes it reachable.

## WP10/WP12/slice 3 status — ACCEPTED by architect (2026-11-23)

Verified: workspace 1,150 (after WP10/12) then 1,153 passed / 0 failed
(`logs/wp13-workspace-test.log`); guide source + Wasm `Result: Ok(i32(42))`.
`mb check` shipped. Flat String-owning nominal structs work as tuple and
fixed-array elements. Architect decisions on the contractor's questions:
- Tuple temporaries holding owners (`(make(), 1)`, inline struct) stay
  accepted: same staging as tuple-of-tuple, covered by capped stress.
- `Array<Array<Label,N>,M>` construction/release stays accepted. The element
  read limit (`grid[i][j].borrow()` → LE900) predates slice 3 and is deferred
  to roadmap stage 2 (general element borrows); do not gate construction.

## Phase 2c run 2 — slice 4 + anonymous records + D2 reconciliation

Slice 4 per proposal (struct-in-struct, flat owner in enum payload, owner
arrays inside struct/tuple/enum payload) through the shared predicate, then
String-owning anonymous records through the same predicate, then a written D2
acceptance reconciliation against the manifest row.

## D2 acceptance reconciliation

Written by the contractor (2026-11-23). Each clause of the D2 manifest row in
`implementation-requirements.md` is quoted and mapped to the test that proves it
(`crates/memobits-cli/tests/<file>::<test>`), or marked MISSING. The contractor
does not mark D2 complete; the architect decides.

Manifest row, quoted:
> D2 | Ordered tuples in arguments, results, struct fields, enum payloads and
> nested aggregates, plus labels as projection sugar and complete labeled
> initialization. Depends on core aggregate layout and ownership checks. | Same
> storage via label and ordinal, order-sensitive type identity, written-order
> initialization despite reordering, and exact move/drop for admitted owning
> elements. Reject duplicate, missing or unknown labels and unsupported loans.
> Internal signatures only.

| Clause | Evidence | Status |
|---|---|---|
| "Ordered tuples in arguments, results" | `cli.rs::tuples_preserve_order_across_internal_arguments_results_and_projections` (scalar); `cli.rs::owned_string_tuples_move_through_internal_calls_and_returns` and `tuple_owned_temporaries.rs::temporary_owned_string_tuple_transfers_to_call_and_cleans_on_later_exit` (String-owning) | covered |
| "struct fields" | `cli.rs::tuples_nest_in_struct_fields_and_enum_payloads` (scalar); `tuple_owned_temporaries.rs::string_owning_tuple_field_in_local_nominal_record_cleans_in_source_and_wasm` (String-owning) | covered |
| "enum payloads" | `cli.rs::tuples_nest_in_struct_fields_and_enum_payloads` (scalar); `tuple_owned_temporaries.rs::string_owning_tuple_enum_payload_moves_and_cleans_on_normal_and_early_returns`; `tuple_nested_arrays.rs::enum_arrays_clean_active_tuple_and_nested_array_payloads` | covered |
| "nested aggregates" | `tuple_nested_arrays.rs::tuples_compose_with_fixed_arrays_in_both_aggregate_directions`; `tuple_nested_arrays.rs::string_owning_tuple_arrays_transfer_through_owned_calls`; `cli.rs::nested_tuple_identity_ignores_occurrence_local_labels_in_source_and_wasm`; `tuple_owned_temporaries.rs::nested_string_tuples_move_through_temporary_calls_and_destructure_in_source_and_wasm` | covered |
| "labels as projection sugar" | `cli.rs::tuple_labels_are_occurrence_local_independently_of_function_order`; `cli.rs::labeled_tuple_initializer_reorders_written_values_to_local_alias_slots` | covered |
| "complete labeled initialization" | `cli.rs::labeled_tuple_initializer_reorders_written_values_to_local_alias_slots`; rejection of mixed labeled/positional initializers in `cli.rs::labeled_tuple_malformed_forms_are_rejected` | covered |
| "Same storage via label and ordinal" | `d2_tuple_acceptance.rs::tuple_label_and_ordinal_address_the_same_storage_in_source_and_wasm` (reads and writes one tuple through `.left`/`.0` and `.right`/`.1`; source and standalone Wasm agree) | covered (WP16) |
| "order-sensitive type identity" | `cli.rs::tuple_element_order_is_checked_by_type`; TE002 half of `cli.rs::nested_tuple_identity_ignores_occurrence_local_labels_in_source_and_wasm` | covered |
| "written-order initialization despite reordering" | Tuples: `d2_tuple_acceptance.rs::labeled_tuple_initializers_evaluate_in_written_order_in_source_and_wasm` (effects written right-then-left, slots left=2/right=1, source and Wasm agree). Anonymous records: `d1_anonymous_shapes.rs::anonymous_records_and_contextual_inline_enum_variants_run_in_source_and_wasm`. | covered (WP16) |
| "exact move/drop for admitted owning elements" | `tuple_destructure_memory_stress.rs` (all stress tests, 8,192 iterations under a capped memory), `cli.rs::tuple_destructuring_moves_owned_elements_in_source_and_wasm`, `cli.rs::owned_string_tuple_transport_rejects_use_after_move_and_nominal_structs`, `cli.rs::later_argument_early_return_cleans_staged_owned_tuple`, `d2_owner_placement.rs::repeated_string_owner_elements_release_on_normal_and_early_returns`, `d2_nested_owner_transport.rs::repeated_nested_string_owners_release_on_normal_and_early_returns`, `d2_record_owner_transport.rs::repeated_string_owning_records_release_on_normal_and_early_returns` | covered |
| "Reject duplicate ... labels" | `cli.rs::labeled_tuple_malformed_forms_are_rejected` (duplicate in initializer and in type) | covered |
| "Reject ... unknown labels" | `cli.rs::labeled_tuple_malformed_forms_are_rejected` (`first/second` against `left/right`) | covered |
| "Reject ... missing labels" | `d2_tuple_acceptance.rs::labeled_tuple_missing_label_is_rejected` (`(left: 1,)` against `(left, right)`: TE002 "tuple arity does not match its expected type"); also the mixed-form and differing-label cases in `cli.rs::labeled_tuple_malformed_forms_are_rejected` | covered (WP16) |
| "unsupported loans" | `cli.rs::tuple_reference_elements_are_gated_before_ir_validation`; `cli.rs::tuple_nested_option_reference_is_gated_before_owner_can_escape`; `tuple_nested_arrays.rs::tuple_array_elements_keep_reference_and_list_gates` | covered |
| "Internal signatures only" | `d2_tuple_acceptance.rs::tuple_exported_signatures_stay_rejected` (tuple parameter and labeled tuple result in `build --lib`: LE900 "exported signatures cannot take/return structs"); generic gate also in `d2_owned_struct_transport.rs::owned_string_struct_exported_signatures_and_plain_structs_are_unchanged`, `d2_nested_owner_transport.rs::nested_string_owner_exported_signatures_stay_rejected`, `d2_record_owner_transport.rs::string_owning_record_exported_signatures_stay_rejected` | covered (WP16) |

WP16 update: all four items below now have tests (`crates/memobits-cli/tests/d2_tuple_acceptance.rs`, 4/4 pass, `logs/wp16-d2-tuple-acceptance.log`); no MISSING row remains. Closure is the architect's decision. Original summary: (1) same storage through label and ordinal on one
tuple value, (2) written-order side-effect test for labeled tuple initializers,
(3) dedicated missing-label rejection case, (4) tuple-specific exported
signature rejection. Probes with `mb run` (not committed as tests): items (1) and (2) already
behave correctly (`(left: 40, right: 2)` read as `p.left + p.1` gives 42;
side-effecting initializers written right-then-left evaluate in written order),
so they need tests, not compiler changes. For (3), `take((left: 1,))` against `(left: i32, right: i32)` is
rejected with TE002 "tuple arity does not match its expected type" (`(left: 1)`
without the comma is SE002), so it needs a test only. (4) was not probed.
Not part of the manifest and unchanged: partial destructuring and labeled
destructuring aliases.

## Slice 4 + anonymous records — ACCEPTED by architect (2026-11-23)

Verified: workspace 1,161 passed / 0 failed (`logs/wp15-workspace-test.log`),
guide source + Wasm `Result: Ok(i32(42))`. Recursive owner predicate admits
nested owner structs, owner arrays in fields, owners as enum payloads, and
String-owning anonymous records. Decisions on contractor questions:
- Struct-literal field owners staged into hidden locals: ACCEPTED (same
  mechanism as tuple elements, principle A). Direct temporaries as owned call
  arguments remain rejected for now; revisit with roadmap stage 2.
- Element reads through field-held arrays (`bag.items[0].borrow()`): deferred
  to roadmap stage 2 with the other element-borrow limits.
- The Error-ancestry negative now reports the generic LE900 nesting message;
  acceptable, but a dedicated message is a nice-to-have.

## Next run — D2 closure + D3

1. D2 MISSING tests from the reconciliation: label+ordinal same storage,
   tuple written-order labeled initialization with effects, missing-label
   rejection, tuple-specific exported-signature rejection. Then update the
   reconciliation table (no MISSING left) — architect decides closure.
2. D3 per decision "Optional spelling migration" in docs/design/decisions.md:
   non-failing warning channel (CLI prints warnings; exit status unchanged),
   migration warning for legacy `Option<T>`, migrate guide/maintained fixtures
   to `T?` (not protected examples). Then a "D3 acceptance reconciliation"
   table against the D3 manifest row (distinct `(borrow T)?` vs `borrow T?`
   parse/type forms, no expanded reference transport, contextual None, Some
   evaluated once, matching, type errors, legacy migration diagnostics) with
   test citations or MISSING, and add tests for any MISSING item.

## D3 acceptance reconciliation

Written by the contractor (WP17, 2026-11-23). D3 manifest row, quoted:
> D3 | `T?` type spelling, grouping, then `None` and `Some`. Reuse current outcome
> machinery before expanding construction. | Distinct parse/type forms for
> `(borrow T)?` and `borrow T?`; no expanded reference transport. Tests for
> contextual None, Some evaluated once, matching, type errors, and legacy
> migration diagnostics.

Paths are `crates/memobits-cli/tests/<file>::<test>` unless noted.

| Clause | Evidence | Status |
|---|---|---|
| "`T?` type spelling" | `cli.rs::postfix_optional_type_runs_in_source_and_wasm` | covered |
| "reuse current outcome machinery" (`T?` is the same type as `Option<T>`) | `d3_optional_warnings.rs::postfix_and_legacy_spellings_are_the_same_type`; syntax `parser.rs::postfix_optional_type_preserves_grouped_reference_precedence` (both lower to path `Option`) | covered (WP17) |
| "Distinct parse forms for `(borrow T)?` and `borrow T?`" | `memobits-syntax/tests/parser.rs::postfix_optional_type_preserves_grouped_reference_precedence` (AST shapes) | covered |
| "Distinct ... type forms" | `cli.rs::postfix_optional_reference_grouping_keeps_current_transport_gate` (`borrow i32?` accepted, `(borrow i32)?` rejected TE017 in a signature); `d3_optional_warnings.rs::postfix_optional_spelling_produces_no_warning` (grouped form never warns) | covered |
| "no expanded reference transport" | same gate test; `memobits-analysis/tests/outcomes.rs::local_borrow_option_unsupported_transports_are_gated`, `ir_rejects_escaping_or_nonconsuming_borrow_option_transport`; `cli.rs::tuple_nested_option_reference_is_gated_before_owner_can_escape` | covered |
| "contextual None" | `cli.rs::postfix_optional_type_runs_in_source_and_wasm` (annotated); `d3_optional_warnings.rs::contextual_none_and_matching_work_through_calls_and_returns_in_source_and_wasm` (argument and return contexts, source + Wasm) | covered (WP17) |
| "Some evaluated once" | `cli.rs::postfix_optional_some_evaluates_its_payload_once_in_source_and_wasm`; `cli.rs::inferred_options_execute_payload_once_in_source_and_artifact` | covered |
| "matching" | `cli.rs::postfix_optional_type_runs_in_source_and_wasm`; `d3_optional_warnings.rs::contextual_none_and_matching_...`; `cli.rs::option_some_value_roundtrips_through_match` | covered |
| "type errors" | `cli.rs::postfix_optional_type_rejects_mismatched_and_uninferred_values` (`Some(true)` for `i32?`, context-free None); `d3_optional_warnings.rs::postfix_optional_type_errors_are_reported` (`Some(1)` for `Bool?`, context-free None, `take(true)` for `i32?`); `cli.rs::unresolved_none_preserves_previous_artifact` | covered |
| "legacy migration diagnostics" | Originally WP17 MW001 tests; MW001 removed. `d3_optional_warnings.rs::option_spelling_is_silent_on_check_build_and_run` now asserts no warning | WAIVED by user decision 2026-11-23 |

No MISSING row remains. Warning channel design: the parser records `MW001`
warnings in `ParseResult.warnings` (separate from `diagnostics`, so no existing
`diagnostics.is_empty()` check changes); `Resolution.warnings` aggregates them;
the CLI prints them to stderr with the shared renderer right after parsing, before
any error. Limits to note: warnings are only reported for source that is parsed
(unreachable modules are not), `mb run FILE.wasm` has no source, and `Option`
written as a path segment other than the type spelling is not warned.
Logs: `logs/wp17-d3-optional-warnings.log` (9/9), `logs/wp17-workspace-test.log`
(1,174 passed, 0 failed, before the 9th D3 test was added; D3 file rerun 9/9),
guide: `logs/wp17-guide-run.log`, `logs/wp17-guide-wasm-run.log`
(`Result: Ok(i32(42))`, no warnings). Closure is the architect's decision.

## D2 and D3 — ACCEPTED by architect (2026-11-23)

Architect re-ran the final state: `cargo test -j1 --workspace --no-fail-fast
-- --test-threads=1` → 1,175 passed / 0 failed
(`logs/arch-verify-d3-workspace.log`); guide source + standalone Wasm
`Result: Ok(i32(42))` with empty stderr. Both reconciliation tables have no
MISSING rows. D2 and D3 are accepted as complete for the launch manifest,
pending commit packaging (not done; user has not asked for commits).
Warning code prefix `MW` accepted.

## Next run — C1

Per docs/design/decisions.md "Text traversal and spelling migration":
1. `loop ch in text` scalar traversal yielding `Char` (source + Wasm), with
   ASCII, multibyte, supplementary-plane and empty-string cases compared to
   `.len()` byte length; loop loan conflicts (mutation of the text inside the
   loop rejected); early break/return cleanup with heap strings.
2. Migration warnings MW002 (`String` → `string`) and MW003 (`Bytes<N>` →
   `Array<u8, N>`); migrate guide + maintained fixtures; protected examples
   untouched.
3. "C1 acceptance reconciliation" table against the C1 manifest row with test
   citations or MISSING; close MISSING with tests.

## C1 acceptance reconciliation

Manifest row: "Array shape/length checks and nesting; invalid
scalar/surrogate/multi-scalar char rejection; exact ASCII, supplementary and
multibyte traversal versus byte length; retained cleanup. Migrate maintained
guide/fixtures without touching protected dirty examples. Document
compatibility and avoid allocator changes. Bytes is outside the target core."
(`c1` = `memobits-cli/tests/c1_text_traversal.rs`.)

| Clause | Evidence | Status |
| --- | --- | --- |
| Array shape/length checks | `memobits-analysis/tests/types.rs::fixed_arrays_reject_incompatible_elements_lengths_and_ranges`; `types.rs::fixed_bytes_use_array_length_and_element_rules`; `array_calls.rs::array_type_mismatches_between_argument_and_parameter_are_type_errors`; `memobits-wasm/tests/arrays.rs::oversized_or_overflowing_array_layouts_are_diagnostics` | covered |
| Array nesting | `memobits-analysis/tests/nesting.rs::{nested_reads_chain_field_and_element_addresses, array_of_struct_forms_are_accepted, recursive_containment_through_arrays_is_te026}`; `memobits-cli/tests/nesting_cli.rs::{a_particle_system_mutates_nested_arrays_and_sums_through_a_borrow, zero_length_arrays_of_structs_and_per_element_repetition}`; `tuple_nested_arrays.rs` | covered |
| Invalid scalar / surrogate / multi-scalar char rejection | `memobits-syntax/tests/parser.rs::malformed_character_literals_report_scalar_errors_and_recover` (empty, `'ab'`, newline, bad escape, `'\u{D800}'`); `memobits-ir/tests/validation.rs::rejects_non_scalar_char_constants` (55296, 1114112); `cli.rs::char_and_u32_are_distinct_scalar_types`; `c1::traversal_loan_and_binding_negatives` (Char is not u32, no ordering) | covered |
| Exact ASCII traversal vs byte length | `c1::scalar_traversal_counts_scalars_not_bytes` ("", "hello"), `c1::scalar_traversal_binds_exact_chars_in_order` | covered (source + Wasm) |
| Multibyte (2/3-byte) and supplementary (4-byte) traversal vs byte length | `c1::scalar_traversal_counts_scalars_not_bytes` (é 1/2, € 1/3, 😀 1/4, mixed 5 scalars/11 bytes), `c1::scalar_traversal_agrees_with_scalar_at_byte_offsets`, `c1::nested_traversal_and_break_continue_with_borrowed_text`, `cli.rs::scalar_traversal_counts_scalars_separately_from_utf8_bytes_in_source_and_wasm` (manual loop) | covered |
| Retained cleanup | `c1::early_exits_with_heap_text_release_it_under_a_capped_wasm_memory` (8,192 iterations of 4 KiB heap text with return/continue/break inside the loop, one extra page); `c1::text_is_still_usable_after_the_loop_and_receiver_is_evaluated_once`; loan negatives in `c1::traversal_loan_and_binding_negatives` | covered |
| Maintained guide migrated, protected examples untouched | `c1::language_guide_uses_current_spellings_and_runs_with_empty_stderr` (no `String`/`Bytes<` outside comments, empty stderr in source and standalone Wasm); `cli.rs::language_guide_checks_bytes_array_equivalence_in_source_and_wasm`; no maintained test fixture asserts empty stderr with a legacy spelling (full run passes unmodified); only `examples/projects/language-guide/src/main.mb` changed under `examples/` | covered |
| Documented compatibility | `crates/memobits-cli/README.md` MW002/MW003 rows; `docs/design/decisions.md` "Shipped C1 receiver rules"; guide comments above `count_wide`; warnings tested by `memobits-syntax/tests/migration_warnings.rs::legacy_string_and_bytes_spellings_warn_and_current_spellings_do_not`, `c1::legacy_string_and_bytes_spellings_warn_without_failing` (exit 0, check/build/run), `c1::current_spellings_produce_no_warnings`, `c1::legacy_spelling_warnings_do_not_hide_errors`, `structs.rs::uppercase_string_is_a_compatibility_spelling_but_qualified_paths_are_rejected` | covered |
| No allocator changes | Review: edits are limited to syntax, analysis, IR, ownership and `memobits-wasm/src/lib.rs` instruction emission; `string_heap.rs`, `memory.rs`, `string_descriptor.rs`, `list_descriptor.rs` and `utf8.rs` are untouched. Behavior: the capped-memory test above passes with the unchanged allocator | covered (review, no dedicated test) |
| Bytes outside the target core | `types.rs::fixed_bytes_use_array_length_and_element_rules` (alias of `Array<u8,N>`), `c1::legacy_string_and_bytes_spellings_warn_without_failing` (MW003 on `Bytes<N>`), `cli.rs::language_guide_checks_bytes_array_equivalence_in_source_and_wasm` | covered |

No MISSING row remains. Decision to flag: bare `String` had been rejected with
TE001 (HEAD) although the accepted decision says legacy spellings stay accepted
with warnings; it is accepted again with identical meaning and MW002, and the
old rejection test was rewritten (qualified `m::String` still rejected).
Not covered by C1: traversal of fields, call results and literals, general
iterator protocol, slicing. Other maintained examples (`hashing`,
`utf8-validator`, `strings`) use legacy spellings and now print warnings.

## C1 — ACCEPTED except one correction (architect, 2026-11-23)

Verified: workspace 1,187 passed / 0 failed (`logs/wp18-workspace-test.log`);
guide source + Wasm `Result: Ok(i32(42))`, empty stderr. `loop ch in text`
and MW003 accepted.

CORRECTION (architect error): the committed accepted decision (HEAD
`docs/design/decisions.md`) is "The only source type spelling is lowercase
`string`", and bare `String` was rejected with TE001 + migration guidance.
The architect's C1 note wrongly called `String` a compatibility spelling and
the contractor followed it. `docs/design/decisions.md` has been corrected by
the architect. Code must be restored: bare `String` → TE001 with the original
guidance; MW002 removed. `Bytes<N>` + MW003 stays.

## Next run — String restore + remaining-row reconciliation

1. Restore the String rejection (see correction above) and verify.
2. Read-only reconciliation (no code) for M1, I1, G1, G2, OP1, H1 and D1:
   per row, quote each acceptance clause from the manifest and cite
   test file::name or MISSING, plus a one-line effort estimate per MISSING.

## Reconciliation of M1, I1, G1, G2, OP1, H1, D1 (WP19, read-only, contractor)

Method: clauses are quoted from the "Full launch manifest" acceptance column
(and the "Operator contract matrix" for OP1); tests were located by grep over
`crates/*/tests` and in-crate `#[cfg(test)]`, and test bodies were spot-read
for the clauses marked with a note. Nothing here was executed (the one
workspace run of this WP is the String-restore verification). `cli` =
`crates/memobits-cli/tests/cli.rs`, `gce` = `.../generic_const_evidence_cli.rs`,
`d1c` = `.../d1_anonymous_shapes.rs`, `roots` = `memobits-resolve/tests/roots.rs`.
Effort: S under a day-part, M a focused slice, L multi-slice. "Decision" = needs
user/language decision.

### M1 acceptance reconciliation

| Clause | Evidence | Status |
| --- | --- | --- |
| "Behavior-preserving compiler extraction ... with array, List and operations responsibilities separated in private modules" | Files exist and are private `mod`s: `memobits-analysis/src/types/{arrays,lists,operations}.rs`, `lower/{arrays,operations}.rs`, `memobits-wasm/src/{arrays,operations}.rs`, `memobits-syntax/src/items.rs`. Review only; no test asserts structure | covered (review) |
| "Rust-owned minimal portable core" | `roots::compiler_owned_core_module_path_cannot_be_redeclared`; `cli::user_defined_add_selects_core_ops_interface_in_source_and_wasm` (virtual `core::ops`) | covered (partial: only `core::ops` exists) |
| "Existing compiler entry points stay authoritative" | whole suite drives the public entry points; no API-surface test | covered (indirect) |
| "Focused before/after diagnostic and execution equivalence" | none dedicated; launch-progress "M1 extraction checkpoint" lists suite runs only. No recorded HEAD-vs-WIP diagnostic/output comparison | MISSING: S/M (script compares `mb check/run` output of the example set and a diagnostics corpus between HEAD worktree build and current; read-only, but needs a second build). Decision: no (architect may accept the green suite as the oracle) |
| "No new dependencies solely for organization" | `git status` shows no `Cargo.toml`/`Cargo.lock` modified | covered (git evidence) |
| "no disconnected production TODO paths" | grep `todo!\|unimplemented!\|TODO\|FIXME` over `crates/*/src` returns nothing | covered (grep evidence) |
| "no graph-wide formatting churn" | `cargo fmt --all -- --check` and `git diff --check` logged in the M1 checkpoint; not re-run in this WP | covered (process; re-run at final) |
| "Backend keeps source decisions out of Wasm encoding" | none; `memobits-wasm/src/lib.rs` is still ~5.9k lines and `memobits-analysis/src/types.rs` ~6.9k lines, so the extraction is shallow | MISSING: M (review plus, if wanted, a small guard test or doc); Decision: no, but architect should say whether line-count depth is acceptable |

Clauses 8; MISSING 2.

### I1 acceptance reconciliation

| Clause | Evidence | Status |
| --- | --- | --- |
| "Interface/extend/pub, `fn draw(borrow self)`" | `parser.rs::parses_interface_and_borrowing_extension_methods`; `roots::extension_conformance_checks_receiver_mode_and_parameter_mutability`; `cli::explicit_interface_selector_resolves_a_unique_candidate` | covered |
| "postfix `point.draw() of graphics::Draw`" | `parser.rs::parses_explicit_interface_selection_on_a_call`; `cli::explicit_interface_selector_resolves_a_unique_candidate` (unqualified `of Draw` locally); `gce::generic_array_type_const_and_evidence_forward_through_nested_specializations` (qualified through `use common;`) | covered |
| "grouped selector chaining" | parse only (`parses_explicit_interface_selection_on_a_call` covers `(x.f() of I).g()`); no execution test of a grouped chain found by grep | closed WP20: `wp20_s_gaps::grouped_selector_chain_runs_in_source_and_wasm` |
| "scoped/grouped imports" | `parser.rs::grouped_symbol_imports_expand_to_individual_bindings`; cli fixtures using `use self::main::{Point, Draw}` (e.g. `interface-later-argument-loans`, ambiguity fixtures) | covered |
| "current prelude name support" | `roots::imported_and_prelude_annotations_require_types`; `roots::prelude_alias_cannot_hide_private_type_in_public_signature`; `cli::generic_specialization_keeps_declaring_module_imports_and_prelude_in_source_and_wasm` | covered |
| "Open extensions from independent packages at the semantic identity boundary" | `roots::extension_candidate_identity_includes_independent_package_name` | covered (identity only; loading out of scope per manifest) |
| "Implicit access only for receivers" | `cli::interface_selection_requires_a_receiver_method_call` | covered |
| "Unique selection" | `cli::explicit_interface_selector_resolves_a_unique_candidate` | covered |
| "all ambiguity locations" | `cli::explicit_interface_selection_reports_all_ambiguous_candidates`; `cli::imported_extensions_from_two_modules_are_ambiguous` | covered |
| "private/hidden/missing implementations" | `cli::explicit_interface_selection_reports_private_imported_extension`; `cli::explicit_interface_selection_reports_missing_implementation` | covered |
| "direct module vs grouped and individual symbol imports" | direct module: `roots::bare_module_import_is_a_direct_extension_edge_not_a_symbol_alias`, `cli::directly_imported_public_extension_runs_from_another_module`; symbol: `roots::symbol_import_loads_a_module_without_activating_it_as_an_extension_edge`, `cli::symbol_import_loads_but_does_not_activate_an_extension`. A grouped `use m::{A, B}` import not activating an extension has no dedicated test | closed WP20: `wp20_s_gaps::grouped_symbol_import_does_not_activate_an_extension` |
| "no transitive or prelude activation" | `roots::extension_candidates_follow_direct_module_edges_and_public_visibility` (transitive load and prelude alias see no candidates); inherent analogue `d1c::generic_nominal_method_visibility_rejects_symbol_transitive_and_private_extensions` | covered at resolver level; closed WP20: `wp20_s_gaps::transitive_and_prelude_references_do_not_activate_an_interface_extension` |
| "correct receiver modes" | `roots::extension_conformance_checks_receiver_mode_and_parameter_mutability`; `cli::borrowed_extension_receiver_remains_live_through_later_arguments` | covered |
| "later-argument loan conflicts" | `cli::extension_receiver_loans_reject_conflicting_later_argument_access` | covered |
| "Use a multi-module fixture" | `examples/projects/module-imports` + cli fixtures with several `src/*.mb` | covered |
| "separate package-identity tests" | `roots::extension_candidate_identity_includes_independent_package_name` | covered |

Clauses 16; MISSING 3 (one full, two partial), all S, no decision.

### G1 acceptance reconciliation

| Clause | Evidence | Status |
| --- | --- | --- |
| "Generic types, functions, const parameters and interface constraints" | `parser.rs::generic_function_type_and_const_parameter_syntax_parses`; `roots::generic_parameters_are_scoped_types_during_name_resolution` | covered |
| "Instantiate one generic struct ... at different types and lengths" | `cli::generic_nominal_structs_specialize_types_and_const_lengths_in_source_and_wasm`; `typetable.rs::generic_nominal_types_specialize_type_and_const_arguments_once` | covered |
| "... and enum at different types and lengths" | `cli::generic_nominal_enums_construct_and_match_contextual_instances` (`Maybe<i32>`/`<u32>`); `cli::generic_nominal_enums_substitute_const_array_payloads_in_source_and_wasm` (`Packet<1>`/`<3>`) | covered |
| "a generic function forwarding type, const and selected interface evidence through another generic" | `gce::generic_array_type_const_and_evidence_forward_through_nested_specializations` (`relay` -> `inspect`, `T`, `N`, `SelectIndex`) | covered (arrays only: `Array<T, N>` shape; other const forms gated) |
| "Two callers using the same concrete type but different allowed evidence must keep distinct selections" | `cli::generic_interface_evidence_specializations_keep_caller_selections_distinct`; same `gce` test (`left`/`right` modules); `cli::generic_heterogeneous_add_forwards_each_callers_selected_evidence` | covered |
| "Reject missing/ambiguous evidence" | `cli::generic_interface_evidence_rejects_missing_and_ambiguous_candidates` | covered |
| "mismatched types/const values" | `cli::generic_functions_reject_conflicting_types_and_preserve_owned_moves`; `cli::generic_array_function_rejects_conflicting_const_arguments`; `cli::generic_nominal_structs_reject_mismatched_and_missing_arguments`; `types.rs::generic_parameter_inference_uses_semantic_types_and_rejects_conflicts` | covered |
| "recursive by-value type layout" | `typetable.rs::generic_type_layout_cycles_and_unbounded_specialization_are_diagnosed` (`Node<T>`, `Grow<T>`); `structs.rs::recursive_structs_and_alias_cycles_are_diagnostics`; `enums.rs::recursion_by_value_is_the_recursive_type_diagnostic` | covered |
| "unbounded specialization with a diagnostic" | type-layout growth covered by the typetable test; generic inherent methods by `d1c::generic_nominal_method_specialization_limit_is_reported`. The 256-function cap in `types.rs` (about line 6484, "generic specialization limit exceeded") has no test | closed WP20: `wp20_s_gaps::generic_function_specialization_limit_is_reported` |
| "Support const lengths in admitted array shapes" | `cli::generic_functions_forward_array_type_and_const_arguments_in_source_and_wasm`; `cli::generic_nominal_enums_substitute_const_array_payloads_in_source_and_wasm` | covered |
| "Depends on I1 and core type identity" | evidence tests above run through I1 selection | covered |
| Not claimed by manifest but recorded as limits (launch-progress): multiple bounds, borrowed/compound generic parameters | gated with TE007 | info only |

Clauses 11; MISSING 1 (S, no decision).

### G2 acceptance reconciliation

| Clause | Evidence | Status |
| --- | --- | --- |
| "Associated `Rhs` and `Output` through the selected implementation" | `parser.rs::associated_type_declarations_and_bindings_parse_in_interface_extensions`; `roots::associated_type_bindings_are_required_and_substitute_method_signatures`; `cli::user_defined_add_selects_core_ops_interface_in_source_and_wasm` | covered |
| "including forwarding" | `cli::generic_heterogeneous_add_forwards_each_callers_selected_evidence`; `cli::generic_add_bound_dispatches_through_core_evidence` | covered |
| "Same-type owned Add is the pilot" | `cli::user_defined_add_selects_core_ops_interface_in_source_and_wasm`, `user_defined_add_consumes_both_owned_operands` | covered |
| "One distinct RHS and one distinct output case, both working under a generic constraint" | `cli::generic_heterogeneous_add_forwards_each_callers_selected_evidence`; `user_defined_{sub,mul,div,rem,bitand,bitor,bitxor,shl,shr}_supports_heterogeneous_generic_operands_in_source_and_wasm` (RHS and output both distinct types) | covered |
| "prove output identity in a typed caller" | the same tests bind `let result: Difference = subtract(...)`; `cli::heterogeneous_add_rejects_wrong_rhs_missing_bindings_and_unresolved_projection` exercises exact `Output` annotation | covered (no test with a deliberately wrong annotated `Output` type found; closed WP20: `wp20_s_gaps::wrong_annotated_output_type_is_rejected_directly_and_through_generics`) |
| "Reject missing or inconsistent associated bindings" | `cli::heterogeneous_add_rejects_wrong_rhs_missing_bindings_and_unresolved_projection` (ME005); `cli::user_defined_add_rejects_wrong_signature_and_ambiguous_evidence`; `roots::associated_type_bindings_are_required_and_substitute_method_signatures` (missing, duplicate, undeclared) | covered |
| "wrong RHS" | same cli test (TE007); `user_defined_{sub,mul,div,rem}_rejects_wrong_rhs_type` | covered |
| "unresolved associated projection" | same cli test (NE008, `T::Output` unresolved) | covered |

Clauses 8; MISSING 1 partial (S, no decision).

### OP1 acceptance reconciliation

Manifest clauses first, then the matrix rows.

| Clause | Evidence | Status |
| --- | --- | --- |
| "Exercise every required operator family in the matrix, integrating suitable operators through I1/G1/G2" | families below; generic forwarding in `cli::user_defined_*_supports_heterogeneous_generic_operands_*` and `gce` | covered |
| "Preserve all existing primitive behavior and built-in assignment" | `cli::u32_bitwise_and_shifts_match_source_and_standalone_wasm`; `gce::primitive_signed_shifts_are_rejected`; `gce::assignment_and_short_circuit_operators_resist_user_overloads`; `cli::user_defined_neg_evaluates_operand_once_and_primitive_negation_stays_builtin`; wasm arithmetic boundary tests (`checked_mul_division_negation_and_remainder_cover_boundaries`) | covered |
| "Include reviewed audit results for missing operators" | `interface-architecture-plan.md` "Audit disposition for the OP1 launch"; `launch-progress.md` "OP1 compound-assignment gate and operator audit disposition" and "OP1 final matrix reconciliation" | covered (docs; no test needed) |
| "Positive and negative cases per family" | see matrix rows | covered with gaps below |
| "exact left-to-right evaluations" | `user_defined_{bitand,bitor,bitxor,shl,shr}_evaluates_operands_left_to_right`; `gce::overloaded_sub_mul_div_rem_evaluate_operands_left_to_right_in_source_and_wasm`; equality/ordering order inside their cli tests; Add order via `user_defined_add_rhs_early_return_unwinds_staged_owned_operand` | covered |
| "once-only LHS place capture" | `cli::user_defined_*_assign_mutates_nominal_target_in_source_and_wasm`; `gce::generic_array_add_assign_captures_index_once_mutates_rhs_and_checks_loans`; `gce::generic_compound_families_order_index_before_rhs_and_skip_bounds_and_method_on_return` | covered |
| "loan/move/failure tests" | `user_defined_*_consumes_*_operands`, `*_rhs_early_return_unwinds_*`; compound loan tests in `gce::generic_compound_families_allow_disjoint_projected_index_loans`, `generic_array_add_assign_captures_index_once_mutates_rhs_and_checks_loans` | covered |
| "primitive regressions" | see "Preserve" row | covered |
| "A working Add alone fails this row" | all families shipped | covered |

| Matrix row | Evidence | Status |
| --- | --- | --- |
| Arithmetic `+ - * / %`: "Test each family and one heterogeneous case"; "No mixed-type primitive coercion"; "Primitive division and overflow remain checked" | `user_defined_{add,sub,mul,div,rem}_*` incl. heterogeneous tests and `_rejects_wrong_rhs_type`, `_rejects_missing_inactive_and_ambiguous_implementations`; primitive checked behaviour in wasm/analysis boundary tests (`types.rs::checks_calls_assignments_and_returns` and wasm `checked_mul_division_negation_and_remainder_cover_boundaries`) | covered; a mixed-type primitive coercion rejection test (`1u32 + 1i32`) not located by name: closed WP20: `wp20_s_gaps::mixed_type_primitive_arithmetic_is_not_coerced` |
| Bitwise `& \| ^` and shifts: "Each form selects once ... correct evidence and precedence"; "wrong RHS and ambiguous extensions"; "Primitive signed shifts remain gated" | `user_defined_{bitand,bitor,bitxor,shl,shr}_*`; `gce::overloaded_add_shift_and_bitand_equality_keep_operator_precedence`; `gce::primitive_signed_shifts_are_rejected` (i32 only) | covered; signed widths other than `i32` unverified (recorded limit): closed WP20: `wp20_s_gaps::signed_shifts_of_every_width_are_rejected` (i8/i16/i64 shifts and compounds) |
| Equality and ordering: "equal and unequal cases, ordered cases, receiver remains available, RHS follows normal move/copy rules, one evaluation in written order and Bool result rejection"; "Never infer ordering from equality" | `cli::user_defined_equality_borrows_receiver_and_runs_in_source_and_wasm`; `cli::user_defined_ordering_borrows_receiver_and_runs_in_source_and_wasm` (`<=`, `>=`, `!=`, BE001 move, Bool, TE007 selection); `c1::traversal_loan_and_binding_negatives` (Char has no ordering, primitive) | covered; "ordering is not inferred from `==`" is exercised only via the missing-implementation diagnostics inside the ordering test, no dedicated named test |
| Compound `+= -= *= /= %= &=` and remaining: "Exercise each family, mutation of a valid target, index capture once, live overlapping loan rejection, disjoint access and early RHS exit"; "Primitive `u32 &= \|= ^= <<= >>=` enabled with source/Wasm coverage" | all ten: `cli::user_defined_{add,sub,mul,div,rem,bitand,bitor,bitxor,shl,shr}_assign_mutates_nominal_target_in_source_and_wasm`; `gce::generic_compound_*` (disjoint loans, ordering, early return); overlapping live-loan rejection in `gce::generic_array_add_assign_captures_index_once_mutates_rhs_and_checks_loans`; primitive: guide plus `u32_bitwise_and_shifts_match_source_and_standalone_wasm` (does it cover all five compounds? verified WP20: `wp20_s_gaps::all_five_primitive_u32_compound_operators_match_source_and_wasm`) | covered; one verify item |
| Unary: "Verify user minus selection and existing signed-minimum rejection. Unary plus, integer complement, short circuit operators, range, updates and optional operators get no implicit overload rule" | `cli::user_defined_neg_*` (3 tests); signed-minimum in wasm boundary test; no test that `+x`, `!x`, `~x`, `a..b`, `x++`, `x ?? y` on a nominal type with matching extensions stay rejected | closed WP20: `wp20_s_gaps::unary_plus_not_complement_range_update_and_optional_have_no_overload` |
| Built-in `=`, `&&`, `\|\|`: "Reject extension-based assignment and short circuit overrides. Check RHS-first replacement and skipped effects" | `gce::assignment_and_short_circuit_operators_resist_user_overloads`; `gce::short_circuit_skips_rhs_effects_in_source_and_wasm`; String replacement tests (`cli` String assignment early-exit cleanup) | covered |

Clauses 9 manifest + 6 matrix rows (15). MISSING: 4 small items (mixed-type
primitive coercion rejection, signed shift widths other than `i32`, unary
plus/`!`/complement/range/update/optional no-overload negatives, confirm all
five primitive `u32` compounds in one test), all S, no decision (the audit
disposition already settled scope).

### H1 acceptance reconciliation

| Clause | Evidence | Status |
| --- | --- | --- |
| "Wasm-only execution" | `host_capability_cli::cli_profile_links_one_typed_capability_for_wasm_guests`; `cli::cli_host_profile_is_validated_before_import_free_execution`. No negative test that a non-Wasm/JS host is requested | covered (non-Wasm hosts are absent rather than rejected; nothing to test) |
| "serde-parsed `[host] profile = \"cli\"`" | `memobits-project/tests/discovery.rs::manifest_host_profile_is_parsed_and_validated` (valid cli; missing profile; unknown `browser`; unknown capability; wrong module/params) | covered |
| "one typed capability, `memobits:console.write_i32(i32) -> unit`" | `host_capability_cli::cli_profile_links_one_typed_capability_for_wasm_guests`; discovery test (`params=['i64']` rejected) | covered |
| "source binding via root-module `extern fn write_i32(value: i32);`" | `memobits-syntax/tests/host_declaration.rs::parses_external_function_declaration_and_calls`; `host_capability_cli::source_extern_must_match_manifest_profile_and_signature` (includes "must be declared in the application root") | covered |
| "manifest-selected source and artifact execution" | `host_capability_cli::source_extern_declaration_calls_typed_import_in_run_build_and_artifact_run` (`Host i32: 42` / `Result: i32(7)`) | covered |
| "import-free execution" | `cli::cli_host_profile_is_validated_before_import_free_execution` | covered |
| "undeclared or mismatched Wasm imports before guest execution" | `host_capability_cli::undeclared_and_mismatched_guest_imports_fail_before_guest_execution` | covered |
| "Guide source and standalone Wasm both report `Result: Ok(i32(42))`" | `cli::language_guide_checks_bytes_array_equivalence_in_source_and_wasm`; `c1::language_guide_uses_current_spellings_and_runs_with_empty_stderr` | covered |
| "Other profiles/capabilities/signatures, multi-module declarations, non-CLI hosts, JS ... are not delivered" (limits) | discovery test (other profile/capability/signature rejected); root-only rule in `source_extern_must_match_manifest_profile_and_signature` | covered |

Clauses 9; MISSING 0.

### D1 acceptance reconciliation

| Clause | Evidence | Status |
| --- | --- | --- |
| "Omitted/empty/field/enum body with and without trailing extension" | parse: `memobits-syntax/tests/d1_nominal_forms.rs::nominal_body_forms_parse_with_and_without_trailing_extensions`; run: `cli::inherent_extension_methods_run_from_source_and_wasm`, `d1c::field_bearing_nominal_with_trailing_extension_runs_in_source_and_wasm`; bodyless/empty-with-method executed in the guide only (`bodyless_nominal_types_remain_distinct_and_unconstructable` has no method run) | covered; a dedicated source+Wasm test of a bodyless and an empty-struct type with trailing methods closed WP20: `wp20_s_gaps::bodyless_and_empty_nominal_types_run_trailing_methods_in_source_and_wasm` |
| "direct `extend Type { ... }`" | `parser.rs::parses_inherent_extensions_without_an_interface_constraint`; `cli::inherent_extension_methods_run_from_source_and_wasm`; `cli::directly_imported_public_inherent_extension_runs_from_source_and_wasm` | covered |
| "Bodyless nominal identity stays distinct from empty structs"; "Distinct bodyless identity and diagnostics" | `parser.rs::parses_bodyless_nominal_types_separately_from_empty_structs`; `cli::bodyless_nominal_types_remain_distinct_and_unconstructable` (TE002, TE023) | covered |
| "Non-empty structural records use exact field-name/type shape identity"; "Reordered exact record shapes agree" | `anonymous_shapes.rs::anonymous_record_shapes_are_order_independent_but_exact`; `d1c::anonymous_record_types_require_the_exact_shape` | covered |
| "while expressions run in written order" | `d1c::anonymous_records_and_contextual_inline_enum_variants_run_in_source_and_wasm` (counter-based initializers, source and Wasm) | covered |
| "Inline anonymous enums support unit and payload variants and retain nominal declaration-site identity" | `anonymous_shapes.rs::anonymous_enum_aliases_keep_declaration_site_identity_and_contextual_unit_variants`; `anonymous_enum_payloads_are_typed_and_extracted_by_variant_patterns`; `d1c::inline_anonymous_enum_declarations_keep_distinct_identity_in_projects`; `d1c::anonymous_payload_enum_identity_and_payload_types_are_checked`; `d1c::payload_anonymous_enums_construct_and_extract_multi_field_payloads_in_source_and_wasm` | covered |
| "generic specializations include concrete payload types" | `resolved_types.rs::generic_specializations_keep_inline_enum_payload_types_distinct` | covered |
| "Expected-type constructors and pattern extraction cover unit and payload variants, including local annotations" | `d1c::local_inline_enum_annotation_resolves_without_module_variant_declarations`; `resolve/names.rs::local_inline_enum_annotation_registers_variants_for_its_initializer`, `local_inline_enum_variant_names_do_not_escape_their_block`; `d1c::anonymous_records_and_contextual_inline_enum_variants_run_in_source_and_wasm` | covered |
| "distinct inline declarations remain incompatible" | `d1c::inline_anonymous_enum_declarations_keep_distinct_identity_in_projects`; `d1c::anonymous_payload_enum_identity_and_payload_types_are_checked` | covered |
| "Named qualified payload variants remain intact" | `resolve/names.rs::alias_of_inline_payload_enum_resolves_qualified_constructors_and_patterns`; `cli/match_cli.rs::imported_and_aliased_enums_match_through_qualified_paths`; `enums_cli.rs` | covered |
| "Reference-bearing payloads stay rejected" | `d1c` test at line ~335 (`enum [Borrowed(Option<borrow i32>)]`, "reference type arguments require embedded-loan tracking"); verify its test name when closing | covered (one inline case; named-enum reference payload rejection not located: closed WP20: `wp20_s_gaps::named_enum_and_struct_reference_payloads_stay_rejected`) |
| "String payloads are supported through D2 type-directed cleanup" | `d2_nested_owner_transport.rs`, `d2_record_owner_transport.rs::string_owning_records_compose_as_fields_elements_and_payloads`, `tuple_destructure_memory_stress.rs` (direct-String enum variant) | covered |
| "Generic nominal trailing methods specialize for type and const arguments" | `d1c::generic_nominal_trailing_methods_specialize_for_each_receiver_type` (`Box<T>`, `Packet<const N>`); `generic_nominal_method_specialization_reaches_mutual_method_calls`; `generic_nominal_method_can_instantiate_a_generic_free_function`; visibility and limit tests | covered |
| "Remaining limit: nested expanding generic type arguments in method bodies are not supported. This limit does not narrow the manifest acceptance." | WP21: `d1_nested_generics::bounded_nested_type_arguments_run_for_several_receivers_in_one_module`, `::bounded_nested_type_arguments_cross_a_public_direct_import`, `::unbounded_polymorphic_recursion_hits_the_specialization_limit`; fix in `TypeTable::substitute_generic_arguments` | closed WP21; residual const-forwarding limit closed WP22: `wp22_residual_fixes::const_parameter_forwards_into_nested_types_for_two_instances`, `::forwarded_const_mismatch_is_te002`, `::unknown_const_name_stays_ne003` |
| "Empty anonymous shapes remain gated" | `anonymous_shapes.rs::anonymous_record_and_enum_type_syntax_rejects_ambiguous_empty_shapes` | covered |

Clauses 15; MISSING 3 (one L needing a decision, two S).

### Reconciliation summary

| Row | Clauses | MISSING | Notes |
| --- | --- | --- | --- |
| M1 | 8 | 2 | before/after equivalence (S/M), backend/source separation review (M); both no decision, though depth of extraction is an architect call |
| I1 | 16 | 3 | all S: grouped selector chain execution, grouped-import non-activation, CLI transitive/prelude negative |
| G1 | 11 | 1 | S: generic-function 256 specialization cap untested |
| G2 | 8 | 1 | S: wrong `Output` annotation negative |
| OP1 | 15 | 4 | all S: mixed-type primitive coercion rejection, non-`i32` signed shifts, no-overload negatives for unary `+`/`!`/`~`/ranges/updates/optional, five primitive `u32` compounds in one place |
| H1 | 9 | 0 | |
| D1 | 15 | 3 | L + decision: nested expanding generic type args in methods; S: bodyless/empty method execution test, named-enum reference payload negative |

The only decision-needed item is D1's nested-expansion limit (accept as a
documented limit vs implement), plus the M1 depth question.

## String restore — ACCEPTED; reconciliation reviewed (architect, 2026-11-23)

Verified: workspace 1,188 passed / 0 failed (`logs/wp19-workspace-test.log`),
guide source + Wasm `Result: Ok(i32(42))`, empty stderr. Note: the C1 table
row above that calls bare `String` accepted is superseded by this correction.
`examples/projects/strings` uses bare `String` and fails with TE001; it also
failed at HEAD (pre-existing, not touched — reported to the user).

Architect decisions on the reconciliation:
- All S test gaps (I1×3, G1×1, G2×1, OP1×4, D1×2) are approved as-is.
- D1 nested expanding generic type arguments: implement. Target: bounded
  nested type arguments in generic nominal method bodies (e.g. a method on
  `Wrap<T>` that constructs/calls `Pair<Wrap<T>>` or `Wrap<Pair<T>>`
  finitely) specialize and run; unbounded polymorphic recursion (a method on
  `Wrap<T>` calling itself on `Wrap<Wrap<T>>`) is rejected by the existing
  256-specialization diagnostic, never hangs. If bounded support needs a
  language decision, stop and report a blocker record.
- M1: acceptance is the named seams in
  `interface-architecture-plan.md#compiler-changes-by-phase` (array, List,
  operations responsibilities in private modules; backend free of source
  decisions), not line counts. Do it LAST as its own run, with a before/after
  equivalence harness (diagnostics + execution outputs over the test fixture
  corpus and examples) captured before any move.

## Next run — S test gaps + D1 nested generics


## WP20/WP21 status (contractor, 2026-11-23)

All I1, G1, G2, OP1 and D1 S-gaps are closed by `crates/memobits-cli/tests/wp20_s_gaps.rs` (11 tests; the matching reconciliation rows above now cite them). D1 nested generic type arguments are implemented and tested by `d1_nested_generics.rs` (3 tests). No language decision was needed; no blocker record. Residual limit found: a receiver const parameter cannot be forwarded as an argument of a nested nominal type (`Tag<N>` inside a method of `Tag<const N: u32>` reports NE003 unknown type 'N') because the resolver reads `N` as a type name; a separate, pre-existing issue: method calls on a field projection receiver (`t.first.read()`) fail IR validation (TE018) even for non-generic types. Both are reported to the architect rather than changed.
## WP20/WP21 — ACCEPTED (architect, 2026-11-23)

Verified: workspace 1,202 passed / 0 failed (`logs/wp21-workspace-test.log`),
guide source + Wasm `Result: Ok(i32(42))`, empty stderr. I1, G1, G2, OP1, D1
reconciliations have no MISSING rows; nested generic type arguments work and
unbounded recursion hits the 256 cap.

Architect decisions on residual limits (both are bugs, not language rules):
- Receiver const parameter forwarded into a nested nominal argument
  (`Tag<N>` inside a method of `Tag<const N: u32>`, NE003): const parameters
  in scope must resolve in type-argument positions. Fix.
- Method call on a field-projection receiver (`t.first.read()`, TE018 in IR
  validation, also non-generic): fix; receiver modes must work on projected
  places per I1 (borrow self reads the field place; share self requires a
  mutable owner and respects field-level loans; owned self on a field is a
  partial move and stays rejected per decisions).

## Next run — residual bug fixes, then M1 last

## WP22 status (contractor, 2026-11-23)

Both residual bugs fixed; tests in `crates/memobits-cli/tests/wp22_residual_fixes.rs` (12). I1 rows: receiver modes on projected places (borrow/share/owned) are now covered by `wp22_residual_fixes` (interface-selected case `interface_selected_borrow_self_reads_a_field_place`). Remaining limits: generic functions whose result is not `Array<T, N>`/`T` stay outside the specialization subset (e.g. `fn mk<T, const N: u32>(..) -> Tag<N>`, TE007; body-local `Tag<N>` works); a struct nested as a field of another struct that owns a `string` still hits the LE900 gate when its projected field is a method receiver (`d.title.size()`), unchanged; array elements of String-owning structs work.

## WP22 — ACCEPTED (architect, 2026-11-23)

Verified: workspace 1,214 passed / 0 failed (`logs/wp22-workspace-test.log`),
guide source + Wasm `Result: Ok(i32(42))`, empty stderr. Const params forward
into nested nominal arguments; projected-field receivers work for borrow/share
self; owned self on a field is TE022. `d.title.size()` on a String-owning
nested field (LE900) is deferred to roadmap stage 2 with the element-borrow
limits.

## Next run — M1 (last launch row)

Seams from `interface-architecture-plan.md#compiler-changes-by-phase` already
present: syntax `items.rs`; analysis `types/{arrays,lists,operations,templates}.rs`,
`lower/{arrays,operations}.rs`; wasm `{arrays,operations,...}.rs`.
Triggered-but-missing seams (their trigger conditions have occurred):
1. wasm `validation.rs`: `validate_string_struct_borrows`,
   `unsupported_instruction` and their private signature checks.
2. wasm `layout.rs`: `StructLayout`, `struct_layouts`, `member_layout`,
   `struct_layout_at`, `nested_struct_layouts`, `aggregate_layout`,
   `type_layout` (+ owner-cleanup layout helpers if tightly coupled).
3. analysis `lower/calls.rs`: argument construction from the `ExprKind::Call`
   arm of `Builder::lower_expr` and the selected/receiver call lowering.
4. analysis `types/interfaces.rs`: signature conformance and applicable
   candidate selection.
Method: capture a baseline BEFORE any move (equivalence harness), move code
mechanically (no logic edits, no renames beyond visibility, no reformatting
of unmoved code), then prove equivalence: identical test results, identical
stdout/stderr/exit for every example and fixture command, and byte-identical
Wasm artifacts for the guide and examples.

## M1 acceptance reconciliation (contractor WP23, 2026-11-23)

| M1 clause | Evidence |
| --- | --- |
| Source seams from the architecture plan applied | Pre-existing: syntax `items.rs`, analysis `types/{arrays,lists,operations,templates}.rs`, `lower/{arrays,operations}.rs`, wasm `{arrays,operations,...}.rs`. New: wasm `validation.rs`, `layout.rs`; analysis `lower/calls.rs`, `types/interfaces.rs` (moved items in `m1/equivalence-report.md`) |
| Array, List and operations responsibilities in private modules | Present in analysis types/lower and wasm (listed above); no change needed |
| Existing entry points stay authoritative | Public API untouched; moves are private modules with `pub(super)` visibility only; `lower_expr`/`Checker::expr_impl` delegate |
| Focused before/after diagnostic and execution equivalence | `m1/equivalence.sh`; `diff -r m1/before m1/after` empty (stdout/stderr/exit for check/run/build/run-wasm/syntax/analyze/ownership on 14 examples) |
| Byte-identical Wasm | `m1/*/wasm.sha256` identical (13 artifacts incl. language-guide) |
| Identical test results | 1,214/0 before and after; sorted pass lists equal (`m1/before-tests.txt`, `m1/after-tests.txt`); logs `logs/m1-{before,after}-tests.log` |
| No new dependencies | Cargo manifests/lock unchanged |
| No disconnected production TODO paths | grep of new files: no TODO/todo!/unimplemented! |
| No graph-wide formatting churn | rustfmt run only on the four new files; unmoved code not reformatted; `git diff --check` clean |
| Backend keeps source decisions out of Wasm encoding | PARTIAL: validation and aggregate layout are now separate from `lib.rs` encoding; no audit of other source-level decisions in `lib.rs` was part of this mechanical slice (architect to judge) |
| Rust-owned minimal portable core | Not touched by this mechanical slice (no code change); MISSING as separate evidence |
| Residue (documented, not edited) | Operator/generic-evidence candidate selection inlined in `Checker::expr_impl`; owner-cleanup layout helpers and `host_import`/`field_addr_rooted_at_local` remain in wasm `lib.rs` |

## M1 — ACCEPTED; launch manifest rows all accepted (architect, 2026-11-23)

Architect verified independently: `diff -r -x build.log m1/before m1/after`
empty (14 example projects: check/run/build/run-wasm/syntax/analyze/ownership
stdout+stderr+exit, 13 Wasm sha256 identical); sorted pass lists identical
(1,214); 0 failures.
Architect resolution of the two open M1 clauses:
- "Backend keeps source decisions out of Wasm encoding": memobits-wasm's
  normal dependencies are only entry-abi, diagnostics, ir, ownership and
  wasm-encoder (syntax/analysis are dev-dependencies for tests); no
  interface/extension/evidence/prelude logic in wasm sources; backend follows
  concrete IR call targets. Validation and layout gates now live in
  `validation.rs`/`layout.rs`, separate from encoding. ACCEPTED.
- "Rust-owned minimal portable core": `core::ops` is a Rust-owned virtual
  module (`CORE_OPS_SOURCE`, `is_core_module` in
  crates/memobits-resolve/src/lib.rs); compiler-known Array/List/Option/
  Result/Attempt templates live in crates/memobits-syntax/src/templates.rs and
  analysis `types/{templates,arrays,lists,operations}.rs`; Bytes is a
  compatibility alias with MW003. ACCEPTED.
All manifest rows (S1/S2, N1–N4, M1, I1, G1, G2, OP1, D1, D2, D3, C1, H1)
are accepted by the architect. Pending user decisions: commit packaging and a
repo-wide `cargo fmt`.

## User decisions (2026-11-23) and closing run

User answered: (1) one bulk commit ("toplu commit at"); (2) separate
formatting-only commit; (3) migrate examples/projects/strings to `string`;
(4) REMOVE MW001 — `Option<T>` is accepted silently; D3's migration-diagnostic
clause is waived by user decision (docs/design/decisions.md updated by the
architect). Architect will create a launch branch (repo is on main), commit
with explicit paths and no co-author trailers per the requirements, then
run `cargo fmt --all`, re-test, and commit formatting separately.

## Closing — committed (architect, 2026-11-23)

Branch `launch/manifest-completion` (from main @ c41b624), not pushed:
- `554e0d1` Complete launch manifest rows D1-D3, C1, M1 and follow-ups
  (67 explicit paths; .local-design/, legacy/, target/ excluded).
- `5a58b35` Apply cargo fmt to the workspace (19 files, formatting only).
After formatting: `cargo fmt --all -- --check` clean; workspace 1,215 passed /
0 failed (`logs/fmt-workspace-test.log`); guide source + standalone Wasm
`Result: Ok(i32(42))`; examples/projects/strings `Result: i32(0)` (matches
its README). Next: roadmap stage 2 (general owned-element model, element
borrows, replace/swap) when the user asks.

## Examples cleanup (user approved "tamam yap", 2026-11-23)

Scope = the four non-restructuring items; directory restructure and merging
small examples are a later, separate step.
1. Documented expected output for every examples/projects/* project
   (README "Expected output" block; add READMEs for enf-lexer and
   language-guide) + one CLI test that runs each project from source and as
   standalone Wasm and compares stdout exactly to its README block.
2. Uniform success convention: `main` returns `Result<…, Error>` with
   `Ok(<meaningful value>)` on success and `Err(Error { code })` per failed
   check, like the guide. Projects already returning `Ok(…)` stay. Exempt:
   host-capability (H1 acceptance evidence pins `Result: i32(7)`; note why in
   its README).
3. Migrate legacy `Bytes<N>` in hashing and utf8-validator to `Array<u8, N>`
   (zero warnings on `mb check` for every project); fix stale root README
   text (`Bytes<N>` advice, `Option<u32>` → `u32?`, uppercase `String`).
4. Move examples/design/language-guide.mb → docs/design/proposed-language-guide.mb
   with `git mv`, add a header line that it is a historical proposal
   (current rules: docs/design/decisions.md + runnable guide), update links.
Architect commits after review, as a separate commit on
launch/manifest-completion.

## Examples restructure (user approved "klasorleri duzenle", 2026-11-23)

Target layout (architect decision):
```
examples/
  README.md   catalog table: name · topic · run command · expected output
  guide/      the runnable language guide as ONE project (project.toml here),
              split into topic modules under src/
  topics/     arrays, basics, enums, generics-operators (new), host-capability,
              module-imports, numeric, structs
  apps/       astar, enf-lexer, hashing, utf8-validator
  analysis/   unchanged (single-file analyze/ownership inputs)
```
- `basics` = calculator + computation + strings merged as modules of one
  project (Result convention, distinct Err codes, one Ok value).
- `numeric` stays separate (CLI/library-export reference used by README/tests).
- New `topics/generics-operators`: small program (e.g. a `Vec2` type with
  core::ops Add/Sub/PartialEq and a generic constrained helper) using only
  shipped features.
- Guide split: same checks, same error codes, same final `Ok(i32(42))`;
  main.mb keeps `main` and calls per-topic modules. Anything that cannot move
  across a module boundary stays in main.mb and is reported as a finding.
- Use `git mv` for every move; update all live references (tests, READMEs,
  AGENTS.md, crates/memobits-cli/README.md, docs/design/*, live .local-design
  docs: inventory, requirements, implementation-plan, interface plan);
  historical logs/progress/PLAN text stay as history.
- `.gitignore`: ignore example build output (`examples/**/target/`).

## Examples restructure — committed 01709bf (architect verified: 63 guide Err codes and 285 declarations preserved; 1,217 passed / 0 failed; guide source + Wasm Ok(i32(42)))

## Guide check codes + test direction (user approved "yap", 2026-11-23)

Guide check codes renumbered by defining module (1xx numbers … 9xx
operators), table in examples/guide/README.md. Roadmap stage 2 gains:
source-level tests (`test fn`, `assert`, `mb test`) per decisions.md
"Source-level tests"; once shipped, convert the guide and examples' Err-code
checks to tests.

## PRIORITY 0 — Built-in type spelling migration (user decision 2026-11-23)

Binding rules: docs/design/decisions.md "Built-in type spelling". This runs
BEFORE roadmap stage 2 (user: changes get harder as the codebase grows).
Run S1 (compiler + migration tool):
- Parser: `T ! E` and `T ?! E` type operators (`?` tighter than `!`), with
  parenthesized grouping; lowercase `bool`, `char`, `array<T, N>`.
- Type table: Option/Result become the compiler-known optional/fallible
  types behind the operators; Attempt type removed; `T ?! E` ≡ `T? ! E`;
  `Done/Skipped/Failed` desugar to `Ok(Some(v))/Ok(None)/Err(e)` for
  construction and patterns (prelude short names).
- Removed spellings → TE001 with replacement guidance; `Bytes` deleted
  (ordinary unknown type); MW001–MW003 gone; warning channel kept.
- Type display in diagnostics/host output uses the new spellings.
- Entry adapter: `T ! E` and `T ?! E` entries (versioned metadata bump if
  layout changes); define and document CLI result rendering.
- A token-aware migration tool (outside crates, e.g. .local-design/migrate/)
  that rewrites .mb sources and Memobits sources embedded in Rust tests.
Run S2: apply the tool repo-wide (tests, guide, examples, docs), fix
remaining expectations, full verification, docs/inventory/requirements.

### S1 status (contractor, 2026-11-23)

Done: parser support for `bool`, `char`, `array<T, N>`, `T ! E` (`?` tighter than `!`, parenthesized grouping); old spellings still accepted; `?!`/Attempt untouched. Repo migrated with the tool; S2 remains (TE001 for removed spellings, Bytes removal, MW cleanup, Attempt -> `?!`, diagnostics/host type names, entry rendering, expectation updates, docs/inventory).

Tool: `.local-design/migrate/migrate_types.py` (Python 3, stdlib only, not in the workspace).
Usage: `python3 .local-design/migrate/migrate_types.py [--check] [--inline] [--comments] [--report-skipped] [--exclude SUBSTR] PATH...`
`--check` prints a unified diff and changes nothing. Handles `.mb`, `.rs` (string literals that look like Memobits source: raw and normal, escapes mapped back) and `.md` (fenced blocks; `--inline` also `code spans`). Idempotent.
Known limits: Rust literals are treated as Memobits only if they contain `fn`/`type`/`let`/`var`/`use self::` shapes; expected-diagnostic strings and fragments without those (e.g. `"Array<u8, 2>"` in assertions) are untouched (use `--report-skipped`). `Result<T, E>` with a `borrow`/`share` argument is left unchanged with a WARN (no spelling defined for `T ! borrow E`). `Bytes<N>` is rewritten to `array<u8, N>` everywhere (also in sources that deliberately test the Bytes warning: exclude those). Comments are untouched unless `--comments` (.mb, backtick spans only). Bare `Bool`/`Char`/`Array` after `::`, `.`, `type`, and enum variant names in declarations are skipped. Prose in docs needs manual review.

## S1 — ACCEPTED, committed 7d600b9 (1,223 passed / 0 failed)

## Order update (user, 2026-11-23)
Done/Skipped/Failed are removed entirely (no aliases); nested patterns are
added first. `T ! (borrow E)` grouping allowed (syntax only).
1. N-PAT: nested patterns per decisions.md "Nested patterns".
2. S2: `?!` (≡ `T? ! E`), Attempt + Done/Skipped/Failed removal (migrate uses
   to Ok(Some(v))/Ok(None)/Err(e)), old spellings → TE001, Bytes deleted,
   MW001–MW003 removed, diagnostics/host output use new spellings
   (e.g. host renders `Ok(Some(bool(true)))`), entry adapter for `T ?! E`.
3. Roadmap stage 2.

## N-PAT — ACCEPTED, committed (1,245 passed / 0 failed)
Tech debt noted (pre-existing at HEAD, reused by N-PAT): the IR validator
recognizes a compiler-created discard local by its name "discarded match
payload" (crates/memobits-ir/src/scoped_string.rs). Replace with an explicit
local-kind flag in a later cleanup.

## S2 — ACCEPTED, committed (1,243 passed / 0 failed)
Architect correction: the contractor had un-reserved `Option`/`Result` as
user type names without sign-off; restored the HEAD rule (`Option`,
`Result`, `Attempt` reserved) with its test. Built-in type spelling change is
complete. Next: roadmap stage 2 plan.

## Platform layers + memory model — user approved (2026-11-24)
See decisions.md "Platform layers and memory model". Pending user decisions
for stage 2: assert failure semantics, replace/swap spelling, test function
form (architect defaults: trap; function form `replace(place, v)`/`swap(a, b)`;
`test fn`).

## Stage 2 — user said "otonom ilerle" (2026-11-24); defaults accepted
Order: T1 test infrastructure → T2 convert guide/examples checks to tests →
A1 alloc layer (`use alloc::List;`, profile gating) → E1 general owned-element
model (List<T> any element, array<string, N>, element borrows, list literals,
list[i]) → R1 replace/swap → D1 tech debt. Architect reviews and commits after
each run.

## T1 — ACCEPTED, committed (1,263 passed / 0 failed)
Architect rule for the open scope question: `mb check` always checks every
project module and all tests; `build`/`run` check only modules reachable
from the app/library roots (tests ignored there). Implement in T2.

## T2 — ACCEPTED, committed (1,264 passed / 0 failed; all 13 projects' mb test pass)
## Next: A1 alloc layer — see decisions.md "Alloc layer switch"

## A1 — ACCEPTED, committed a843e79 (1,276 passed / 0 failed)
## Next: E1 general owned-element model — decisions.md "Owned elements in collections"
Run E1a: design note in PLAN (touch points, slices) + implement slice 1
(owned elements in array<T,N> incl. array<string,N>; element places with
borrow/share/in-place match/projection; element-borrow limits lifted).
Run E1b: List<T> any element, list literals, list[i] places, loop borrowing.

## E1 design note (contractor, 2026-11-24)

Scope: decisions.md "Owned elements in collections". E1a = `array<T, N>`;
E1b = `List<T>`.

### Gates that blocked owned array elements (before E1a)

- `crates/memobits-wasm/src/layout.rs` `type_layout`: arrays rejected a direct
  `string` element ("Wasm does not yet support String array elements").
- `crates/memobits-wasm/src/validation.rs` `supported_type`: `Type::Array` of
  `Type::String` was an unsupported local/value type (LE900).
- `crates/memobits-ir/src/lib.rs` heap-String validation (the `ArrayNew` arm and
  the `feeds_owned_array_element` capture rule) used `owns_string_aggregate`,
  which is false for a bare `String`, so moving a String local into an array
  element reported TE018.
- `crates/memobits-ir/src/lib.rs` `VariantAddr`: borrowed access to a `String`
  payload was TE018 "String enum payloads require a consuming match", which
  blocked in-place `match` on a String-owning enum element.
- IR heap-String `report` rejected `Share` projections (`ElementAddr`,
  `FieldAddr`, `VariantAddr`) of a heap owner, so `items[1].share()` failed.
- `crates/memobits-wasm/src/validation.rs` `validate_string_struct_borrows`:
  the call-argument allowance understood a chain of at most two reborrows from
  a local and ignored `FieldAddr`, so `grid[i][j].borrow()`,
  `bag.items[0].borrow()` and `d.title.size()` were LE900 ("a whole borrow or
  share of a struct with String fields requires ...").
- `crates/memobits-wasm/src/lib.rs` `field_addr_rooted_at_local`: a String field
  reached through an element (`items[i].text.len()`) was LE900 because only
  `FieldAddr` links were accepted in the chain.
- `crates/memobits-analysis/src/lower.rs` `lower_collection_read`: only `Field`
  bases were lowered as read places; a `String` `Index` base was loaded
  (`unsupported reference pointee`).
- `crates/memobits-ir/src/scoped_string.rs` `validate`: whole-array `var`
  reassignment of a String-owning array was TE018.

### How array and List storage and cleanup work

- Array storage is inline in the frame (`ArrayCell`, row-major, element stride
  from `type_layout`); a `string` element is a 12-byte descriptor, an owner
  struct element is its struct layout. Arrays of owners are laid out through
  `struct_layout_at` / `member_layout` (arrays of flat owners were admitted in
  WP13/WP14).
- Ownership facts are IR-global: `Program::heap_strings` (scoped_string.rs)
  propagates "this local holds heap storage" through named-local moves
  (`ArrayNew`, `StructNew`, `Assign`, call transport, returns). Cleanup is
  type-directed: lowering emits `EndStructLocal` for any struct/enum/array local
  that `is_string_owner_aggregate_type`, and Wasm
  (`emit_local_string_storage_cleanup`) walks the type (arrays loop over
  elements, enums by active tag), so any admitted element type is released
  exactly once on normal and early returns. A moved-from source is cleared by
  `clear_moved_heap_source`; an `Assign` with `initialize: false` releases the old
  value first.
- Element places: `ElementAddr` (bounds check, trap `IndexOutOfBounds`) and
  `FieldAddr`/`VariantAddr` chains built by `lower_place` + `address_chain`;
  loans (memobits-ownership `loans.rs`) already track constant index, dynamic
  index (`items[_]`, conservative) and field/variant steps.
- `List<T>` is a separate 12-byte descriptor (`list_descriptor.rs`) with
  `Primitive` elements only (`Type::List(Primitive)`); `ListPush/Pop/Get/Read`
  copy primitive bytes; there is no per-element cleanup.

### Touch points

E1a (this run): the gates above, plus `check_element_support`/repeat check in
analysis `types.rs`, TE022 text (`types/arrays.rs`), array-literal owner staging
(`lower.rs`), `array_binding`/`validate` (reassignment).
E1b (next): `Type::List(Primitive)` in `memobits-ir` must become
`List(Box<Type>)` (types, layout, `ListGet/Read/Push/Pop` operand and result
types, entry ABI, wasm `list_descriptor`, `lists.rs` in analysis); element
stride from `type_layout`; `EndListLocal` must release owned elements (loop
over len, then free the block); list literal `[a, b]` with an expected `List<T>`;
`list[i]` as a place (`ListElementAddr` analogue of `ElementAddr` with the length
read from the descriptor; loan path step like an element); `pop()` returning
`T?` for owners (moves out, non-copyable); `get` stays copyable-only; `loop x in
items` read-only loans for non-copyable elements; realloc/grow must memcpy
descriptors (bitwise move) and `clear` must release elements.

### Risks

- Three mirrored owner predicates (IR `scoped_string.rs`, analysis `lower.rs`
  and `types.rs`) must stay in step; E1a changed none of them (they already
  cover `string` elements through the array recursion).
- The IR heap-String validator is pattern based (instruction shape after
  `ArrayNew`); element literals that are not named locals or hidden-local staged
  owners stay rejected rather than guessed.
- Borrowed in-place match now accepts String payload bindings as read-only
  references (`VariantAddr`); the stale TE018 negatives for this were updated.
- E1b grows heap storage and moves elements bitwise; moved-from slots must be
  cleared like `clear_moved_heap_source` does for arrays.

## E1a — ACCEPTED, committed (1,281 passed / 0 failed)
Architect decisions: in-place match of borrowed String enums is accepted
(read-only lending per PAT-01). `items[i] = s` on an owning element is
rejected for now; R1 must make it a proper RHS-first replacement that
releases the old element exactly once (same contract as S2 field
replacement), alongside `replace`/`swap`. D1 must unify the three mirrored
owner predicates (IR scoped_string.rs, analysis lower.rs, types.rs) into
one shared predicate per decision A.

## E1b — ACCEPTED, committed (1,287 passed / 0 failed; architect verified guide source+Wasm empty stderr, all 14 examples check/test)
## Next: R1 — replace/swap + owning overwrite as RHS-first replacement;
## also loop over fixed arrays of owners (borrow binding), reword the nested
## List TE017 message, and add "Shipped E1 details" to decisions.md.

## R1 — ACCEPTED, committed (1,293 passed / 0 failed; guide 87 tests; empty stderr verified)
## Next: D1 cleanup run — see dispatch prompt (predicate unification, discard-local flag,
## Error-ancestry message, direct temporaries as owned args, if/match RHS for replace,
## swap BE005 hint, unused ignored_tests, mixed struct-literal LE900).

## D1 cleanup — ACCEPTED, committed (1,301 passed / 0 failed; items 1–2 equivalence verified by architect)
Stage 2 complete. Remaining known limits: if/match owner values outside
`replace` (TE018); struct literal as function tail (LE900); swap with dynamic
same-collection indices (no runtime check); nested List<List<T>>.

## Stage 3 — user: "sırayla git" (defaults approved; decisions.md "Stage 3 ergonomics")
Order: G1 remaining limits → G2 try/else → G3 ranges → G4 interpolation →
G5 const → G6 numerics → G7 patterns → G8 `~`/Self.

## G1 — ACCEPTED, committed 9038be2 (1,307 passed / 0 failed)
Bug carried into G2: `if c { a } else { return …; }` reports TE013 ("string
and never"); a diverging branch must take the other branch's type
(LANG-04/05 divergence). Fix first in G2 — `try … else { return … }` relies on it.
Follow-ups (later): Some(list)/enum List payloads, arrays of Lists, List
fields in structs; discarding an owner `if` as a statement.

## G2 — ACCEPTED, committed (1,321 passed / 0 failed)
Follow-up batch (principle A, schedule after G8): heap payload composition
gaps hit in G2 — `Ok(Some(heap))`, `Ok(list)`, struct literal inside `Ok(…)`,
heap `Ok(x)` inside an if branch (TE018/LE900); plus G1 leftovers
(Some(list), enum List payloads, arrays of Lists, List fields in structs).

## G4 — ACCEPTED, committed (1,349 passed / 0 failed; equivalence verified)
Follow-ups added to the post-G8 batch: float formatting in interpolation
(Rust Display, shortest round-trip); heap String call results returned or
pushed directly (`fn h() -> string { g() }`, `xs.push(g())`, TE018).

## G5 — ACCEPTED, committed (1,366 passed / 0 failed; equivalence verified)
Accepted contractor choices: const-named match arms TE017 until G7 (G7 must
turn them into constant patterns); LE004 cycle, LE005 non-constant.
Tech debt: `[v; NAME]` repeat count accepts only uppercase-leading
identifiers (case-based parse rule) — generalize to any const name in G7/G8.

## G6 — ACCEPTED, committed (1,384 passed / 0 failed)
Follow-ups (later, optional): overflowing_*, pow, abs, rotates, bit counts;
checked_* on untyped literal receivers infer from expected `T?`.

## G7 — ACCEPTED, committed (1,404 passed / 0 failed). G5 repeat-count debt resolved.
Follow-ups: guards seeing Strings inside String-owning tuples in enum payloads
(needs borrows of String-owning aggregates in locals); literal on `string ! E`
Ok payload (TE018); mixed String+other payload with String unbound; @-bindings,
struct/float/range patterns (open).

## G8 — ACCEPTED, committed cec50ae (1,416 passed / 0 failed). STAGE 3 COMPLETE.
Accepted: untyped `~0` defaults to u32 (same convention as other bitwise ops).

## Follow-up batches (architect priority, decision-free under principle A)
F1: method calls with aggregate/struct arguments (TE017 today, e.g. `q.eqx(r)`);
    heap String call results returned or pushed directly (`fn h() -> string { g() }`,
    `xs.push(g())`, TE018); hex/binary integer literals `0x…`, `0b…` with `_`
    digit separators (standard spelling, incl. const and patterns);
    drop the duplicate NE003 after a misplaced `Self` SE002.
F2: heap payload composition: `Ok(Some(heap))`, `Ok(list)`, struct literal inside
    `Ok(…)`/`Some(…)`, `Some(list)`, enum List payloads, arrays of Lists, List
    fields in structs, mixed String+other payload with String unbound, literal on
    `string ! E` Ok payload, guards seeing Strings in tuples inside payloads.
F3: float formatting in interpolation (Rust Display, shortest round-trip).
Then Stage 4 (needs user decisions: closure capture semantics etc.).

## F1 — ACCEPTED, committed (1,427 passed / 0 failed)
Added to F2: tuple holding a String-owning enum (`(gk(), 1)` validation
error); `string ! E` call results beyond immediate consuming match; List
call results gate; range diagnostics should echo the literal as written
(hex stays hex) instead of the canonical decimal.

## F2 — contractor report written (2026-11-24); awaiting architect acceptance
Items 1-9 shipped except the struct-with-enum-field transport gate (kept, TE017); see launch-progress F2.


## F2 — ACCEPTED, committed (1,441 passed / 0 failed)
Tech debt: literal original spellings live in a thread-local side table keyed
by span (syntax/literals.rs) — move the original text into the AST literal
node. Remaining gate: struct with String/List field + heap-owning enum/tuple
field moving by value into a call (widen the shared predicate to enum fields).
Next: F3 float formatting + these two items.

## F3 — ACCEPTED, committed (1,453 passed / 0 failed). Follow-up batches F1–F3 COMPLETE.
Accepted unrequested change: Cargo.toml dev-profile opt-level 3 for wasmi crates
(test runtime only; reported to user). Remaining small items: in-place match
on struct enum field with List payload (TE018); struct whose only owning
field is an enum/tuple is not a transport owner.
Waiting on user: Stage 4 decisions (anonymous fn syntax `fn(x) => …`, closure
model, multi-generic `where`, Box<T>, named-fn `=> expr` bodies).

## STAGE 4 started (user: "basla"); decisions.md "Stage 4: functions as values…"

## H1 — ACCEPTED, committed (1,475 passed / 0 failed)
Accepted choices: method wins over same-named field call; anonymous `=>`
infers result from body; ownership analysis treats an indirect call as a
call to every address-taken function of that signature (conservative).
Carry into H2: `borrow fn`/`share fn` parameters; List params/results in
function types (TE017 today).

## H2 — ACCEPTED with required follow-up, committed (1,493 passed / 0 failed)
ARCHITECT REQUIREMENT (H2b, before H3): capture inference currently probes the
closure body and promotes captures when a diagnostic *quotes the variable
name* — semantics keyed on diagnostic text, cost ~(promotions+1)^depth.
Replace with a structural capture analysis (walk uses; classify mutation
contexts from the checker's own facts: assignment targets, compound assign,
share receivers/arguments, push/pop/clear/replace/swap, nested closures'
captures), linear in body size, no dependence on message wording. Behavior
must stay identical (same tests green). Also: leak test for a temporary List
owner passed through a function value (`indirect(make(), 0)`), and make the
direct `take(make(), 0)` form consistent with it.

## H2b — ACCEPTED, committed (1,503 passed / 0 failed). Capture inference is structural; 12-level nesting 77 s → 35 ms.
Next: H3 generics (multiple params/bounds via where, borrowed generic params).

## H3 — ACCEPTED, committed (1,519 passed / 0 failed)
Delegated syntax reported to user: qualified projection `T::Interface::Name`.
Open (later): explicit call-site type args `f<i32>(x)`, method-level type
params, `where` on type declarations, const params as values (`[x; N]`,
`0..N`), nested projections; String literal in tuple built in generic body (LE900).
Next: H4 Box<T>.

## H4 — ACCEPTED as interim, committed (1,537 passed / 0 failed)
REQUIRED before H5 (H4b): (1) release of recursive structures must not be
bounded by call depth — a 1,000+ node list/tree currently traps "call stack
exhausted" on drop; use an iterative release (worklist / pointer reversal /
tail-field loop) so million-node lists drop; (2) single-pointer-word Box
layout per decision (own IR type; heap block = T's layout), keeping all
owner rules; (3) built-in String/List methods auto-deref through Box.

## H4b — ACCEPTED, committed (1,545 passed / 0 failed). Box = 1 pointer word; O(1)-stack release (1M-node list drops).
Backend task queued (BK1): allocator first-fit single free list shows
pathological scans when many small frees precede larger allocations (98 s vs
0.1 s in a contractor probe). Replace with segregated size classes (and
coalescing/splitting as needed); heap programs' Wasm will change, behavior
must not. Kept gate: consuming nested patterns through box payloads (needs
partial-move tracking inside the box).
Next: H5 owned (escaping) closures.

## H5 — committed e85e6d4 as INTERIM (1,561 passed / 0 failed)
Architect rejects the per-exact-type representation switch (whole-program
discovery makes one module's closure change another module's copy rules —
non-local semantics). Proposed fix (H5b): uniform rule — owned `fn(...)`
values are move-only owners with a nullable environment (null env = no heap,
trivial release); calls and lending borrow, so higher-order use is unaffected.
Pending USER decision: how a closure that mutates its captured state is
expressed (today: dynamic trap 14). Options presented: dynamic trap /
immutable environments / `var fn(...)` type marker (architect recommends
`var fn`).
## BK1 — ACCEPTED, committed (1,566 passed / 0 failed). Waiting on user for H5b mutation-rule decision.

## User chose C (2026-11-25): `var fn(...)` for env-mutating owned closures. Run H5b.

## F4 — ACCEPTED, committed (1,581 passed / 0 failed). STAGE 4 + follow-ups COMPLETE.
Open small items: share fn parameter reassignment; explicit call-site type
args; generic methods in interfaces; struct with array<string,N> field built
from a named array local (TE018); moving owner fields out of `self`.
## STAGE 5 (order: formatter → Component Model/WIT → packages → LSP). Start S5-1 `mb fmt`.
## S5-1 mb fmt dispatched (decisions.md 'Source formatting')
## S5-1 — ACCEPTED, committed (1,615 passed / 0 failed). Next S5-2 Component Model — needs user decision on engine/output.
