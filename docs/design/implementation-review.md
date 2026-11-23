# Implementation review

Review date: 2026-11-16. This is a point-in-time review of the current working
tree against the accepted design, not a certification of memory safety.
No compiler or runtime implementation changes were made during this review.

## Confirmed findings

### High: direct owner reads bypass live exclusive loans

`memobits-ownership/src/loans.rs::check_instruction` checks specific writes,
loan creation, calls, and consuming operands. It does not generally check
read operands against active exclusive loans. A structurally valid IR function
with `Borrow(Share, owner)`, `Capture(Read, owner)`, then `Load(share)` passes
`check_loans` without diagnostics. The capture occurs before the share's last
use and should be rejected. Reference loads and reborrow access also need an
access-matrix audit rather than a fix limited to Capture.

Current exposure is limited: source borrow/share remains unsupported and the
backend rejects reference IR. This must be fixed before enabling that path.

### Medium: independent reference parameters are conflated

`provenance` assigns every reference parameter the same `Root::External`.
A valid function with two distinct share parameters, a store through the first,
and a later load through the second receives BE005. At a checked internal call,
exclusive parameters must already have non-overlapping owners. The callee needs
to preserve parameter identity and the relevant call contract, while reborrows
must retain their actual ancestry. External ABI assumptions remain a separate
unimplemented contract.

### Medium: library output retains unrelated functions in a selected module

`lower_resolved` lowers every function in every loaded module; the backend
emits every function in the resulting Program. Export selection restricts the
public export table, not the function bodies included in the artifact.

Reproduction: one `main.mb` containing public `answer`, private `main`, and
private `unused`, with only `answer` selected in the manifest export table.
`mb build --lib` succeeds with one export but the Wasm function section contains
three functions. This violates the requested omission of unrelated application
entry code when entry and library definitions share a module. Existing separation
works when the unrelated entry is in an unloaded module.

Implement item reachability from entry/export roots and remap function identities
before emission. Keep checking policy for unused source separate from the rule
that unrelated executable bodies must not enter the artifact.

## Alignment and incomplete targets

- The crate layout, shared diagnostics, primitive type/flow analysis, typed CFG,
  owned move checks, Wasm backend, and common source/artifact runtime follow the
  accepted direction. Existing libraries provide TOML/Serde, Wasm encoding,
  validation in tests, and execution; language-specific passes are handwritten.
- Borrow/share is experimental IR infrastructure, not an end-to-end language
  feature. `check_loans` is separate, while `check_moves` rejects references.
  Running both is not yet a usable combined reference-safety pipeline.
- General aggregate types, strings, collections, matching, and outcome types
  were unavailable in the executable subset at the time of review.
  The [fixed-grid A* consumer](../../examples/apps/astar/README.md) has
  since landed, along with the [bounded ENF lexer fixture](enf-lexer-slice.md).
  ENF protocol conformance remains pending.
- Dependencies, import selection, external packaging, and dependency cycle
  checks are not implemented merely because manifest fields are parsed.
- Per-definition incremental compilation/cache artifacts are not implemented.
  Item reachability and incremental invalidation are separate tasks.
- Optimization, compile/run latency measurements, cross-platform execution
  validation, and a stable binary compatibility contract remain pending.
  Wasm emission alone does not establish these properties.
- Status documents should distinguish the implemented experimental loan API
  from source support. Statements that library builds omit unrelated entry code
  need the current module-granularity qualification.

## Verification

- `cargo test --offline --workspace -q`: 146 tests passed.
- `git diff --check`: passed for tracked changes.
- Three additional isolated audit tests reproduced the findings above. They
  failed their expected-correctness assertions; both loan fixtures passed IR
  structural validation first. The library test inspected the generated Wasm
  function section using wasmparser.
- Temporary reproduction crate and project:
  `/tmp/memobits-audit-77uy00z7`. These are session-local evidence, not persistent
  regression coverage. Promote them into the relevant crate suites with fixes.

This review did not prove all borrow-checker cases, audit every legacy source
change, benchmark performance, or execute on other operating systems. Passing
the existing suite is evidence for its covered subset, not completion of the
language's safety or compatibility goals.

## Recommended next sequence

1. Add permanent regression tests and repair loan access/provenance rules.
2. Establish a combined availability and loan-checking gate, then connect source
   lowering and Wasm reference frames behind end-to-end tests.
3. Fix item-level library reachability, including same-module entry exclusion.
4. Expand the executable subset toward collections and the small validation
   consumers; keep ABI stability and optimization claims deferred until tested.

## Fix checkpoint

The three findings above have been addressed with permanent ownership, backend,
and CLI regression tests. Direct reads and reference access now respect live
exclusive loans, and reference parameters retain distinct root identities.
Wasm emission selects the transitive direct-call closure of export roots and
remaps compact function indices, excluding unrelated same-module entry bodies.
Source analysis still checks all declarations in loaded modules; this change
does not implement per-definition incremental compilation.

The next integration step has introduced `check_ownership`, combining move and
loan diagnostics at CLI and backend boundaries. It retains BE002 for references
until reference availability and executable lowering are implemented. This shared
gate does not yet enable source borrow/share or establish a stable reference ABI.

## Subsequent reference availability checkpoint

Reference availability is now implemented at the shared ownership gate; the
previous blanket BE002 limitation above is superseded. Invalid nonconsuming
reference transport remains explicitly rejected with BE002. Reference handles
move through captures, assignments, and CFG arguments; fresh loan sites represent
reborrows. Additional tests cover availability on joins/backedges, frozen-parent
relocation, local handle mutation, and owner consumption in terminators. Source
reference lowering and Wasm reference emission are still disabled.

## Source-reference audit follow-up

Two additional regressions were reproduced and repaired before Wasm preparation:

- A reference-valued RHS of short-circuit `&&` or `||` was forwarded as a raw
  loaded scalar to a consuming join, causing TE018. Lowering now computes a
  fresh owned Bool with equality to true inside the RHS branch, preserving
  short-circuit evaluation and the restriction against raw loaded-value escape.
- A directly constructed IR call could pass an immutable local Share handle
  to a Share parameter without BE004. The call checker now enforces the same
  capability restriction as stores and explicit reborrows. Mutable handles
  remain accepted.

Permanent regressions cover both fixes. The full workspace suite passes 182
tests. No additional concrete defect was reproduced in this bounded review;
this is not a proof of complete ownership soundness. The next-stage requirements
are recorded in `wasm-reference-readiness.md`; reference emission remains gated.
