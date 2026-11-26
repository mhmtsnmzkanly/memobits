> Historical working document, moved from the local design folder on 2026-11-26.
> It records decisions and evidence at the time; current rules are in
> [../design/decisions.md](../design/decisions.md) and status in [../roadmap.md](../roadmap.md).

# Memobits implementation handoff

Language baseline is `863a45e`; handoff/scaffold baseline is `113ec09`. This package is a plan and disconnected scaffolding. No language behavior has been added. Start in the repository root and read [implementation requirements](../design/launch-manifest.md), [AGENTS.md](../../AGENTS.md), and the [accepted decisions](../design/decisions.md). The tracked [implementation plan](../design/implementation-plan.md) describes the wider roadmap. The [canonical local language feature inventory](../design/feature-inventory.md) records shipped behavior, accepted intent, open proposals, and acceptance boundaries across all tranches. Resolve historical statements against current code and regression tests before treating them as pending work.

Preserve the existing root README and calculator, computation, hashing, and strings example worktrees, including the existing hashing artifact. Use them as fixtures or copy them into a temporary directory. Keep subsequent changes confined to the active slice. This handoff needs no parent-session follow-up. If accepted semantics are missing, leave the affected interface gated, record the decision needed and evidence, and continue an independent, authorized slice. Do not treat proposals, experimental workarounds, or untracked example syntax as language decisions.

## Canonical launch prompt

Copy this block as the single implementation launch. Start at the current checkout. The baseline below the prompt describes the handoff, and is not a request to reset the branch.

```text
Implement the full current Memobits launch manifest in .local-design/implementation-requirements.md, using .local-design/implementation-plan.md for orchestration, .local-design/interface-architecture-plan.md for compiler seams, and .local-design/language-feature-inventory.md for accepted language contracts and historical status. Read AGENTS.md. Treat the launch manifest and blocker register as the scope for this run. The struct-share and hashing tranche and the Add pilot are checkpoints, not completion. Continue independent work when another slice is blocked.

Before edits record HEAD, status, and hashes of the existing dirty README and calculator, computation, hashing and strings fixtures including their existing artifacts. Preserve them. Use disjoint workers only for independent vertical slices or read-only investigations. Merge shared compiler changes serially. Assign one orchestrator to all Cargo builds and tests with -j1 on the warm workspace target, using targeted tests before one final workspace integration pass. Put generated Wasm and scratch fixtures in /tmp. No build artifacts in commits.

Use the delegated defaults in the manifest where compatible with accepted behavior. Record each chosen public default and its tests. If an actual major conflict or missing owner choice prevents a safe contract, keep the affected gate closed, record the exact decision and evidence, and finish the other runnable slices. Do not expand into Box, general reference transport, JS hosting, speculative operators or allocator/representation optimization.

For each activated language slice update the runnable language guide and scoped tracked docs in the same change. Verify source and standalone Wasm, failure diagnostics, and capped same-instance reuse for ownership changes. Commit only completed, tested, explicitly staged slice files. No co-author trailers, blanket staging, unrelated examples or temporary artifacts. Never hide a partial slice behind a passing unrelated suite.

Stop for the independent parent audit after the required manifest is fully verified or every remaining row is genuinely blocked with an auditable reason and all independent work is done. Deliver a row-by-row evidence report with commit IDs, tests, exact results, scope and defaults chosen, residual gates, and dirty-file/artifact preservation checks. Report partial status whenever any required item remains blocked. Do not start the independent audit or a later feature tranche.
```

## Launch order after the baseline tranche

Follow the [full manifest](../design/launch-manifest.md#full-launch-manifest) for completion.

1. Start S1/S2 and N1–N3 in dependency order within each lane. Extract compact compiler modules as each lane needs them. Coordinate shared files rather than applying concurrent edits to a compiler layer.
2. Establish explicit imports and interface selection, then run the Add pilot. Implement constrained type/function/const instantiation and evidence forwarding. Finish associated `Rhs`/`Output` and the general operator matrix, including mixed operands/results and exclusive compound forms. Current OP1 progress: nominal `/=` and `%=` now select `DivAssign` and `RemAssign` with concrete evidence and the established compound-place sequencing. Later checkpoints cover selected generic owned-local compounds. See [launch progress](launch-progress.md) for per-family coverage and [the transfer handoff](#local-only ".local-design/archive/superseded/transfer-handoff.md is a local note, not in the repository") for open acceptance work.
3. Land nominal and structural data slices, tuples, optional grouping followed by construction, and char-first text. These may progress independently wherever file ownership and accepted syntax allow. Complete the core split and coordinated spelling migration after replacements work.
4. Integrate the CLI-only Wasm host profile and one capability after its manifest/ABI validation is ready. Run combined fixtures and the completion rubric before handing off.

## Tranche 1. Direct struct share and hashing foundations

| Order | Slice | Dependency and stopping point |
| --- | --- | --- |
| 1 | S1, direct exclusive struct parameter | Extend the direct borrowed-struct path to a direct internal `share Record` of a named mutable caller owner. First enable read-only use and validate the exclusive call and loan boundaries. Keep field writes gated at this checkpoint. |
| 2 | S2, direct String field replacement through that parameter | Build on S1 and the existing staged field-replacement and direct `share String` paths. Enable only the RHS forms already supported on direct mutable owning locals. Validate caller cleanup before opening another transport path. |
| 3 | N1, unsigned widening | First numeric slice. Implement only the lossless `u8` to `u32` foundation. Use the accepted `as` and `.to_u32()` forms, then finish the approved cast matrix under N4. |
| 4 | N2, explicit wrapping arithmetic | Add `u32` wrapping addition and multiplication as an independent vertical slice. Preserve plain checked arithmetic. Use the approved `wrapping_add` and `wrapping_mul` methods. |
| 5 | N3, unsigned bit operations | Implement the approved `u32` bitwise operators/methods and unsigned shifts with their existing accepted precedence and checked count. |
| 6 | Numeric consumer verification | Run the unchanged software hashing example and test the selected primitives independently. Once all required public operations exist, exercise a native equivalent in a controlled temporary fixture or in an explicitly authorized example update. |

This is the default integration order. S1 and S2 are dependent. N1–N3 are ordered for integration and example migration. Numeric work can progress if a struct slice blocks. Continue through the full launch manifest after these checkpoints. The broader historical inventory below provides context. Only items selected in the launch manifest are required in this run.

## How to execute a slice

1. Reproduce one success and one rejection or failure on the baseline. Trace the shortest path through source checking, lowering, typed IR validation, ownership and Wasm. Identify the existing primitive or aggregate path to reuse.
2. Implement the slice end to end behind the smallest gate. Keep the old gate for excluded forms. Test the gate at the relevant layer and verify normal source entry points. Avoid backend-only checks for language rules that the ownership or IR stages already enforce.
3. Update the runnable language guide and live status documents for a public language change. Follow AGENTS.md for multiple-module or CLI-dependent examples. Leave historical checkpoints dated and add current cross-links where readers may confuse them with the current status.
4. Run focused checks and source/standalone Wasm verification before workspace checks. Record the commands, results, temporary artifacts, remaining gates and exact restart point.

## Parallel work and build budget

One build orchestrator owns the Cargo target directory and executes all Cargo and artifact build/run commands in sequence. Run Cargo builds and tests with `-j1`. Workers may read, review, draft tests or edit strictly disjoint files. Do not parallelize by compiler layer on a shared change. The struct and numeric paths eventually touch the same analysis, IR and Wasm files, so serialize their integration. Assign a single writer to shared guide and status files. Independent fixture preparation, design review and provenance inspection can run alongside implementation without invoking Cargo.

Prefer the warm workspace Cargo target directory, or retain an explicitly configured target directory that is already warm. Use that same target for focused and workspace checks. Write generated Wasm to a separate temporary output directory. Before choosing a cold target, check free space and record why the warm target is unsuitable. Preserve the existing Cargo profile and flags when reusing a warm build. Disable incremental output and debug information only when a cold build is necessary and temporary storage is tight. Prefer an offline baseline if the dependencies are already cached. Run one focused suite per changed behavior, rerun failures narrowly, then run the workspace suite once at the completed integration checkpoint. Avoid concurrent workspace runs, unnecessary clean builds and repeated unchanged checks. A reasonable planning budget is one baseline pass, one focused build/test cycle per slice plus a retry for a concrete failure, and one full workspace pass per integrated tranche. A persistent blocker gets an explicit record and an independent next step.

Commands for the orchestrator, from the repository root:

```sh
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$PWD/target}"
memobits_wasm_dir="$(mktemp -d /tmp/memobits-wasm.XXXXXX)"
cargo test -j1 -p memobits-cli --test cli string_struct
cargo test -j1 -p memobits-wasm --test stack string_struct
cargo build -j1 -p memobits-cli
"$CARGO_TARGET_DIR/debug/mb" run --project examples/guide/project.toml
"$CARGO_TARGET_DIR/debug/mb" build --project examples/guide/project.toml --output "$memobits_wasm_dir/guide.wasm"
"$CARGO_TARGET_DIR/debug/mb" run "$memobits_wasm_dir/guide.wasm"
cargo test -j1 --workspace
cargo fmt --all -- --check
git diff --check
```

Choose the focused filters for the active slice. Do artifact runs only after a successful build. Compare exact values as well as exit status. For scalar entries, account for the documented raw Wasm type display in standalone mode. Outcome entries should agree exactly. Record a baseline test failure separately from a slice regression.

## Later tranches. Remaining scope inventory

Priorities are scheduling guidance. P0 protects the next slice, P1 unblocks demonstrated consumers, P2 extends the language on established foundations, and P3 is deferred design or measurement. The launch manifest supersedes earlier scheduling where it selects an item from this inventory. None of the rows below automatically enables a language feature. The later tranches proceed from ownership and consumer blockers (P1), to bounded language and package slices (P2), to measurement and new design work (P3). Each row is an inventory item that must be split into vertical slices before scheduling. Only Tranche 1 has Rust preparation modules.

| Priority | Remaining work | Dependencies | Acceptance boundary |
| --- | --- | --- | --- |
| P0 | S1/S2 and ownership regressions | Existing direct borrow gate, field replacement, lexical cleanup | Caller still owns every field. Enforce exclusivity and prove exact cleanup and reuse. |
| P0 | Handoff and documentation accuracy | Source, actual tests and accepted decisions | Cross-link the runnable String-struct example and distinguish special String fields from ordinary aggregate A1–A4 support. Fix the UTF-8 note that broadly gates other embedded storage when updating live docs. Preserve historical checkpoints. |
| P1 | N1–N3 and hashing consumer | Explicit numeric contracts and grammar decisions | Deterministic width-specific behavior, existing checked traps, exact independent FNV-1a/DJB2/Adler-32 vectors in source and artifact. |
| P1 | Remaining heap ownership | S2 and per-place provenance | Separately prove forwarded borrow/share, owned struct args, returns, whole replacement, struct drop, extraction and nesting. Stage args left to right, prove drop exactly once per path, and test bounded Wasm reuse before each gate opens. |
| P1 | General temporary cleanup, heap Result transport and forwarded `share String` | Scope and loan provenance, existing direct Result and String paths | Validate each flow independently across joins, early exits and live loans. Preserve guest trap discard and failed allocation behavior. |
| P1 | ENF and reusable validation consumers | Canonical protocol grammar and encoding specification | Extend bounded lexer only from documented grammar. Include malformed inputs, precise offsets, exact outcome/error behavior and source/Wasm parity. A* fixed-grid fixture already exists. |
| P2 | Collections and slices | Element ownership and bounds contracts | Primitive List widths, checked subscripting, literals/conversions and indexed operations in separate slices. Owned elements, nested storage, element borrows, capacity APIs, byte/text slicing and generic-length processing require their own scope and loan rules. Preserve fixed-array semantics. |
| P2 | Strings | Valid UTF-8 and bounded view lifetime | Separate raw literals, identifier-only interpolation and formatting, scalar iteration, and text views. No integer String indexing. Check UTF-8 boundaries, exact bytes and owner liveness. |
| P2 | Outcomes and Error | Existing `T?`, `T ! E`, `T ?! E` and embedded-loan checks | Expand local borrowed wrapper assignment/joins before calls, nesting, destructuring or exclusive payloads. Owned ancestor conversion needs a spelling and retained identity through entry metadata. Audit Error message storage/reporting and reference coercion beyond direct calls separately. |
| P2 | Control flow and patterns | Accepted `defaults` direction, proposed syntax for remaining constructs | Defaults only on normal completion. Define `try` behavior before activation, preserve old value on failed assignment if specified. Assess mutable/nested/literal patterns, guards and `is` binding without implicit partial moves. |
| P2 | Values, functions and numeric growth | Separate ownership and syntax choices | Aggregate copy and `swap`, explicit partial moves, additional numeric modes, narrowing/sign changes and additional widths. Function value storable representation and indirect calls precede partial binding, closures or function Lists. Named args must preserve written order if adopted. |
| P2 | CLI, package and artifact work | Accepted manifest direction and explicit byte/ABI contracts | Candidate directory manifest convenience and diagnostics checks first. Implement local dependencies, import selection, cycle detection and bundled vs external artifacts in separate slices. Add deterministic compatibility and failure cases before remote fetching. |
| P3 | Optimization and incremental compilation | Correct baseline plus measurements | Measure allocator splits/coalescing, String representations and compile/run cost. Separate guest representation from Rust compiler text storage. Preserve ownership, UTF-8, trap behavior and outputs. Design stable symbol fingerprints and invalidation before promising an incremental cache. |
| P3 | Broader design and stable distribution | Explicit language and host decisions | User generics, recursive values/indirection, extension/property systems, tasking, parallelism, static storage, host callbacks and stable external ABI/FFI each require a separate specification. Prove compatibility, resource limits and reset/trap policy before exposing persistent host APIs. |

## Evidence map

- [Owned heap and String structs](../design/owned-heap-foundation.md), [struct checkpoints](../design/struct-implementation.md), [outcomes](../design/outcome-implementation.md), [Lists](../design/list-slice.md), [UTF-8](../design/utf8-text-slice.md), [Wasm backend](../design/wasm-backend.md), [artifact output](../design/artifact-output.md), and [ENF fixture](../design/enf-lexer-slice.md) describe current bounds and dependencies.
- [Source audit](#local-only ".local-design/archive/superseded/audit-source-code.md is a local note, not in the repository") and [examples audit](#local-only ".local-design/archive/superseded/audit-examples.md is a local note, not in the repository") are snapshots. The [inventory reconciliation notes](../design/feature-inventory.md#reconciliation-and-decision-gates) retain the dated documentation review findings and point to the current documents. Their 866-test report is historical evidence. [Implementation review](../design/implementation-review.md) has an older recommended sequence followed by fix checkpoints. [Evaluation-order repro](#local-only ".local-design/review-repros/evaluation-order.rs is a local note, not in the repository") is a historical probe. Verify whether a current test already covers any finding before scheduling a fix.
- [Hashing findings](#local-only ".local-design/archive/superseded/experimental-findings.md is a local note, not in the repository") and the [local hashing example](../../examples/apps/hashing/README.md) demonstrate demand for native operations, plus workarounds and known vectors. The manifest-directory failure and absence of generic-length functions and slicing are separate work.
- [Small feature ideas](#local-only ".local-design/developer/Ufak özellikler.md is a local note, not in the repository"), [String optimization ideas](#local-only ".local-design/developer/String optimizasyon.md is a local note, not in the repository"), and [local clarifications](#local-only ".local-design/son-netlestirmeler.md is a local note, not in the repository") provide proposals and context. Primitive iteration, search and bounded explicit `drop` already shipped. Broader versions require separate semantics.
