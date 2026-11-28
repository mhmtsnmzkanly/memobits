# Remaining work and priorities

This document is a planning guide for contributors who are new to Memobits. It
summarizes the work remaining after commit `35d4646` and suggests an order. It
is not a release schedule or a promise that every open idea will be implemented.
The [roadmap](roadmap.md) records project status, the
[feature inventory](design/feature-inventory.md) describes individual features
and decisions, and the [Component Model contract](design/component-model-contract.md)
explains the external interface boundaries.

## Context

Memobits compiles programs to WebAssembly. `mb run` and `mb test` use the Wasmi
engine for development; `mb exec` uses Wasmtime to execute built artifacts.
The project can also build experimental WebAssembly Components, whose public
interfaces use WIT (WebAssembly Interface Types).

The current Component implementation supports scalar application and library
functions. Application entries can also return primitive `T?`, `T ! Error`,
and `T ?! Error` values, with the exact built-in root `Error` for the two
result forms. The CLI console capability is available as a WIT import. These
slices do not establish a stable external ABI or complete the broader Component
Model work.

## How to read the estimates

The priorities below are a suggested technical order, not an accepted project
commitment. **P1** unblocks or strengthens the next Component slices; **P2**
adds broader interoperability and package support; **P3** covers subsequent
platform and language improvements. A user-facing blocker may justify changing
that order.

Estimates are rough **working days for one developer familiar with this
repository**, including implementation, tests, review preparation, and relevant
documentation. They are not derived from measured project velocity. Unsettled
design decisions, review feedback, and defects can increase them. Do not add
the ranges to produce a delivery date: work overlaps, can be split or run in
parallel, and may change after design. Estimates for ownership, packaging, and
LSP are especially uncertain.

## Prioritized work

| Priority | Work | Purpose and benefit | Estimate | Dependencies and risks |
| --- | --- | --- | --- | --- |
| P1 | Nested options and simple composed results | Represent values such as `i32??` at the Component boundary without confusing `None` with `Some(None)`. | 3–6 days | Each option layer needs correct WIT tags, alignment, and source/core/component parity tests. The current standalone application adapter supports only primitive `T?`. |
| P1 | Library option and outcome exports | Let explicitly exported library functions return supported `T?`, `T ! Error`, and `T ?! Error` values to other hosts. | 5–10 days | Unlike the application entry, library exports may have parameters and multiple functions. Export naming, canonical adapters, and unsupported signatures need tests. |
| P1 | Component boundary hardening | Close gaps in WIT name and collision handling, independent type validation, diagnostics, traps, fuel, determinism, and failure atomicity. This makes later mappings safer to build on. | 3–7 days | Some checks already exist; audit coverage first. This does not by itself make the external ABI stable. |
| P2 | WIT `string` mapping | Exchange text across Component boundaries and support more useful host interactions. | 8–15 days | Requires UTF-8 validation, canonical allocation and transfer, post-return cleanup, and tests for leaks, invalid input, and repeated calls. |
| P2 | WIT lists and other aggregates | Exchange lists, tuples, records, and variants instead of restricting external interfaces largely to scalars. | 15–30 days | Split into separately reviewable mappings. Lists need allocation and cleanup; records and variants need visibility, naming, and type-identity rules. Fixed arrays need a representation that preserves their length. |
| P2 | Additional outcome and error forms | Support Unit success payloads and preserve derived Error fields and identity across the Component boundary. | 5–12 days | The derived-error external representation, names, and dynamic identity need a contract before implementation. Do not silently reduce a derived error to its code. |
| P2 | Additional WIT host capabilities — S5-2c | Provide capabilities beyond the existing typed CLI console import. | 3–8 days per capability | The next capabilities and profiles are not selected. Each needs a contract, host implementation, import validation, and source/core/component tests. |
| P2 | Local package dependencies — S5-3 | Allow source packages and local Wasm dependencies, with selected public imports, cycle rejection, and interface checks. | 15–30 days | Package identity, artifact layout, transitive linking, and interface compatibility need decisions. Manifest parsing alone does not provide linking. |
| P3 | Package distribution and reproducibility | Make separate or bundled dependencies reproducible and distributable, with appropriate identity and integrity checks. | 10–25 days | Depends on S5-3. Identity/version/hash policy, lock and update flow, layout, and transitive policy remain open; remote fetching is deferred. |
| P3 | Language Server Protocol (LSP) — S5-4 | Provide editor diagnostics, go-to-definition, and completion. | 10–20 days for a bounded initial version | Define transport, project behavior, completion scope, and whether incremental analysis is included. A fuller implementation may take longer. |
| P3 | Known language and ownership gaps | Address concrete limitations such as whole `share fn` parameter reassignment, moving owner fields, certain nested `Box` patterns, and the `array<string, N>` field IR failure. | 1–8 days per slice | Prioritize by user impact. Ownership changes need focused move, loan, cleanup, and regression tests. |
| P3 | Language ergonomics and tooling | Consider explicit generic call arguments, more patterns and numeric helpers, interpolation formats, and formatter line breaking. | 2–10 days per slice | Some behaviors and syntax are still open proposals; decide their contracts before implementing them. |

## Suggested sequence

1. Extend Components in small slices: nested options, library results, and the
   boundary checks required by those changes.
2. Agree on memory ownership and cleanup for external values. Implement `string`
   first, then lists and other aggregates as separate changes.
3. Settle package identity and local linking, then implement local dependencies.
   Treat distribution and remote fetching as later work.
4. Define a bounded LSP and deliver diagnostics, navigation, and completion.
5. Address language bugs and ergonomics alongside these stages when their user
   impact justifies it; they do not all depend on Component or package work.

This ordering is a recommendation. In particular, package support or LSP can be
prioritized earlier if they are more important to current users. Host capabilities
should be chosen from actual use cases rather than implemented speculatively.

## Decisions and verification that apply across slices

- Keep unresolved representations gated. Fixed-length arrays, recursive values,
  functions, and borrowed/shared references need explicit external contracts;
  WIT resources are not automatically equivalent to Memobits ownership or loans.
- Preserve existing behavior when extending an ABI. Compare source, core Wasm,
  and Component execution where all three apply, including failure and cleanup
  paths. Engine parity applies to the supported artifact scope, not every possible
  WebAssembly proposal.
- When changing a supported language feature, update and run the executable guide
  in `examples/guide/` as required by [AGENTS.md](../AGENTS.md). Record actual
  test results rather than treating an older count as current evidence.
- Keep the existing bounded console integration distinct from additional WIT host
  capabilities. Broader WASI support is not implied by that integration.
