# Memobits roadmap and status

This page records completed work and the next development stages.
Binding language rules live in [design/decisions.md](design/decisions.md); the
feature catalog is [design/feature-inventory.md](design/feature-inventory.md).

## Completed

| Stage | Contents |
| --- | --- |
| Launch manifest | S1/S2, N1–N4, M1, I1, G1, G2, OP1, D1, D2, D3, C1, H1 ([manifest](design/launch-manifest.md), [report](history/launch-report-2026-11-23.md)) |
| Spelling | `bool`, `char`, `array<T, N>`, `T?`, `T ! E`, `T ?! E`; old spellings rejected; nested patterns |
| Stage 2 | `test fn` / `assert` / `mb test`; alloc layer (`use alloc::List;`, `[build] alloc`); owned elements in arrays and Lists; `replace` / `swap`; owner cleanup |
| Stage 3 | owner `if`/`match` values, `try … else`, range loops, string interpolation (incl. floats), `const`, integer APIs for all widths, literal/constant/or patterns and guards, `~`, `Self` |
| Stage 4 | function values, anonymous functions, `borrow fn` / `share fn` closures, owned closures, `var fn`, multi-parameter generics with `where`, method generics, `Box<T>` with iterative release, whole-owner reassignment |
| Backend | size-class guest allocator |
| Stage 5 step 1 | `mb fmt` |
| Stage 5 step 2a | `mb exec` for core Wasm via Wasmtime; Wasmi remains the `run`/`test` engine |
| Stage 5 step 2b, first slice | Scalar application and library components with Wasmtime execution; aggregate mappings remain gated |

Verification at pause: 1,615 workspace tests passing, 0 failing; every
example passes `mb check`, `mb test` and `mb fmt --check`; the guide returns
`Result: Ok(i32(42))` from source and standalone Wasm with empty stderr.

## Next: Stage 5 (outside world)

1. **S5-2b/c Component Model** — see the 2026-11-26 decision in
   [design/decisions.md](design/decisions.md) and the
   [component interface design](design/component-model-contract.md). Scalar
   components and the WIT console import are implemented; aggregate mappings,
   other capabilities and broader Component Model support remain open.
2. **S5-3 packages** — dependencies in `project.toml`, package identity,
   cross-package extensions (see PKG-03/PKG-04 in the inventory).
3. **S5-4 LSP** — diagnostics, go-to-definition, completion.

## Known open items

- `share fn` parameters cannot be reassigned as a whole.
- No explicit call-site type arguments (`f<i32>(x)`); no generic methods in
  interface declarations; nested associated projections.
- A struct with an `array<string, N>` field built from a named array local
  fails IR validation; owner fields cannot be moved out of `self`.
- Consuming nested patterns through a `Box` payload; `var fn` values held in
  enum payloads cannot be called through a match binding.
- `@` bindings, struct/float/range patterns; format specifiers in
  interpolation; `overflowing_*`, `pow`, `abs`, rotates, bit counts.
- `mb fmt` does not break method chains or long string literals.

## How work was done

Each step had an explicit plan, was implemented with focused and capped-memory
tests, verified against the previous build with
[tools/equivalence.sh](tools/equivalence.sh) where behavior had to be
preserved, and committed only after a full green workspace run. The working
log is [history/development-log.md](history/development-log.md) and the
detailed per-step record is [history/launch-progress.md](history/launch-progress.md).
