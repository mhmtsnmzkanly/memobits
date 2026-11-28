# Component Model interface contract for S5-2b

Status: implementation in progress, 2026-11-27. An experimental
scalar/Unit application component, application components returning
`T ! Error` or `T ?! Error` for bool, char, integer or float `T` with exact root
`Error`, and a scalar library component can
be built; this is not yet the complete S5-2b
contract. Recognized compiler-generated checked traps and stack exhaustion use
the faulting core module's trap metadata and instruction; ambiguous or nested
component traps retain the generic engine diagnostic. The
[engine decision](decisions.md#execution-engines-and-the-component-model-2026-11-26-user-decision-not-implemented-yet)
selects WIT and the overall type mappings. This document proposes the boundaries
and defaults needed to implement them; it does not silently promote unresolved
language or package decisions to accepted contracts.

## Current boundary

`mb build` emits a core module. Application `main` is a zero-argument export;
scalar library functions are exported under manifest `[export]` aliases. A
primitive-success application outcome uses a private entry adapter and metadata.
Other aggregate exports are currently gated. That private format is not a WIT
or canonical ABI contract: a Component Model boundary needs its own validated
adapter, rather than treating the private entry result as a canonical result.
See [artifact output](artifact-output.md) and [outcome implementation](outcome-implementation.md).

## WIT type mapping and boundaries

The accepted directions apply to fully instantiated, externally representable
values. The table distinguishes a mapping target from support in the first
implementation slice.

| Memobits source type | WIT target | Proposed initial boundary |
| --- | --- | --- |
| `bool`, `char` | `bool`, `char` | Scalar values; reject invalid Unicode scalar values at a boundary. |
| `u8`–`u64`, `i8`–`i64` | `u8`–`u64`, `s8`–`s64` | Preserve width and signedness, including narrow integer validation. |
| `f32`, `f64` | `f32`, `f64` | Preserve the Component Model's floating-point semantics. Do not promise NaN payload identity without a separate contract. |
| Unit function result | No WIT result | Unit parameters or stored Unit values require an explicit representation decision; reject them initially. |
| `string` | `string` | UTF-8 value with canonical ABI validation and transfer; enable only after allocation and cleanup rules are tested. |
| `List<T>` | `list<T>` | Element mapping must itself be supported; enable only after ownership and allocation tests. |
| `T?` | `option<T>` | Preserve `Some`/`None`; do not assume internal tag or payload layout matches the canonical ABI. |
| `T ! E`, `T ?! E` | `result<T, E>`, `result<option<T>, E>` | Application outcomes with bool, char, integer or float `T` and exact root `Error` are supported. Derived errors, other payloads and library outcomes remain gated. Returned `Err` is not a trap. |
| Tuple | `tuple<...>` | Preserve element order. Source tuple labels do not create WIT fields. |
| Struct or structural record | Named WIT `record` | Preserve fields and mapped names. Open only for externally visible fields and types with an agreed identity and complete conversion. |
| Enum | Named WIT `variant` | Preserve case order, case names and payloads; do not infer a host ABI from internal discriminants. |
| `array<T, N>` | Unresolved | Do not silently map to variable-length `list<T>`: that erases `N`. Keep exports gated until a portable fixed-length representation and validation are chosen. |
| `Box<T>`, recursive types, functions/closures, `borrow`/`share` values | Unresolved | Gate at the boundary. WIT resources are not automatically equivalent to Memobits `Box` or lexical loans. |

`T ?! E` is a result whose success is optional; `Ok(None)` and `Err` stay
distinct. Generic declarations are not exported as polymorphic WIT functions:
only a supported concrete instantiation can be considered, after an explicit
export and naming rule exists. Unsupported type combinations must fail with a
source-located diagnostic; do not emit a lossy interface or fall back to the
private core ABI.

## World and export proposal

Start with an import-free application world whose single function corresponds
to the configured application entry, with the external name `main`. It is a
plain WIT function, not an implied `wasi:cli/run` world or a promise of WASI
imports. A scalar example is:

```wit
package memobits:generated;

world application {
    export main: func() -> s32;
}
```

The experimental executable vertical slice covers zero-argument application
entries with scalar, Unit or supported `T ! Error` / `T ?! Error` results. A component validator and an
independent WIT decoder check the actual export and type, and `mb exec` invokes
it for comparison with core Wasm.
`mb run` and `mb test` continue to use Wasmi; `mb exec` uses Wasmtime. A
component without a supported `main`, with a wrong signature, or supplied to
an unsupported command must produce a clear error before guest execution.

For libraries, the existing manifest export table selects functions; public
visibility alone does not add exports. Scalar owned parameters and scalar or
Unit results are supported, with deterministic WIT names and ordering. A host
can call parameterized exports; `mb exec` currently calls zero-argument exports
only. Type exports and unsupported signatures remain gated. Application and library selection, export aliases, visibility,
and failure atomicity must continue to follow the existing artifact contract.
The world name and package above are illustrative: the component currently
contains an inspectable function type but does not encode a named WIT package
or world. These names do not establish a package-identity, versioning,
registry, or stability policy. Do not derive a
public package identity from an unchecked manifest string. Multiple artifacts
or sidecars need an explicit output and atomicity contract before shipping.
The initial output is one component file; its WIT world must be inspectable
from the component. No standalone `.wit` sidecar is emitted in this slice.

## Names and collisions

The proposed deterministic normalization for generated WIT identifiers is:

1. Accept ASCII letters, digits, `_` and `-`; reject other characters with a
   diagnostic at the originating declaration. Do not transliterate Unicode.
2. Split on underscores and hyphens, lowercase-to-uppercase transitions, and
   before the final capital in an uppercase run followed by lowercase (so
   `HTTPServer`, `http_server` and `http-server` all become `http-server`).
   Lowercase ASCII letters and join non-empty words with one hyphen. Digits
   remain within their word. Reject an empty result or a result whose first
   character is not a letter.
3. Escape a WIT keyword with `%` in WIT source without changing its external
   name. Validate the result against the pinned WIT parser and Component Model
   name rules; reject anything those rules disallow.

Reject collisions after normalization and WIT name equivalence, including
collisions between distinct source identifiers and between exported types or
functions; report both source declarations. Never silently append
order-dependent suffixes or discard an export. Apply the same policy to fields,
cases and parameters in their respective WIT namespaces. Manifest export
aliases are normalized by the same algorithm. WIT package naming and long-term
compatibility are separate from the loader's current opaque package value and
remain S5-3 decisions.

## Canonical ABI and ownership

The component's visible interface is WIT; the lowered core signatures, memory,
string encoding, allocation and cleanup must follow the Component Model
[Canonical ABI](https://github.com/WebAssembly/component-model/blob/main/design/mvp/CanonicalABI.md)
for the chosen toolchain/profile. Internal Memobits layout is an implementation
detail and must not be exposed as canonical layout without a proven adapter.

For owned values crossing the boundary, specify and test which side owns each
allocation at each transition. For lists and strings the implementation must
provide the required memory and reallocation operations and arrange post-return
cleanup where the selected canonical lift requires it. Prove no leaks, double
frees, invalid UTF-8 acceptance, use-after-free or unbounded same-instance
heap growth on successful calls and normal error returns. Define allocation
failure and traps separately: a trap is not an `Err`, and a trapped instance
must not be resumed under the current CLI lifecycle. Do not translate lexical
`borrow` or `share` to component resource handles without a separate lifetime,
identity, mutation and reentrancy contract.

For the outcome boundary, bool, char, integer or float successes and the exact
built-in root `Error` are accepted for both result forms. The optional form
preserves `Ok(Some(value))`, `Ok(None)` and `Err(error)`. Unit successes remain gated. The root error is exposed in the `types` interface as a named `error` record
with one `code: u32` field. The WIT result is `result<T, error>` or
`result<option<T>, error>` for supported primitive `T`. The adapter checks the private concrete identity before removing
that internal word and presenting the code; it rejects a mismatched identity.
It uses the canonical result layout and does not allocate. Repeated calls
repopulate the private return cell before it is lifted. Derived errors and
outcome exports from libraries remain gated: their full fields,
dynamic identity and stable external names need a separate contract. Do not
reduce arbitrary derived errors to a code or string.

## Imports, acceptance and implementation sequence

The CLI console capability is represented by WIT interface
`memobits:console/console` with `write-i32: func(value: s32)`. When reachable
core code imports `memobits:console.write_i32`, the component lowers that WIT
function into the core import. The `cli` manifest profile must explicitly enable
the existing typed capability at execution; missing, unknown or mismatched
imports are rejected before guest execution. No other capability or WASI world
is implied. Further host capabilities and profiles require separate contracts.

1. Pin the WIT/Component Model tooling and supported profile; validate the
   proposed application world with that version. Implement deterministic WIT
   generation for scalar and Unit application entries and reject everything
   outside that slice. Test malformed names, unsupported entries, old-artifact
   preservation and deterministic output.
2. Emit and independently validate a component, inspect its world and export
   signature, and exercise the same fixture through source, core Wasm and
   component execution. Test explicit missing exports, invalid components,
   fuel, traps and feature-disabled builds. Do not claim components work until
   `mb exec` actually executes them.
3. Add each aggregate mapping only with the necessary canonical ABI adapter,
   ownership, failure and cleanup tests. Check nested values and returned
   outcomes independently. Keep unsupported references, recursion, fixed arrays
   and Error cases gated until their own contracts are settled.
4. Extend WIT host imports beyond the CLI console as separate S5-2c slices and
   implement package linking as S5-3; neither is required for scalar components.

The [WIT specification](https://github.com/WebAssembly/component-model/blob/main/design/mvp/WIT.md)
defines worlds, functions, names and value types. WIT and the Component Model
continue to evolve: pin a mutually compatible version in the implementation
and do not assume later proposal features, such as fixed-length lists, are
available in the selected baseline.
