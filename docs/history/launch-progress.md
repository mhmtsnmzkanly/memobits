> Historical working document, moved from the local design folder on 2026-11-26.
> This is a dated snapshot, not a current work plan. Its task queues, pending
> items, approval requests, paths, commands, and status describe earlier
> checkpoints; do not treat them as current instructions. Current status is in
> [../design/decisions.md](../design/decisions.md) and status in [../roadmap.md](../roadmap.md).

# Launch progress record

Starting checkout: `113ec0932ad3a014f9a0afbe783dafffc93dd34b`.

Starting working tree already contained the S1/S2/N1–N3 changes and protected dirty files. Protected fixture hashes recorded at continuation:

- `README.md`: `284197d1f6652c712e66a04decd993af0790468fec3454b8d9367ccb2c8f7fca`
- calculator README: `a960ca4be560b9186dc4045f6af118766680c33a16909e10afe14de11caa5575`
- computation README: `d4ac92f277f385cea18b61610cdcd17faa02c99a4362115dcb456a7387f8b0f4`
- hashing README: `f2b32b32bd63d5aade2e9f626a720d38bce8840f76fb6efac7e60ef31137c843`
- strings README: `4fad0ec6f89f1058ac3a561352cf2971e5e196190547a9ab75c63b40e7220b9f`
- existing hashing Wasm artifact: `dc8ae32371a83445fd25c444b5b488587e5c973ceaaef160f271c1366afd459b`

## Numeric consumer verification

Copied only the hashing `project.toml` and `.mb` sources into `/tmp/memobits-hashing.*`; the existing `target/` artifact was not copied or modified.

- `cargo build -j1 -p memobits-cli`: passed using existing workspace `target/`.
- Copied unchanged software fallback source run: `Result: Ok(u32(1774777415))`.
- Copied unchanged software fallback standalone Wasm run (`/tmp/memobits-hashing.wasm`, 23,397 bytes): `Result: Ok(u32(1774777415))`.
- In the temporary copy only, replaced `bits.mb` implementations with native casts, wrapping methods, bitwise operators and shifts. Native source run: `Result: Ok(u32(1774777415))`.
- Native temporary standalone Wasm run (`/tmp/memobits-hashing-native.wasm`, 14,889 bytes): `Result: Ok(u32(1774777415))`.

This verifies the existing fallback consumer and the selected native numeric primitives against the same complete internal FNV-1a, DJB2 and Adler-32 known-vector checks. It did not complete N4 at that checkpoint or the overall launch manifest. The protected hashing source and artifact remain unchanged.

## Restart point recorded at the time

The original restart reference was a local-only transfer handoff and is not
part of the repository. It recorded instructions for the 2026-11-23 checkpoint;
it is not a current restart guide.

## N4 seam review (initial state; superseded below)

The supported scalar cast domain is ten types: `i8/i16/i32/i64`, `u8/u16/u32/u64`, and `f32/f64`, so NUM-04 requires 100 explicit source/target pairs. Existing source parsing already produces a general cast node, but activation is currently restricted at all semantic stages:

- `memobits-analysis/src/types.rs`: only `u8 -> u32` type checks.
- `memobits-analysis/src/constants.rs`: cast evaluation returns the unconverted integer operand; constant evaluation currently has no float value representation.
- `memobits-analysis/src/lower.rs`: casts are lowered with hard-coded `Primitive::U32`.
- `memobits-ir/src/lib.rs`: validation accepts only read-only `u8 -> u32`.
- `memobits-wasm/src/lib.rs`: emission currently copies the input lane unchanged.

Therefore, broadening the type checker alone would produce incorrect code. A complete N4 change must carry both source and target types through constant semantics, typed IR validation, and lowering, and then implement Wasm integer extension/truncation, float conversions, and Rust-compatible saturating float-to-integer behavior. This is an implementation dependency map, not a semantic blocker: NUM-04 already specifies behavior.

## N4 implementation checkpoint

Enabled explicit casts across all 100 source/target pairs among the ten supported scalar numeric types. Source and target types now travel through typed IR; type analysis accepts numeric pairs only; lowering preserves both types; IR validation checks the source/target/operand contract; and Wasm emission handles signed/unsigned integer extension and truncation, float conversions, saturating float-to-integer conversion, narrow-target saturation, NaN, and float rounding. Constant analysis now follows integer and floating casts, including nested conversions. `.to_u32()` remains restricted to `u8` and lowers as `u8 as u32`. The delegated cast binding is tighter than multiplicative operators; mixed-type CLI cases exercise it.

Evidence (all Cargo commands were sequential with `-j1` and used the existing workspace target):

- `cargo check -j1 -p memobits-analysis -p memobits-ir -p memobits-wasm`: passed.
- `cargo test -j1 -p memobits-cli --test cli numeric_cast`: 3 passed, 0 failed. This includes all 100 pairs, plus boundary values from each source type checked against all ten targets from runtime parameters and exact Rust cast results; source and standalone Wasm agree. It covers signed minima/maxima, unsigned maxima, fractions, NaN, positive/negative infinity, signed/unsigned saturation, f32 rounding and f64-to-f32 overflow.
- Constant cast-chain and dynamic cast-chain arithmetic both return `i8(0)` from source and `i32(0)` from standalone Wasm. Checked overflow after a cast remains a static `LE001` diagnostic for constant input and a runtime `RE007` trap for dynamic input.
- `cargo test -j1 -p memobits-analysis`: passed.
- `cargo test -j1 -p memobits-ir`: 53 tests passed, 0 failed.
- `cargo test -j1 -p memobits-wasm`: 200 tests passed, 0 failed.
- `cargo build -j1 -p memobits-cli`, guide source run, guide standalone Wasm build/run, `cargo fmt --all -- --check`, and `git diff --check`: passed. Guide source/artifact both printed exactly `Result: Ok(i32(42))`; artifact: `/tmp/memobits-guide-casts.wasm` (73,671 bytes).

The first cast boundary probe showed that Wasm `trunc_sat` to a 32-bit lane followed by narrow signed truncation does not implement Rust's saturation to the narrower target. Added pre-conversion clamping for i8/i16/u8/u16 and reran the matrix successfully. The existing README/example/artifact hashes above still match the continuation baseline. No unrelated example or README was staged; no commits were created because `.git` is read-only.

The launch remains incomplete. Next manifest row is M1 behavior-preserving compiler extraction, subject to the root orchestrator's sequence.

### OP1 user-defined BitAnd slice

Binary `&` now selects compiler-provided `core::ops::BitAnd` for nominal operands. It follows the existing owned receiver/RHS, associated `Rhs`/`Output`, and caller evidence-forwarding path used by `Rem`; primitive `u32 & u32` remains on the existing bitwise path. The language guide demonstrates heterogeneous `MaskLeft & MaskRight -> MaskResult` through a generic `T: BitAnd` function.

- `cargo test -j1 -p memobits-cli --test cli user_defined_bitand_`: 4 passed. Coverage includes heterogeneous source/standalone Wasm execution, wrong RHS, missing and ambiguous implementations, both operand moves, early RHS return, and left-to-right operand effects. Source returns `u32(8)`, `u32(10)`, and `u32(42)`; standalone Wasm returns `i32(8)`, `i32(10)`, and `i32(42)` through the raw scalar entry ABI.
- `cargo test -j1 -p memobits-cli --test cli language_guide_checks_bytes_array_equivalence_in_source_and_wasm`: passed; guide source and standalone Wasm both return `Result: Ok(i32(42))`.
- `cargo test -j1 -p memobits-cli --test cli u32_bitwise_and_shifts_match_source_and_standalone_wasm`: passed, preserving primitive bitwise and shift behavior.

Other OP1 families remain incomplete. This slice does not implement XOR/OR overloads, comparisons, compounds, unary operations, or complete the required audit disposition.

## M1 extraction checkpoint

Created focused private seams without changing public compiler entry points or language behavior:

- `memobits-syntax/src/items.rs`: top-level function/use/type declaration parsing moved from `Parser::item`.
- `memobits-analysis/src/types/{arrays,lists,operations}.rs`: array gates and owned-position propagation, List receiver/get/mutation checks, and numeric operator type categories.
- `memobits-analysis/src/lower/{arrays,operations}.rs`: fixed-array repetition lowering and source-to-IR operator/cast-target mapping.
- `memobits-wasm/src/{arrays,operations}.rs`: inline array-cell lookup/copy and numeric cast instruction emission.

Verification after extraction, serialized with the warm workspace `target/` and `-j1`:

- `cargo check -j1 -p memobits-analysis -p memobits-wasm`: passed.
- `cargo test -j1 -p memobits-analysis`: full crate suite passed after moving `lower_repeat`.
- `cargo test -j1 -p memobits-wasm`: full crate suite passed, including 200 tests.
- `cargo test -j1 -p memobits-syntax`: 29 tests passed (2 error derivation and 27 parser tests).
- `cargo test -j1 -p memobits-cli --test cli language_guide_checks_bytes_array_equivalence_in_source_and_wasm`: 1 passed; guide source and standalone Wasm agree on `Result: Ok(i32(42))`.
- `cargo test -j1 -p memobits-cli --test cli numeric_cast`: 3 passed, including 100-pair cast coverage.
- `cargo fmt --all -- --check` and `git diff --check`: passed.

This is the current M1 extraction boundary. The launch remains incomplete. Proceed to I1 interface/extension syntax and lookup unless orchestration changes the order. No commits were made; `.git` is read-only.

## I1 partial checkpoint

Implemented a resolver-level direct module edge using the delegated `use module;` spelling. A one-segment use that names a project module loads it and is represented as a module edge rather than a symbol alias; a normal symbol import loads a module without creating that edge. Existing prelude aliases continue to load names without creating direct edges.

- Resolver tests: `cargo test -j1 -p memobits-resolve` passed, 7 unit tests and 15 root tests. Added tests cover module-only edge behavior and symbol-import non-activation.
- Added `examples/projects/module-imports/` and a guide pointer. CLI source and standalone Wasm runs both produced `Result: i32(42)`; artifact `/tmp/module-imports.wasm`.
- Added parser-only forms for `pub interface Draw { fn draw(borrow self) -> i32; }` and `extend Point of Draw { fn draw(borrow self) -> i32 { ... } }`. Parser test passes as part of `cargo test -j1 -p memobits-syntax` (28 parser tests plus 2 derivation tests).
- Resolver/name analysis currently treats interfaces as named declarations. `cargo check -j1 -p memobits-analysis` and `cargo check -j1 --workspace` pass with extension declarations ignored by executable analysis.

I1 is not complete: postfix `of` selection, extension candidate discovery and visibility/ambiguity checks, interface signature conformance, extension body checking/lowering, and end-to-end selector execution are still absent. Parser-only interface/extension syntax is not yet a supported executable feature. Keep this row open; do not claim full launch completion. The immediate next task is to add the selector AST/parser and trace it through resolution, type checking, lowering, IR and Wasm, or record a concrete architecture blocker if the accepted contracts cannot be implemented safely.

### I1 selector parser update

Added `interface: Option<Type>` to call syntax nodes and parse the accepted `call() of module::Interface` suffix, including grouping and a subsequent `.inspect()` chain. Syntax tests cover declaration receiver mode, extension method bodies, explicit qualified selection and grouped chaining. Selector metadata is traversed by resolver/name analysis. To prevent silent normal-call dispatch, analysis currently rejects a selected call with `TE007` and the explicit message `explicit interface selection is parsed but not yet supported by call analysis`.

- `cargo test -j1 -p memobits-syntax`: passed, 29 parser + 2 derivation tests.
- `cargo test -j1 -p memobits-cli --test cli explicit_interface_selector_is_rejected_until_dispatch_is_implemented`: passed; confirms a selected call is rejected with the explicit gate.
- `cargo check -j1 --workspace`, `cargo fmt --all -- --check`, and `git diff --check`: passed.

This still does not satisfy full I1. The syntax AST is in place, but there is no extension symbol table, direct-import candidate lookup, interface method signature comparison, extension method body checking, ambiguity/privacy diagnostics or selected-call lowering. Do not remove the type-analysis gate until those pieces select a unique public candidate and the same selection identity reaches Wasm code generation. Next implementation work is the extension candidate/type metadata model across resolution and analysis, not another parser expansion.

### I1 resolver conformance update

Resolver/name checking now validates local interface and extension method names and compares receiver access, explicit parameter count/types, and result type. It checks extension target/interface types, checks interface method signatures, and checks extension method bodies with `self` and explicit parameters in scope. New resolver tests cover a valid local extension, an unknown interface signature type, and a mismatched implementation signature. `cargo test -j1 -p memobits-resolve` passes (7 unit + 18 root tests); `cargo fmt --all -- --check` and `git diff --check` pass.

Remaining I1 work: interface-constrained calls are still gated with TE007; local conformance check does not yet include imported interfaces; extension visibility and direct module edge filtering are not used in candidate lookup; no ambiguity diagnostic exists; extension bodies are name-checked but not typechecked/lowered; no selector reaches executable IR/Wasm. This is an explicit partial checkpoint, not an I1 completion.

### I1 public signature visibility update

Resolver public-signature checking now includes public interface methods and public extension target/interface/method signatures. Added a regression ensuring a public interface cannot expose a module-private type. `cargo test -j1 -p memobits-resolve` passes (7 unit +19 root tests); the explicit-selector TE007 CLI test passes; formatting and diff checks pass.

The actual call selection/runtime path remains gated. No candidate discovery or ambiguity algorithm is implemented yet, so current evidence only validates imports as separate edges, declaration/name/conformance behavior, and the explicit rejection boundary.

### I1 candidate-scope API checkpoint

`Resolution` now carries the source package identity and exposes `extension_candidates(module)`: it returns local declarations and declarations from directly imported modules only, filters imported candidates to `pub`, and carries module/package identity plus source span and signatures for later disambiguation. The resolver test verifies that the direct module edge sees only its public extension, the declaring module sees both local public/private candidates (with distinct declaration spans), symbol import sees none, a transitive module load sees none, and a prelude alias loads the module without activating extensions.

- `cargo test -j1 -p memobits-resolve`: 7 unit and 20 roots passed.
- `cargo check -j1 --workspace`, formatting and diff checks passed.

The candidate API is not yet called by analysis. Selected calls still fail TE007. Therefore ambiguity diagnostics, receiver-mode checking and selected function identity propagation to IR/Wasm remain outstanding; the row stays partial.

### I1 conformance review fixes (current)

Unified extension/interface signature conformance in `check_extension_conformance`; removed the earlier local-only comparison path. Signature type identity follows transparent aliases through module imports and nested alias declarations, so equivalent local and cross-module signatures compare by their underlying type. Generic/template arguments are canonicalized recursively; repeated aliases in sibling arguments such as `Result<Number, Number>` are covered. Added regressions for local and cross-module aliases. Extension constraints now reject primitives and template types (for example `i32` and `List<i32>`) with ME008, and unresolved constraints also report ME008 instead of being silently ignored.

- `cargo test -j1 -p memobits-resolve`: 7 unit +25 root tests passed, including local/cross-module alias conformance, `i32` and `List<i32>` rejection, nominal-type rejection, and prior import/access/mutability cases.
- `cargo test -j1 -p memobits-cli --test cli`: 152 passed, 0 failed after the final template-root normalization fix, including selected extension calls, imported public extensions, ambiguity/privacy diagnostics, ownership modes, and source/Wasm parity.
- `cargo check -j1 -p memobits-resolve`, `cargo fmt --all`, and `git diff --check` passed. The resolver suite passed again after the final fix (7 unit +25 root tests).

I1 remains open pending broader review/manifest work; these fixes do not change that status. No commit or staging was attempted because `.git` is read-only.

### I1 guide/docs and runtime verification

Updated the runnable guide comments with the multi-module project setup, grouped symbol-import behavior, direct-module activation rule, and current external-package limit. Updated the project README, root README and accepted decisions so they no longer say extension definitions are unspecified; all point to the checked multi-module example.

- `cargo build -j1 -p memobits-cli`: passed.
- `target/debug/mb run --project examples/projects/module-imports/project.toml`: `Result: i32(42)`.
- Standalone module-import Wasm `/tmp/module-imports-i1.wasm` (884 bytes): `Result: i32(42)`.
- Guide source run: `Result: Ok(i32(42))`.
- Standalone guide Wasm `/tmp/memobits-guide-i1.wasm` (73,671 bytes): `Result: Ok(i32(42))`.
- I1 negative coverage remains in resolver and CLI tests: ME008 for primitive/template/nominal/non-interface constraints, plus private, missing, ambiguous and inactive extension diagnostics. Latest suites: resolver 7 unit +25 roots; CLI 152 tests passed.

I1 executable guide and docs are now aligned with the demonstrated local-module contract. No commit or staging was attempted because `.git` is read-only.

### G1 generic nominal constructor checkpoint

Generic named structs already construct concrete applications using the generic TypeTable identities. Existing CLI coverage verifies `Box<i32>` and `Box<u32>`, and `Buffer<u8, 1>` with a substituted fixed-array field in source and standalone Wasm. Added user enum support for contextual constructors and patterns: when the expected value is `Maybe<i32>`, `Maybe::Some(...)` and `Maybe::None` resolve against that concrete specialization. Candidate identity is checked against the generic declaration key, so a different enum cannot borrow the expected type's variant names.

- `cargo test -j1 -p memobits-cli --test cli generic_nominal_`: 3 passed, including generic struct specialization/mismatch and enum construction/matching at `Maybe<i32>` and `Maybe<u32>`; source and standalone Wasm both return `Result: i32(42)`.
- Updated the language guide with generic struct, const-array, and contextual generic enum examples. `cargo test -j1 -p memobits-cli --test cli language_guide_checks_bytes_array_equivalence_in_source_and_wasm`: passed; source and standalone Wasm remain `Result: Ok(i32(42))`.
- Generic function identity probe initially demonstrated the current safe gate: `fn identity<T>(value: T) -> T { value }` fails with `TE001` (`unsupported or unresolved type 'T'`). A syntax-driven monomorphization experiment was removed after review identified risks around contextual types, aliases, mixed/nested calls, identity keys, and public API names. No experimental runtime behavior remains. `generic_identity_function_is_not_silently_monomorphized` passes by confirming the explicit current rejection.
- `cargo fmt --all` and `git diff --check` pass after the enum and guide changes.

G1 remains partial. Generic function type inference/specialization and caller-selected/forwarded interface evidence are not implemented. Generic enum constructors without an expected concrete enum type also remain unsupported. Continue with semantic type inference/specialization or preserve the explicit generic-function rejection gate; do not infer concrete types solely from literal syntax.

### G1 generic-function implementation plan

The current pipeline checks one shared `FunctionFacts` record per declared syntax function. `check_resolved_mode` in `memobits-analysis/src/types.rs` first builds concrete signatures with `type_path`, then checks every body once; unresolved `T` therefore stops at TE001. `FunctionFacts.id` and `PathUse::Function` carry a concrete `FunctionId`, and `memobits-analysis/src/lower.rs` emits functions from syntax items against those facts. Specializing by rewriting source paths alone would bypass this typed identity and is unsafe.

Implement generic calls as a typed worklist: retain generic declarations as templates separate from callable concrete signatures; type-check actual arguments to semantic `Ty` values and unify those with formal type/const patterns (plus expected result constraints where required); resolve aliases before forming a specialization key; carry selected interface evidence identity in that key; enqueue each distinct specialization and type-check its substituted body to produce fresh `FunctionFacts`/`FunctionId`; bind each call expression to that target identity for lowering. Preserve the declared public API names and avoid literal-text inference. Add recursion/specialization limits with diagnostics. This is an implementation path through the existing checker/lowerer seams, not a syntax-gated blocker; generic function runtime support remains unimplemented.

### G1 const-generic enum payload verification

Extended generic enum runtime coverage with `Packet<const N: u32> [Data(Array<u8, N>)]`. `Packet<1>` and `Packet<3>` construct and match independently specialized payloads, and the CLI test compares source execution with standalone Wasm (`Result: i32(43)`). The runnable language guide now includes contextual `Packet<1>` and `Packet<2>` construction and matching; its source and standalone Wasm parity test still passes (`Result: Ok(i32(42))`).

Negative CLI coverage checks and records exact diagnostics for wrong enum origin (`TE009`), wrong fixed-array payload length (`TE002`), missing payload arity (`TE010`), and an unknown variant (`NE004`). `cargo fmt --all -- --check`, `git diff --check`, and the focused positive/negative CLI tests pass. Generic function specialization/evidence forwarding remain gated; contextual enum construction without an expected type remains unsupported. G1 is still incomplete.

### D3 optional type spelling checkpoint (partial)

Added postfix `T?` as syntax sugar for `Option<T>`. The parser also distinguishes `borrow T?` (borrow access on the outer type) from `(borrow T)?` (`Option<borrow T>`); a parser test verifies both AST shapes. The runnable guide demonstrates `i32?`, contextual `Some`/`None`, and matching. Focused CLI evidence: source and standalone Wasm both return `Result: i32(42)`; wrong payload types report `TE002`, and context-free `None` reports `TE002` with `cannot determine None's outcome type; provide an Option<T> annotation`. The guide source/Wasm test passes (`Result: Ok(i32(42))`), all 34 syntax parser tests pass, and formatting/diff checks pass.

D3 remains partial: no new reference transport is enabled; the accepted borrow forms are syntax-distinct only. Full move/loan behavior for `Option<borrow T>` and legacy migration diagnostics remain open. `Some(expr)` once-only behavior is covered by a counter test in source and Wasm.

Migration diagnostic blocker: the architecture plan says exact legacy Option compatibility is open, while current supported code uses `Option<T>`. The analysis helper assigns `Severity::Error` to diagnostics, and `check_resolved_mode` aborts on any diagnostic; there is no warning output channel on successful `build`/`run`. Breaking `Option<T>` or making a warning fatal would change accepted behavior. Decision needed: preserve silent `Option<T>` compatibility, or add a non-failing warning channel and report `Option<T>` as a migration to `T?`. No policy was inferred.

### D1 bodyless nominal identity checkpoint (partial)

Added `type Name;` declarations as bodyless nominal types, distinct from `type Empty {}`. They can appear in internal function signatures, retain nominal identity during type checking, and cannot be constructed as `Name {}` (`TE023`, `bodyless nominal type 'Token' cannot be constructed`). Passing `Empty {}` where `Token` is expected reports `TE002`, `expected Token, found Empty`. Parser and CLI tests cover the declaration distinction, type identity, and construction gate. The runnable guide includes an unconstructed bodyless handle in an internal signature; its source and standalone Wasm verification remains `Result: Ok(i32(42))`.

D1 was partial at this checkpoint. Its bounded acceptance slice is now implemented; see “D1 bounded structural records and anonymous enums” below. Bodyless values remain unconstructable (`TE023`), generic bodyless types are rejected, and trailing extensions on generic nominal types remain gated with `SE002`.

### D1 inherent extension verification

Added standalone `extend Target { ... }` and trailing `type Target { ... } extend { ... }`/`type Target [ ... ] extend { ... }` parsing. Both forms lower methods to typed function identities and dispatch `value.method(...)` through selected-call facts. Local struct and enum calls, bodyless trailing method checking, and public methods from a directly imported module are covered. A symbol import alone does not activate an external inherent extension; a private direct-module extension is rejected, mismatched receivers do not select it, and duplicate applicable methods report ambiguity.

- Local struct method source and standalone Wasm both return `Result: i32(42)`.
- Directly imported public method source and standalone Wasm both return `Result: i32(42)`.
- The language guide source and standalone Wasm both return `Result: Ok(i32(42))` with a trailing enum method and bodyless trailing method.
- Negative CLI tests verify unknown receiver (TE007), ambiguous inherent method (TE007), inactive symbol-import candidate (TE024 field diagnostic), private candidate (TE007), bodyless construction (TE023), and wrong nominal type (TE002).

At this checkpoint anonymous structural records/enums were still missing. That gap is closed by the later D1 slice below. Generic nominal trailing extensions were still gated at this historical checkpoint; their supported concrete receiver specialization is recorded below.

Visibility regression review fix: imported inherent method candidates now retain and enforce method-level `pub` visibility. A public extension block or public nominal type does not make its private `fn` methods callable from another module. Regressions cover both `pub extend Point { fn hidden ... }` and `pub type Point { ... } extend { fn hidden ... }`; both direct-import calls reject with TE007. Local private methods remain usable in their declaring module.

Post-fix verification: `cargo test -j1 -p memobits-analysis` passed; `cargo test -j1 -p memobits-cli --test cli` passed (168 tests); syntax passed (38 parser + 2 derivation); resolver passed (7 unit + 26 roots); `cargo fmt --all -- --check` and `git diff --check` passed. CLI verification includes guide source and standalone Wasm runs.

### D1 bounded structural records and anonymous enums

D1's acceptance slice covers named nominals with bodyless, empty/field-bearing struct, and enum forms, both with and without trailing inherent extensions. Bodyless nominals remain distinct from empty structs and unconstructable (`TE023`). Inherent extension dispatch works for field-bearing and enum nominals; direct `extend Type { ... }` remains supported. Generic nominal trailing methods specialize by concrete type and const receiver arguments, including nested generic type arguments (WP21).

Anonymous record expressions and type spellings are supported for non-empty named-field shapes. Shape identity ignores field order and requires the exact same labels and types; field initializers still evaluate once in written order. Coverage includes locals, function parameters and expected-type contexts. Empty anonymous records/types remain rejected as ambiguous. Inline anonymous enums support unit and payload variants and are nominal by declaration site, even when two declarations list the same variants. Bare constructors and pattern variants resolve from a unique expected enum, including a local inline annotation; without context they are rejected. Payload type arguments are checked against the selected variant, and pattern slots bind payloads in declaration order. Generic specializations of one inline declaration retain distinct enum identities when their concrete payload types differ. Payload types remain subject to existing ownership gates: reference-bearing payloads are rejected, and Wasm currently rejects enum payload storage containing `String`. Named payload enums and qualified constructors/patterns remain supported.

Focused acceptance coverage includes parser checks for each nominal body form with/without trailing extension; analysis coverage for reordered/exact record shapes and anonymous enum identity; and CLI source/Wasm parity for anonymous records/enums and field-bearing nominal trailing extensions. Standalone local-annotation regressions verify that unit and payload variant names resolve without unrelated declarations. The earlier unit-only D1 checkpoint passed with 1080 workspace tests; that result predates payload-bearing inline enum support.

Payload-bearing inline enums parse as `enum [Variant(T, U), Unit]`, preserve payloads in anonymous enum type facts, and use the existing `EnumNew`, `VariantExtract`, and Wasm enum layout paths. Focused coverage checks multi-payload constructors and patterns, expected-type construction, wrong payload types and arity, distinct declaration-site identity, concrete generic specialization identities, reference-payload rejection, and the existing Wasm `String` payload gate. Generic nominal trailing methods carry owner type/const parameters through parsing and resolution, substitute signatures for each concrete receiver, and lower receiver-specific method bodies and calls. Focused regressions cover multiple type and const instances, mutual method recursion, a method that calls a generic free function, the 256-method specialization diagnostic, and cross-module visibility (public direct imports work; symbol-only, transitive, and private extension access remain rejected). The owner reports the generic D1 focused suite passed **13/13**, the full workspace passed **1092 tests**, and guide source plus standalone Wasm both returned `Result: Ok(i32(42))`. Cargo was not run during this documentation update. Remaining limits are explicit: unbounded polymorphic receiver growth is rejected by the 256-method diagnostic and forwarding a receiver const parameter into a nested nominal argument is unsupported; reference-bearing inline enum payloads are rejected; Wasm String payload storage remains unsupported; empty anonymous record/enum shapes are rejected.

### C1 Unicode scalar literal slice (partial)

Added single-quoted `Char` literals with exactly one Unicode scalar and escapes `\\n`, `\\r`, `\\t`, `\\0`, `\\\\`, and `\\'`. Empty, multi-scalar, newline-containing, and unsupported escape forms report lexical errors. `Char` has a distinct semantic/IR type; Wasm currently stores it as an unsigned 32-bit scalar code point. Internal parameters/results and equality work; `Char` is not an entry ABI scalar. `Char` and `u32` remain distinct, and no arithmetic or ordering operators are enabled.

The language guide checks ASCII, accented and supplementary-plane characters, parameter passing, and supported escapes in source and standalone Wasm. Parser tests check literal decoding and malformed forms; a CLI analysis regression checks `Char`/`u32` mismatch. IR tests reject surrogate-range and above-U+10FFFF Char constants, source surrogate-style escapes are rejected, and the Wasm backend rejects Char ordering even for invalid direct IR. This is only the character-literal foundation of C1: lowercase `string`, scalar traversal/byte length parity, and compatibility migration remain outstanding.

### D2 tuple syntax groundwork (superseded by occurrence-local labels below)

Tuple types now intern as distinct structural identities keyed by ordered element types and lower through the existing aggregate layout. Tuple construction, positional projections, internal arguments/results, and local tuples owning String values are checked and lowered. Source and standalone Wasm tests cover scalar identity forwarding/projection and local String cleanup; reordered elements reject with TE002. The guide includes a checked `(i32, Bool)` internal call.

D2 remains partial: tuple pattern/destructuring is not implemented; owning tuple transport across calls remains under the existing Wasm String-struct transport gate. At this checkpoint, labeled tuple forms were gated pending use-site metadata. The occurrence-local labels checkpoint below supersedes that gate. Positional tuple expressions and types remain enabled. Recursive reference-bearing tuple elements are gated with TE017 before IR lowering, including an annotated `Option<borrow i32>` value.

### D2 occurrence-local tuple labels checkpoint

Enabled labeled tuple types, initializers, and projections using occurrence-local alias metadata. Ordered tuple identity remains based on element types; label names map to slots per type/value occurrence and do not accumulate in shared structural metadata. Lowering consumes checker facts for each projection and maps initializer expressions from written order to destination slots. This avoids the earlier order-dependent behavior from globally unioning aliases.

- `tuple_labels_are_occurrence_local_independently_of_function_order` runs two functions with reversed local label maps in both declaration orders. Each `pair.left` selects that occurrence's own slot; source and standalone Wasm both return `Result: i32(42)`.
- `labeled_tuple_initializer_reorders_written_values_to_local_alias_slots` verifies a labeled initializer with reversed written order in source and standalone Wasm.
- `labeled_tuple_malformed_forms_are_rejected` still rejects mixed labeled/positional initialization, duplicate initializer labels, unknown labels, and duplicate type labels. A prior final case that expected two independent reversed alias maps to conflict was removed because those aliases are occurrence-local by contract.
- `tuple_nested_option_reference_is_gated_before_owner_can_escape` verifies a nested `Option<borrow i32>` cannot enter a tuple. Direct references and other nested loan-bearing aggregates remain gated before IR lowering.

Focused verification: `cargo test -j1 -p memobits-cli --test cli tuple_labels_are_occurrence_local_independently_of_function_order` passed; `cargo test -j1 -p memobits-cli --test cli labeled_tuple_malformed_forms_are_rejected` passed. Guide comments and executable examples now cover label aliases; `docs/design/decisions.md` and the current requirements status were updated. Run the full tuple-filtered CLI group, guide source/standalone Wasm parity, formatter, and diff check before treating this checkpoint as complete. D2 remains partial for tuple patterns/destructuring and owned tuple transport across calls.

### D2 owned tuple transport checkpoint

Named local tuples with direct String fields now move through internal owned parameters and tuple results. Lowering stages heap String tuple elements so early exits release their pending owner, IR ownership facts follow tuple moves through calls and returns, and Wasm clears the caller's moved tuple descriptor after the callee completes. Nominal String-owning structs retain their existing LE900 gate. Arbitrary tuple temporaries containing heap Strings remain gated; tuple patterns/destructuring remain outside this slice.

Verification added: source and standalone Wasm return 42 after an early-returning internal tuple transport; use after move rejects with BE001; nominal String-owning struct transport still rejects with LE900. A Wasm integration test forwards a heap String tuple 12,000 times under a two-page memory cap, including both early and normal callee returns, and passes. Run the full tuple test group, guide source/Wasm parity, formatting and diff checks before treating this checkpoint as complete.

### C1 lowercase `string` spelling checkpoint (partial)

Added lowercase `string` as a builtin type spelling that resolves to the existing `String` semantic type. Legacy `String` source remains accepted, so callers and callees can use either spelling without conversions or changes to ownership, UTF-8 storage, or byte-length behavior. The type name is reserved against user declarations. The runnable guide demonstrates an owned lowercase `string` result consumed by the existing `String`-typed byte-length function.

Verification: `cargo test -j1 -p memobits-cli --test cli language_guide_checks_bytes_array_equivalence_in_source_and_wasm` passed. Direct guide source run returned `Result: Ok(i32(42))`; standalone Wasm `/tmp/memobits-guide-c1-string.wasm` (81,888 bytes) returned the same. `cargo fmt --all` and `git diff --check` passed. Broader C1 migration remains partial; `String` compatibility stays enabled, and this slice does not change the existing scalar-at-byte-offset API or promise general scalar iteration.

### C1 bounded scalar traversal and byte length (pending verification)

The runnable guide now defines `scalar_count` as a source-level traversal over
valid UTF-8. It reads each scalar with the existing byte-offset
`.scalar_at(offset)`, advances by that scalar's UTF-8 width, and counts visited
scalars. Examples compare scalar counts and unchanged `.len()` byte lengths for
empty, ASCII, accented, euro and supplementary-plane text. A focused CLI test
checks the same logic in source and standalone Wasm and moves the owner after
the final borrowed traversal. No compiler intrinsic, iterator API, or allocator
change is introduced. `Bytes<N>` remains a compatibility alias outside the
target core; `Array<T, N>` remains core. Cargo verification was not run by this
implementation owner.

### C1 guide uses the core fixed-byte type (verified)

Migrated the runnable guide's fixed-byte examples from `Bytes<N>` to
`Array<u8, N>` for annotations, borrowed/shared parameters, return values and
iteration. `Bytes<N>` remains mentioned as a compatibility alias outside the
target core. Other fixtures were left unchanged because they exercise the
compatibility spelling or are separate consumers. Using the existing CLI
binary, the guide source and standalone Wasm both returned
`Result: Ok(i32(42))`; diff whitespace checks passed. No Cargo command ran.
This is a guide migration checkpoint, not completion of C1's broader source
migration or compatibility policy.

### C1 `string` interface canonicalization regression

Resolver interface conformance now treats lowercase `string` and legacy `String` as one builtin type, including method parameters and results across imported modules. Both spellings are classified as builtin constraints rather than declared interfaces. A resolver test checks mixed parameter/result spelling in an imported extension; a CLI integration test executes that cross-module extension in source and standalone Wasm, returning `Result: i32(5)`. The resolver negative test confirms `string` cannot be used as an interface constraint. Focused tests, `cargo fmt --all -- --check`, and `git diff --check` pass.

### G1 generic-function specialization checkpoint (partial)

Generic functions now specialize one unconstrained type parameter inferred from a direct owned argument. Additional parameters may use that same `T` or fixed concrete types, and the result must be `T`. Each concrete body is checked and lowered separately; repeated calls reuse the same specialization. Same-module forwarding and same-type recursion work, as do public generic functions imported from another module. Owned `String` arguments transfer through the call and retain normal use-after-move diagnostics. Conflicting inferred types reject with `TE002`; forms outside this subset reject with `TE007`.

CLI coverage verifies Bool/i32 specializations, `choose<T>`, nested forwarding, bounded runtime recursion, conflicting arguments, generic owned String transport and use-after-move, and a public imported generic call. Source and standalone Wasm agree. The runnable language guide documents the supported signature shape and its bounds, const, borrow, and nested-type limitations. Focused commands `cargo test -j1 -p memobits-cli --test cli generic_functions_` and `cargo test -j1 -p memobits-cli --test cli language_guide_checks_bytes_array_equivalence_in_source_and_wasm` pass. This does not complete G1: const/type forwarding, constraints/evidence, and unbounded specialization diagnosis remain outside this slice.

Specialization checking now reconstructs the declaring module's lexical function environment, including local names, explicit `use` aliases, and manifest prelude aliases. A CLI test checks a generic wrapper that calls an imported generic alias and a prelude-imported ordinary function; source and standalone Wasm both return 42.

### G1 generic array-function const forwarding checkpoint (partial)

Generic functions now support one unconstrained type parameter `T` and one `u32` const parameter `N` when the inferred owned argument and result use the direct `Array<T, N>` shape. Calls infer `T` and `N` from the checked semantic `Ty::Array` (element type and length), form a concrete signature, and key specializations by that signature. Specialized bodies receive both substitutions, so a generic wrapper can forward an array through another generic function. Other compound patterns, bounds and borrowed parameters remain gated.

CLI coverage specializes two lengths and element values through nested `relay_array` and `echo_array` calls; source and standalone Wasm both return `Result: i32(42)`. A conflicting second array length rejects with TE002. The runnable guide documents the supported direct array shape and executes it. Focused positive, negative, and language-guide source/Wasm parity tests pass; `cargo check -j1 -p memobits-analysis`, formatting, and `git diff --check` pass. G1 remains partial: other compound patterns and generic const forms outside `Array<T, N>` are not implemented.

### G1 caller-selected interface evidence checkpoint (partial)

Generic functions now support one owned direct `T` parameter with at most one interface `where` bound and a fixed non-generic result. At the generic call site, the checker selects the unique visible extension candidate for the concrete `T` and interface from that caller's active extension scope. A nested constrained generic call forwards the existing evidence rather than resolving it in the declaring module. Evidence identity is the candidate declaration module/span and is included in the specialization cache key, so two caller scopes can instantiate the same generic function and concrete type with different implementations. The generic body must explicitly select the bounded method with `of Interface`.

The CLI tests cover nested same-module forwarding, two separate callers with different local implementations for the same shared type/interface, missing evidence, ambiguous evidence, and source/standalone Wasm parity (`Result: i32(42)`). The runnable guide includes the bounded form; its source/Wasm test also passes. `cargo check -j1 -p memobits-analysis`, the three focused generic evidence CLI tests, `cargo fmt --all -- --check`, and `git diff --check` pass. G1 is still partial: generic type/const forwarding combined with evidence, multiple bounds, compound/borrowed generic parameters, and unbounded specialization diagnostics remain open.

Reviewer follow-up preserves written argument checking order when the inference argument is not first. Earlier generic-shaped arguments are checked without unresolved expectations and then validated against the concrete signature; fixed arguments retain contextual checking. `Error`/`Never` at the inference argument returns without an extra inference diagnostic. Source/Wasm order coverage returns 42, a use-after-move case reports BE001, and an invalid inference expression produces no redundant generic inference message. All focused generic tests and formatting/diff checks pass.

The `Never` case uses an expected result type to select the generic specialization, records the specialized function path, and returns `Never` from the call because argument evaluation diverges. A CLI regression verifies `identity({ return 42; 1 })` returns 42 in source and standalone Wasm; without an expected result type, inference reports TE002 with a specific context requirement. This avoids the previous lowering panic and preserves ordinary call divergence behavior.

### G2 same-type owned Add pilot

Binary `+` now selects a visible implementation of the compiler-provided `core::ops::Add` interface for a matching nominal operand type. The resolver exposes its declaration through a Rust-owned virtual core module with `Self` substituted by the implementing target during conformance checks. User extensions select it with `use core::ops::Add`. The pilot requires an owned receiver, one owned right operand of the same type, and a same-type result; lowering calls the selected implementation directly after evaluating/capturing operands in written order. A generic `T: Add` function can use `+` and forwards the caller-selected same-type evidence; source and standalone Wasm both return 42. Primitive numeric `+` remains on its existing checked path. Other operators, heterogeneous operands, associated `Rhs`/`Output`, and broader overload behavior remain gated. The guide demonstrates the pilot with `AddPoint`.

CLI coverage verifies source and standalone Wasm return 42, a directly imported module's distinct `other::Add` does not shadow the canonical interface, a local interface named `Add` cannot activate operator dispatch, symbol-only/non-direct extensions are inactive, and private extensions are rejected. A missing implementation rejects with TE007 (`no visible Add implementation for this operand type`); a malformed implementation rejects through interface conformance. Redeclaring `core::ops` is rejected as a reserved module collision. Focused Add and guide tests pass; G2 and OP1 remain incomplete.

### G2 associated Rhs/Output heterogeneous Add slice

Interfaces can declare `type Rhs;` and `type Output;`; an interface extension binds them with `type Rhs = T;` and `type Output = U;`. Resolver conformance rejects missing, duplicate, and undeclared bindings and substitutes associated names in required method signatures. The compiler-provided `core::ops::Add` now uses those declarations. User `+` checks an owned right operand against the selected method's concrete `Rhs` and returns its concrete `Output`, allowing distinct nominal input and result types. A constrained `T: Add` function forwards the caller-selected implementation, and separate callers with distinct implementations of the same concrete receiver produce their own output. The runnable guide demonstrates `AddPoint + AddRight -> AddResult` through a generic `T: Add` function. Primitive numeric `+` remains on the checked path.

CLI tests verify the heterogeneous generic case returns `Result: i32(42)` in source and standalone Wasm, exact `Output` annotation, distinct caller evidence, wrong RHS rejection (TE007), missing `Output` binding (ME005), wrong method signature (ME005), and an unresolved `T::Output` projection (NE008). Parser and resolver tests cover the accepted syntax and conformance. The focused parser, resolver, Add, heterogeneous Add, and guide tests pass. This is a bounded G2 case: associated projections are rejected when unresolved; generic functions still use a fixed RHS and output type, and OP1's other operator families remain outstanding.

### OP1 user-defined multiplication slice

Binary `*` now selects a visible implementation of compiler-provided `core::ops::Mul` for nominal operands. `Mul` follows the existing associated `Rhs`/`Output` and constrained evidence-forwarding contract used by `Sub`: an owned receiver and owned RHS are passed to the selected method, which returns its declared output. Primitive numeric multiplication retains its checked built-in path. The runnable guide demonstrates heterogeneous `MulLeft * MulRight -> MulResult` through a generic `T: Mul` function.

`cargo test -j1 -p memobits-cli --test cli user_defined_mul_` passes all five Mul tests: heterogeneous generic source/Wasm parity (`Result: i32(42)`), wrong RHS, missing/inactive/ambiguous implementations, owned operand moves, and RHS early-return cleanup/source/Wasm parity. `cargo test -j1 -p memobits-wasm --test backend checked_mul_division_negation_and_remainder_cover_boundaries` passes, including checked primitive multiplication overflow and valid multiplication boundaries. The guide source/Wasm test passes (`Result: Ok(i32(42))`); `git diff --check` passes. The added test block is rustfmt formatted. A repository-wide `cargo fmt --all -- --check` still reports pre-existing formatting differences across other dirty files; no unrelated formatter rewrite was applied. Other operator families in OP1 remain incomplete.

### OP1 user-defined division slice

Binary `/` now selects the compiler-provided `core::ops::Div` for nominal operands, using the established owned receiver/RHS, associated `Rhs`/`Output`, and caller evidence-forwarding path. The generic operator checker infers heterogeneous RHS types for division, while array arithmetic remains explicitly gated and primitive numeric `/` remains on the existing checked path. The language guide demonstrates `DivLeft / DivRight -> DivResult` through a generic `T: Div` function.

`cargo test -j1 -p memobits-cli --test cli user_defined_div_` passes five tests: heterogeneous generic source/Wasm parity (`Result: i32(42)`), wrong RHS, missing/inactive/ambiguous implementations, both owned operand moves, and RHS early-return source/Wasm parity. The guide source run returns `Result: Ok(i32(42))`; standalone Wasm artifact `/tmp/memobits-guide-div.wasm` returns the same. `cargo test -j1 -p memobits-wasm --test backend checked_mul_division_negation_and_remainder_cover_boundaries` passes, confirming primitive division by zero and signed MIN/-1 still trap. Remaining OP1 operator families are incomplete.

### OP1 user-defined remainder slice

Binary `%` now selects compiler-provided `core::ops::Rem` for nominal operands, using the established owned receiver/RHS, associated `Rhs`/`Output`, and caller evidence-forwarding path. Primitive numeric remainder remains on the built-in checked path; the new selection applies only to struct/enum operands. The runnable guide demonstrates heterogeneous `RemLeft % RemRight -> RemResult` through a generic `T: Rem` function.

`cargo test -j1 -p memobits-cli --test cli user_defined_rem_` passes all five Rem tests: heterogeneous generic source/Wasm parity (`Result: i32(0)` for `84 % 2`), wrong RHS, missing/inactive/ambiguous implementations, both owned operand moves, and RHS early-return source/Wasm parity. The guide source/Wasm test passes (`Result: Ok(i32(42))`); primitive remainder tests preserve `i32` `17 % 5 == 2`, dynamic `% 0` traps, and signed MIN % -1 returns zero. Remaining OP1 operator families are incomplete.

### OP1 user-defined bitwise OR slice

Binary `|` now selects compiler-provided `core::ops::BitOr` for nominal operands, with owned receiver/RHS, associated `Rhs`/`Output`, and constrained evidence forwarding. The heterogeneous generic guide example merges `MergeLeft | MergeRight` into `MergeResult`; primitive `u32 | u32` remains on the built-in path. The CLI tests cover heterogeneous generic output and standalone Wasm parity, wrong RHS, missing/inactive/ambiguous implementation selection, moves of either operand, RHS early return, and left-to-right evaluation. `cargo test -j1 -p memobits-cli --test cli user_defined_bitor_ -- --test-threads=1` passes all four tests. The guide source/Wasm test and `u32_bitwise_and_shifts_match_source_and_standalone_wasm` pass. The first parallel-filtered run hit stale temporary fixture directories (`AlreadyExists`), so this test filter was rerun serially. `git diff --check` passes. `cargo fmt --all -- --check` still reports formatting differences in other dirty code and unrelated portions of the touched Rust files; no broad reformat was applied. Other OP1 operator families remain incomplete.


### OP1 user-defined bitwise XOR slice

Binary `^` now selects compiler-provided `core::ops::BitXor` for nominal operands, with owned receiver/RHS, associated `Rhs`/`Output`, and constrained evidence forwarding. Primitive `u32 ^ u32` retains its existing per-bit path. The runnable guide demonstrates heterogeneous `XorLeft ^ XorRight -> XorResult` through a generic `T: BitXor` function.

The `user_defined_bitxor_` CLI tests pass (5/5) and cover heterogeneous generic source and standalone Wasm parity (`u32(6)` / raw Wasm `i32(6)`), wrong RHS, missing/inactive/ambiguous implementation selection, both operand moves (with an explicit RHS move-after-use regression), RHS early return (`42` in source and artifact), and left-to-right operand effects. `language_guide_checks_bytes_array_equivalence_in_source_and_wasm` passes with the guide check returning `Ok(i32(42))`; `u32_bitwise_and_shifts_match_source_and_standalone_wasm` passes and covers primitive XOR method/operator precedence and parity. `git diff --check` passes. `cargo fmt --all -- --check` still reports inherited formatting differences in dirty Rust code, including elsewhere in the touched files; no broad reformat was applied. Comparisons, compounds and unary operations remain gated.

`core::ops::Shr` is now available for user-defined `>>` on nominal types. Selection follows the `Shl` owned receiver/RHS model, including heterogeneous `T::Rhs` / `T::Output` forwarding, with primitive `u32` shifts remaining on their checked built-in path. Five serialized CLI tests cover source and standalone Wasm parity, wrong RHS, missing/inactive/ambiguous implementations, moves of both operands, RHS early return, and left-to-right evaluation. The `language-guide` now demonstrates generic `Shr`; its source/Wasm guide test passes. The primitive shift source/Wasm boundary test passes. All targeted tests were run with `cargo -j1`; no commit was created.

### OP1 nominal equality slice

Nominal `==` and `!=` select compiler-provided `core::ops::PartialEq`. The method contract is `fn eq(borrow self, rhs: Rhs) -> Bool`: the receiver is borrowed and remains usable, while the right operand is owned and follows ordinary move rules. `!=` negates the selected equality result. Primitive equality stays built in; ordering and compound assignments remain gated. The focused CLI test covers direct and forwarded generic evidence, equal/unequal cases, source and standalone Wasm parity, receiver availability, RHS use-after-move rejection, wrong/missing RHS implementations, private/inactive selection, ambiguity (with the correct `!=` diagnostic), malformed receiver/result signatures, left-to-right operand evaluation, and RHS early return. The language guide source/Wasm check and primitive float comparison regression pass. This slice does not finish OP1 or its missing-operator audit.

### OP1 user-defined unary negation slice

Nominal unary `-` now selects compiler-provided `core::ops::Neg`, which declares associated `Output` and owned `neg(self)`. Generic `T: Neg` forwards the selected evidence, and lowering evaluates the operand once before making the selected call. Primitive numeric negation remains on the built-in path, including signed-minimum literal handling. The language guide demonstrates a heterogeneous nominal input/output through a generic negation function.

The four serialized `user_defined_neg_` CLI tests pass: nominal source/standalone Wasm parity (`i32(-5)`), missing implementation rejection and owned receiver move, once-only operand effects with primitive `i32` negation parity (`i32(-7)`), and inactive/private/ambiguous selection diagnostics. An inactive extension reports no visible implementation; a private matching extension reports that the match is private or inactive, consistent with binary operator selection. The guide source/Wasm test passes with its `Neg` example. A first guide run exposed that the generic aggregate operand needed the existing whole-value transfer allowance; this was added narrowly to unary `-`, after which guide source and Wasm both passed. `cargo test -j1 -p memobits-wasm --test backend checked_mul_division_negation_and_remainder_cover_boundaries` passes, preserving signed-minimum and checked negation boundaries. `git diff --check` passes. No commit was created.

### OP1 nominal ordering slice

Nominal `<`, `<=`, `>`, and `>=` select the compiler-provided `core::ops::PartialOrd` interface and call `lt`, `le`, `gt`, or `ge` respectively. Each member borrows its left receiver, consumes an owned associated `Rhs`, and returns `Bool`. The implementation requires all four interface methods; an operator never derives its result from equality or from another ordering member. Primitive comparisons retain their existing numeric path. The binary aggregate-use analysis now admits nominal comparison operands so the selected call can transfer the RHS while retaining the receiver loan. The guide covers all four operators plus generic evidence forwarding.

`cargo test -j1 -p memobits-cli --test cli user_defined_ordering_borrows_receiver_and_runs_in_source_and_wasm -- --test-threads=1` passes source and standalone Wasm parity (`42`), with each of the four methods tested against distinct true/false cases, a heterogeneous `Other` RHS forwarded through `T::Rhs`, left-to-right operand evaluation, receiver availability, RHS use-after-move rejection, wrong-RHS and wrong-signature diagnostics, missing and ambiguous selection, and private/inactive extension filtering. The guide source/Wasm test and nominal equality regression pass. `cargo test -j1 -p memobits-wasm --test backend imported_scalar_inputs_and_float_comparisons_are_checked -- --test-threads=1` passes, preserving primitive float comparisons. Remaining OP1 work includes compounds and the required missing-operator audit.

### OP1 compound-assignment gate and operator audit disposition

The next requested slice, nominal `+=` through an operation-specific exclusive
receiver, is not safe to enable with the current lowering path. Compound
assignments are presently checked as numeric operations and lower by reading a
captured scalar value, evaluating the RHS, then writing a binary result. The
selected-operator facts are keyed by expressions, while assignment selection
needs statement-level facts. A nominal implementation also needs a place loan
that spans RHS evaluation without moving the old value, releases cleanly on an
early RHS return, and writes through the same once-captured place on success.
Adding an interface declaration or routing through the existing binary
operator would violate the required exclusive receiver and ownership contract.
No compound operator implementation was activated in this step.

The operator surface audit now records the launch disposition: only the named
matrix families are in scope. Complement, exponentiation, updates, ranges,
optional coalescing/propagation, and ternary syntax remain outside the launch;
this does not decide their future grammar. The next safe implementation step
for compounds is to introduce statement-level selected-operation facts and
exclusive place-capture/loan lowering, then enable one nominal compound family
with early-exit and aliasing tests before extending the remaining family.

No `AddAssign` core interface was added in this step, so no incomplete public
extension surface is exposed. The accepted signature remains the matrix
contract: `share self`, owned `Rhs`, and `Unit` result. Implementation must add
the canonical interface together with statement-level selection and place-loan
lowering so imports cannot imply working operator support prematurely.

For this gate review, `user_defined_ordering_borrows_receiver_and_runs_in_source_and_wasm`
and `language_guide_checks_bytes_array_equivalence_in_source_and_wasm` pass,
covering current generic/source/standalone-Wasm OP1 behavior. Existing
`captures_binary_and_compound_assignment_left_values_first`,
`compound_field_write_reads_the_old_value_before_the_right_hand_side`, and
`checked_mul_division_negation_and_remainder_cover_boundaries` also pass,
preserving place/RHS sequencing, field compound behavior, and primitive checked
arithmetic. No nominal compound behavior is claimed by these regressions.

### OP1 nominal `+=` first compound slice

Nominal `+=` now selects compiler-provided `core::ops::AddAssign`. The public
contract is `fn add_assign(share self, rhs: Rhs)` with implicit `Unit` result.
Selection uses visible local or imported implementation evidence and checks the
associated RHS type; integer literals therefore infer from `Rhs`. Primitive
`+=` remains on the original checked numeric path. The checker records the
selected call against the assignment target expression, and lowering captures
named local or projected places as `share` references before evaluating the
RHS, then calls the implementation once. A return from the RHS leaves before
the call; the captured loan's liveness reaches the call on falling-through
paths.

`user_defined_add_assign_mutates_nominal_target_in_source_and_wasm` passes a
nominal local update in both source and standalone Wasm (`u32(19)`), covering a
named local, projected field, and indexed array place with an index side effect
evaluated once. It checks an RHS early return in source and standalone Wasm
(`9`), rejects an RHS mutation through an overlapping share loan, and checks missing, inactive, and
ambiguous implementations, immutable targets, wrong RHS types, and mismatched
method signatures. `language_guide_checks_bytes_array_equivalence_in_source_and_wasm`
passes with the new executable `Tally` example. The slice is bounded to concrete
nominal targets whose RHS implementation can be resolved at the assignment;
generic constrained assignment inside a generic function remains outside this
slice; no generic evidence forwarding is claimed for compound selection. No
other compound family was enabled.

### OP1 `AddAssign` generic-forwarding gate review

A focused attempt to forward `T: AddAssign` into compound assignment is blocked
by the existing G1 specialization boundary: a generic function with a mutable
`var T` parameter and `T::Rhs` projection is rejected before assignment
selection (`TE007`, unsupported generic parameter form; `TE017`, unsupported
whole-value use). The current generic function template does not establish
mutable generic parameter storage or compound-assignment place facts. Adding
evidence lookup to the assignment checker alone would therefore not make this
path reachable or sound. No generic forwarding behavior is claimed. Revisit
after G1 supports mutable generic parameter specialization and associated
projection facts for statement-level assignments; retain the existing concrete
`AddAssign` boundary until then.

The failed prototype was removed. The concrete AddAssign source/Wasm,
alias-loan, early-return, projected/indexed-place, malformed-signature,
visibility, ambiguity, and primitive compound regressions remain the acceptance
set for the activated slice.

The acceptance set now also includes indexed-place and field-projected RHS
early-return cases in
`user_defined_add_assign_mutates_nominal_target_in_source_and_wasm`. The index
expression runs before the RHS; each RHS returns from the function, and the
selected method contains a dynamic divide-by-zero trap that must be skipped.
Source execution and standalone Wasm return 11 for the indexed case and 12 for
the field case. These checks prove that the AddAssign method is not called on
the early-exit paths; they do not independently prove frame or allocation
cleanup.

### OP1 nominal `-=` compound slice

Nominal `-=` selects compiler-provided `core::ops::SubAssign` with a shared
mutable receiver, an owned associated `Rhs`, and implicit `Unit` result. The
checker selects the interface by the concrete target and resolves the RHS
before lowering. Lowering reuses the established AddAssign place capture and
exclusive loan path, evaluating the place once and skipping the selected call
when RHS evaluation returns early. Primitive `-=` remains on the checked
numeric path.

The focused CLI test covers source and standalone Wasm with a distinct nominal
RHS and local, field-projected, and indexed targets (including one-time index
evaluation). Named, field, and indexed early-return tests in source and Wasm
prove the method is skipped. It also rejects overlapping loans, wrong and
missing RHS implementations, immutable targets, ambiguous evidence, and
private/inactive evidence; primitive subtraction remains executable. Generic
constrained compound assignment remains gated pending mutable generic parameter
and associated-projection statement facts. Other compound families remain
gated.


### OP1 nominal `*=` compound slice

Nominal `*=` selects compiler-provided `core::ops::MulAssign` with a shared
mutable receiver, owned associated `Rhs`, and implicit `Unit` result. The
checker selects evidence for the concrete nominal target and confirms the
method signature. Lowering uses the existing compound place-capture path, so
locals and projected/indexed targets are captured once before RHS evaluation;
an early RHS return skips the selected call. Primitive checked `*=` remains on
the built-in numeric path.

The focused CLI test covers source and standalone Wasm for a distinct nominal
RHS, local/field/indexed targets, one-time index evaluation, early return,
overlapping-loan rejection, missing/private/inactive/ambiguous evidence, wrong
RHS types, immutable targets, and primitive multiplication. Generic constrained
compound assignment remains gated because generic mutable parameter places and
associated-projection statement facts are unsupported.

### Generic constrained `MulAssign` update

The earlier generic gate is superseded for the owned-local form. An owned `T`
parameter can be moved into a mutable local and updated using caller-forwarded
`T: MulAssign` evidence and `T::Rhs`; the implementation uses a distinct
nominal `Delta` RHS. Source and standalone Wasm both return 42. Missing generic
evidence and a wrong concrete RHS are rejected, the owned RHS is verified as
moved, and primitive `u32 *= u32` retains source/Wasm parity. Generic projected
or indexed targets remain gated.

The runnable language guide now demonstrates concrete and generic nominal
`MulAssign` with `ScaleFactor`, plus primitive multiplication. The focused
command `cargo test -j1 -p memobits-cli --test cli
user_defined_mul_assign_mutates_nominal_target_in_source_and_wasm` passes.


### OP1 nominal `/=` compound slice

Nominal `/=` selects compiler-provided `core::ops::DivAssign` with a shared
mutable receiver, owned associated `Rhs`, and implicit `Unit` result. It shares
the established compound place-capture path: locals and projected/indexed targets
are captured once before RHS evaluation; an early RHS return skips the selected
call. Primitive checked `/=` remains on the numeric path, including division by
zero and signed overflow traps.

The focused CLI test covers source and standalone Wasm for a distinct nominal
RHS, local/field/indexed places, one-time index evaluation, early return,
overlapping-loan rejection, missing/private/inactive/ambiguous evidence, wrong
RHS types, immutable targets, and primitive integer division. Generic constrained
compound assignment remains gated because mutable generic parameter places and
associated-projection statement facts are unsupported.


### OP1 nominal `%=` compound slice

Nominal `%=` now selects compiler-provided `core::ops::RemAssign` with a shared mutable receiver, owned associated `Rhs`, and implicit `Unit` result. It uses the same compound place-capture path as `/=`: local, field-projected and indexed targets are captured once before RHS evaluation, and early RHS return skips the method. Primitive integer `%=` remains built in with checked zero-divisor behavior; signed MIN % -1 remains defined as zero. Generic constrained compound assignment remains gated because mutable generic parameter places and associated-projection statement facts are unsupported.

`cargo test -j1 -p memobits-cli --test cli user_defined_rem_assign_mutates_nominal_target_in_source_and_wasm` passes, covering source and standalone Wasm for heterogeneous nominal RHS, local/field/index targets and one-time index evaluation, early return, overlapping-loan rejection, missing/private/inactive/ambiguous implementations, wrong RHS, immutable targets, generic rejection, and primitive `%=`. Its primitive cases now explicitly verify source and standalone Wasm success for `9 %= 4`, `i32::MIN %= -1` returning zero, and `% 0` producing a `RE007` remainder-by-zero trap. `cargo test -j1 -p memobits-cli --test cli language_guide_checks_bytes_array_equivalence_in_source_and_wasm` passes. Direct guide source and standalone artifact runs both return `Result: Ok(i32(42))`; artifact `/tmp/memobits-remassign/guide.wasm` is 110,996 bytes. `cargo test -j1 -p memobits-wasm --test backend checked_mul_division_negation_and_remainder_cover_boundaries` passes, at the Wasm backend layer, and the focused CLI test separately verifies primitive `%=` source/artifact parity for a normal value, remainder-by-zero traps, and signed MIN % -1 returning zero. `git diff --check` passes.

### OP1 nominal `&=` compound slice

`&=` now parses as an assignment statement and nominal `&=` selects the
Rust-owned `core::ops::BitAndAssign` contract (`share self`, owned associated
`Rhs`, implicit `Unit`). Concrete nominal targets use the established selected
compound place path. `u32 &= u32` is enabled as the narrow primitive equivalent
of existing `u32 & u32`; other primitive bitwise and shift compounds remain
gated. Generic constrained compound assignment remains gated.

The focused parser test passes. The focused CLI test passes source and
standalone Wasm parity for a distinct nominal RHS across local, field and
indexed targets, proves index evaluation once, covers early RHS returns on all
three place forms, alias rejection, missing/private/inactive implementation
visibility, malformed RHS and generic rejection, and primitive `u32 &= u32`
parity. It also verifies a dynamic out-of-bounds indexed target with an RHS
`return 24`: both source and standalone Wasm return 24. The fix captures the
narrowest owner loan that can be formed without checking a dynamic index, keeps
that loan live during RHS evaluation, and forms the checked indexed receiver
only after a normally completing RHS. Statically literal indices keep their
checked place capture before RHS because constant invalid indices are rejected
at compile time. The same ordering correction applies to selected `+=`, `-=`,
`*=`, `/=`, and `%=` compounds; the new regression also verifies an out-of-bounds
dynamic target with an RHS return in source and standalone Wasm for all five.
All five prior source/Wasm compound regression tests pass. A new source/Wasm
case proves a literal indexed target remains disjoint from a sibling literal
index accessed in the RHS. Dynamic-index loans conservatively cover the nearest
array owner while RHS executes, so uncertain accesses into that same owner
remain overlapping.

### OP1 nominal `^=` compound slice

`^=` now parses as compound assignment, and `core::ops::BitXorAssign` is part
of the Rust-owned virtual `core::ops` module. Nominal targets select
`bitxor_assign(share self, rhs: Rhs)` with implicit `Unit`, preserving distinct
RHS types and the established single-capture/RHS-before-method compound path.
Primitive `u32 ^=` is supported through the existing per-bit XOR operation;
other primitive compound families and generic constrained compounds remain
gated. The language guide checks both nominal `FeatureBits ^= FeatureDelta` and
primitive XOR behavior.

`cargo test -j1 -p memobits-syntax parses_bitxor_compound_assignment_statement`
passes. The serialized BitXorAssign CLI test passes source and standalone Wasm
parity for a distinct nominal RHS across local, field, and indexed targets;
index side effects occur once. It also covers early RHS return and skipped
method invocation, dynamic out-of-bounds early return, normal dynamic bounds
traps in source/Wasm, alias rejection, a legal disjoint indexed operation,
missing/private/inactive/ambiguous selection, wrong RHS, malformed receiver,
generic rejection, and primitive `u32 ^=` source/Wasm parity. Test fixture
values distinguish XOR from OR (nominal result 32, primitive result 9).

The prior `BitAndAssign`, `BitOrAssign`, and `AddAssign` focused source/Wasm
compound regressions pass. The language-guide CLI source/standalone-Wasm test
passes, as does `u32_bitwise_and_shifts_match_source_and_standalone_wasm`.
Direct guide runs return `Result: Ok(i32(42))`; standalone artifact
`/tmp/memobits-guide-bitxorassign.wasm` is 113590 bytes and returns the same.
`git diff --check` passes. No broad formatting, reset, or commit was run.

### OP1 nominal `<<=` compound slice

Nominal `<<=` selects `core::ops::ShlAssign` with `share self`, an owned
associated `Rhs`, and implicit `Unit`. It uses the established one-time place
capture and RHS-before-method sequencing for locals, fields and indexed places;
generic constrained compound assignment remains gated. Primitive `u32 <<=`
uses the existing checked shift operation. Statically reducible literal counts (including basic `+`, `-`, and `*`
expressions) at or above 32 report `LE003`; dynamic out-of-range counts trap with `RE007` in source and
standalone Wasm. A nominal custom `Rhs` is passed to its selected method without
primitive count validation.

`cargo test -j1 -p memobits-syntax parses_shift_left_compound_assignment_statement`
passes. `cargo test -j1 -p memobits-cli --test cli
user_defined_shl_assign_mutates_nominal_target_in_source_and_wasm` passes local,
field and indexed place updates, one-time index evaluation, early return,
dynamic out-of-bounds behavior, alias rejection, disjoint access, visibility,
ambiguity, wrong-RHS and generic rejection, plus primitive counts 0, 3, 31,
static 32 and `16 + 16`, and dynamic 32. Source and artifact values/traps agree, and a nominal
custom RHS value of 32 is accepted. The language-guide source/standalone-Wasm
CLI test passes with the new nominal and primitive examples. `cargo fmt --all -- --check` and `git diff --check` both pass.

### Generic constrained `ShrAssign` slice

Generic specialization already selected and carried the caller's interface
evidence, but compound-assignment checking only searched the current module's
concrete extension candidates. The assignment checker now reuses matching
forwarded evidence to obtain associated `Rhs` and the selected method. This
supports a generic function with an owned `T`, `T::Rhs`, and `T: ShrAssign`,
mutating a local specialized from its owned parameter. It does not open
generic projected/indexed places or add support for other still-gated nominal
compound operators.

The existing ShrAssign source/Wasm CLI test now executes `update<T>` for a
nominal `Flags` value and verifies result 8 in source and standalone Wasm. The
language guide includes the same generic constrained form. Run the focused
command `cargo test -j1 -p memobits-cli --test cli
user_defined_shr_assign_mutates_nominal_target_in_source_and_wasm`; it passes.

### Generic constrained `AddAssign` slice

`AddAssign` now has matching generic source and standalone Wasm proof for an
owned `T` local and caller-forwarded `T: AddAssign` evidence. The implementation
uses a distinct nominal associated `Rhs` (`Delta`), and an otherwise identical
generic without an implementation is rejected for missing evidence. Existing
nominal checks continue to cover shared mutable receiver behavior, one-time
target capture, owned RHS, early return, visibility and ambiguity. The focused
regression also confirms primitive `u32 += u32` source/Wasm parity remains
unchanged. The language guide now demonstrates concrete and generic nominal
updates with distinct `TallyDelta`, plus primitive `u32 +=`.

`cargo test -j1 -p memobits-cli --test cli
user_defined_add_assign_mutates_nominal_target_in_source_and_wasm` passes,
including nominal mutation, heterogeneous RHS, generic success, missing generic
evidence and primitive source/artifact parity. The language-guide CLI test
`language_guide_checks_bytes_array_equivalence_in_source_and_wasm` passes.

### Generic constrained `SubAssign` slice

`SubAssign` now has source and standalone Wasm proof for an owned generic
parameter moved into a mutable local, with caller-forwarded `T: SubAssign`
evidence and a distinct nominal associated `Rhs`. The matching generic call
without an implementation is rejected, as is a generic call with the wrong
RHS type. Existing concrete SubAssign coverage retains alias/loan rejection,
single place capture and RHS sequencing; this slice does not enable generic
projected or indexed targets. Primitive `u32 -= u32` source/artifact parity is
also checked.

`cargo test -j1 -p memobits-cli --test cli
user_defined_sub_assign_mutates_nominal_target_in_source_and_wasm` passes.
The language guide demonstrates the same generic owned-local form with
heterogeneous RHS. Generic AddAssign and ShrAssign proofs remain independent;
this does not complete generic compound-assignment support.

### Generic constrained `DivAssign` slice

`DivAssign` now has source and standalone Wasm proof for an owned generic
parameter moved into a mutable local, caller-forwarded `T: DivAssign` evidence,
and a distinct nominal associated `Rhs` (`Delta`). A matching generic call
without an implementation is rejected; wrong RHS and RHS move-after-use are
also covered. Existing primitive checked `u32 /=` source/Wasm behavior remains
covered, and the division trap regression verifies zero and signed overflow.
The language guide demonstrates concrete and generic heterogeneous updates plus
primitive division. Corrected a pre-existing standalone Wasm early-return
expectation: the artifact correctly returns 15, matching source, rather than 7.

`cargo test -j1 -p memobits-cli --test cli
user_defined_div_assign_mutates_nominal_target_in_source_and_wasm` passes,
including generic source result `u32(27)` and standalone Wasm `i32(27)`.
`cargo test -j1 -p memobits-cli --test trap_reports_cli
division_failures_report_zero_and_signed_overflow` passes. The language-guide
source/standalone-Wasm CLI test passes with `Result: Ok(i32(42))`. This does not
complete generic compound-assignment support; generic projected/indexed targets
and the remaining compound families stay gated.

### D2 recursive tuple patterns and ownership (verification pending)

The tuple-surface audit confirms coverage for ordered tuple identities,
construction, positional/labeled projection and initialization, internal
arguments/results, struct fields, enum payloads, and scalar nested aggregate
placement. Existing source/Wasm tests exercise reordered labeled initialization,
occurrence-local labels, nested tuple identities, and tuple payloads in both
structs and enums. String-owning tuples move through internal owned parameters
and results, with memory-cap stress coverage; nominal String-owning struct
transport remains separately gated.

Tuple destructuring now parses recursively nested positional patterns and
wildcards. Analysis binds nested tuple types, enforces arity at each level,
checks duplicate names across the full pattern, and creates internal locals for
nested aggregate staging and wildcard destinations. Lowering extracts each
level in positional order, stages nested tuple values before recursing, and
uses an ordinary local for a wildcarded String so lexical cleanup owns it. The
IR's existing exact-sequence ownership recognition transfers direct String
provenance from a named tuple local to each fresh extraction destination and
the Wasm backend clears source descriptors on the final consuming extraction.
The CLI test `nested_tuple_patterns_and_string_wildcards_transfer_cleanup_in_source_and_wasm`
and the guide's nested tuple example cover a nested scalar pattern and a
wildcarded owned String.

Cargo's first CLI compile reported LE900 for that case because Wasm layout
restricted a tuple with direct String fields to only String and primitive
siblings. The backend now permits nested non-String aggregate fields in the
synthetic tuple layout; nested fields that themselves own String descriptors
remain gated. A negative case preserves the existing nominal String-owning
struct layout restriction. Cargo verification of both the positive nested
pattern and nominal rejection is pending.

This agent did not run Cargo; the new parser, analysis, CLI, and guide cases
await the designated owner's compile and test run. String-owning tuple
temporaries, nested String-owning aggregate elements, destructuring aliases,
and partial-arity destructuring remain gated. No D2 completion claim is made;
verify exact move/drop behavior and audit any additional ownership gaps before
closing the manifest row.

The D2 aggregate-placement audit then found that analysis excluded `Ty::Tuple`
from fixed-array elements with TE017, although tuple values already lower as
struct aggregates and Wasm array storage copies aggregate cells. Analysis now
admits tuple array elements while retaining existing reference and String-owning
storage gates. Added source/Wasm cases for `Array<(i32, Bool), 2>` and
`(Array<i32, 2>, i32)`, plus a guide example covering both placements. The
designated Cargo owner has not yet compiled or run these additions; D2 remains
open against the original manifest acceptance.

The owner reports a full-workspace result of **1,107 passed** for the D2
tuple/array composition state. The negative regressions and early TE017 guards
for reference-bearing, String-owning, and List-containing tuple array elements
were added after that run and remain unverified. The launch manifest still
requires tuple support in nested aggregates and exact move/drop behavior for
admitted owning elements; the documented String and List limits remain
implementation gates, not a redefinition of that acceptance row.

The owner subsequently reports **1,108 passed** after the tuple-array guard
coverage. The next D2 slice stages a direct String-owning tuple temporary in a
cleanup-tracked local when passing it to an owned internal call. Wasm's existing
consuming-call path then clears the caller descriptor; the callee can
destructure the tuple into String locals for lexical cleanup. Source/Wasm
coverage includes multi-String transfer, a later-argument early return, and
repeated calls under a capped memory maximum. The guide demonstrates the
supported direct-call form. These changes have not been run by Cargo; other
String-owning temporary placements and nested String-owning aggregate elements
remain implementation limits, not exclusions from the original D2 acceptance.

The Cargo owner reported two failures on this slice: the callee's owned tuple
parameter remained in the lexical heap-owner set after its recognized final
destructuring extraction, and nested String-owning tuple transport reached IR
validation instead of a language diagnostic. IR ownership validation now
retires a tuple owner at that final consuming extraction, with lowering omitting
the redundant end-of-scope cleanup. Analysis now rejects owned calls whose
tuple parameter contains a nested String-owning aggregate with TE017 before IR
lowering. The temporary, early-exit, stress, and rejection regressions are
pending owner verification; no Cargo run was performed for these fixes.

Added an additional bounded-memory regression that repeats the later-argument
early return 8,192 times after staging a two-String tuple as the first call
argument. It checks source result parity and runs the Wasm artifact with the
existing one-page-over-initial-memory cap; this test also awaits Cargo.

### H1 CLI host capability slice

The bounded source and artifact path is implemented. The project manifest uses
the serde-backed `[host] profile = "cli"` configuration with one typed import,
`memobits:console.write_i32(i32) -> unit`. Root-module source binds it with
`extern fn write_i32(value: i32);`. Analysis validates the declaration against
the manifest, lowering preserves its typed function identity, Wasm emits a
function import, and the CLI enables the matching runtime capability for both
source and artifact runs. Import-free execution continues through the same
runner. Unsupported profiles, capabilities, signatures, multi-module source
declarations, non-CLI hosts, JavaScript, and a stable external ABI remain out
of this slice.

The full workspace suite passed **1,067 tests** (verification log:
workspace-test-h1-final-2026-11-22.log (.local-design/archive/logs/workspace-test-h1-final-2026-11-22.log is a local note, not in the repository)).
Focused CLI coverage includes configured source and artifact calls, import-free
execution, and undeclared or type-mismatched Wasm imports rejected before guest
execution. The runnable guide source and standalone Wasm both report
`Result: Ok(i32(42))`. The host-capability example source and artifact both
print `Host i32: 42` and report `Result: i32(7)`; see
[the example](../../examples/topics/host-capability/README.md).

CLI help and the language-guide overview now state this exact supported scope.

### OP1 final matrix reconciliation

Cargo-owner reports the final focused OP1 verification at **12/12**, the full
workspace at **1,103 passed**, and the language guide source and standalone
Wasm both returning `Result: Ok(i32(42))`. This documentation update did not
run Cargo; these counts and results are owner-reported evidence.

The accepted matrix in [implementation requirements](../design/launch-manifest.md#operator-contract-matrix)
remains in force. Current evidence includes:

- Arithmetic and bitwise/shift dispatch, heterogeneous RHS/output cases,
  missing/wrong/ambiguous implementation rejection, owned operand move
  behavior, source/Wasm parity, and existing primitive arithmetic/bitwise
  boundaries. Side-effecting operand-order tests cover `+`, `-`, `*`, `/`, `%`,
  `&`, `|`, `^`, `<<`, `>>`, equality, and ordering.
- Overloaded precedence cases `x + y << n` and `a & b == c`, with source/Wasm
  parity, plus primitive bitwise precedence and bounded `u32` shift counts.
- All ten concrete nominal compound families on local, field-projected, and
  indexed targets. Generic evidence-forwarding coverage exercises all ten on
  owned locals and indexed targets. Table-driven generic tests cover disjoint
  projected/indexed loans for each family, index-before-RHS ordering, RHS
  early return, deferred bounds checks, and skipped assignment methods. See
  [CLI tests](../../crates/memobits-cli/tests/cli.rs) and
  [generic compound tests](../../crates/memobits-cli/tests/generic_const_evidence_cli.rs).
- Equality and ordering tests check true/false results, receiver availability,
  owned RHS move behavior, Bool signatures, and selection diagnostics. Unary
  nominal negation and checked primitive signed-minimum behavior are covered.
  Built-in String replacement tests retain RHS reads and early-exit cleanup.
- `false && ...` and `true || ...` skip RHS effects in source and standalone
  Wasm. `primitive_signed_shifts_are_rejected` checks primitive `i32 << u32`
  and `i32 >> u32` rejection. `assignment_and_short_circuit_operators_resist_user_overloads`
  verifies `=` replaces a value even with a trapping `AddAssign` implementation
  present, and nominal `&&`/`||` remain Bool-only despite matching
  `BitAnd`/`BitOr` impls. Cargo-owner reports these focused cases in the 12/12
  run.
  New focused cases in `generic_const_evidence_cli.rs` are
  `overloaded_sub_mul_div_rem_evaluate_operands_left_to_right_in_source_and_wasm`,
  `overloaded_add_shift_and_bitand_equality_keep_operator_precedence`,
  `short_circuit_skips_rhs_effects_in_source_and_wasm`, and
  `primitive_signed_shifts_are_rejected`.

The previously open signed `i32 >> u32` and overload-resistance evidence gaps
are closed by the owner-reported focused 12/12 run. Signed primitive shift
rejection is demonstrated for `i32` in both directions only; rejection across
other signed widths remains unverified and is recorded as a test coverage
limit, not as a change to the matrix contract.

The compound matrix scope discrepancy is reconciled: primitive `u32 &=`,
`|=`, `^=`, `<<=`, and `>>=` are supported built-in operations and have
existing source/Wasm tests. Unsigned shift compounds retain the bounded count
contract. Signed and non-`u32` primitive bitwise/shift compounds remain gated.
The matrix row and implementation requirements now state that contract.

The owner-reported 12/12 focused run includes the signed-shift and overload
resistance tests above. This documentation update did not run Cargo.

The architecture audit's other open syntax candidates remain out of this OP1
delivery: integer complement (`~`), exponentiation (`**`), increment/decrement,
ranges, optional coalescing/propagation, and ternary syntax. Their exclusion is
a scope disposition, not an omitted accepted operator. The previously noted
test-verification gaps are closed; OP1 still must be judged against every
accepted matrix row, and this evidence does not claim signed-shift rejection
for widths other than `i32`.

### D2 recursive tuple ownership and next aggregate placements

Extended the current ownership path to tuples containing nested String-owning
tuples. Analysis permits this recursive tuple-only shape while retaining early
TE017 rejection for nested nominal String owners. Lowering stages nested owned
tuple elements in cleanup-tracked locals. IR provenance follows ownership
through nested tuple construction and full recursive extraction. Wasm lays out
and clears nested String descriptors recursively and recognizes nested tuple
owners for internal parameter/result transfer.

Added a source/Wasm regression that constructs `((string, string), u32)`, moves
it through an owned forwarder and consumer, recursively destructures it, and
checks the result. Added a repeated 8,192-iteration source/Wasm memory-cap
stress case with two 4 KiB strings per nested tuple, including owned
forwarding and recursive destructuring. The guide demonstrates this shape.
The existing transport-gate regression now covers a nested nominal String
owner, which remains unsupported. A later ownership pass seeded unused owned
tuple parameters in lower and IR heap provenance; an 8,192-iteration capped
memory stress regression covers unused nested tuple parameters on both normal
and early returns, and guards owned scalar and borrowed parameters. The Cargo
owner reports the focused D2 run at **5/5**, the full workspace at **1,116
passed**, and guide source plus standalone Wasm parity. This evidence predates
the local-record placement work below.

The D2 audit confirms the manifest explicitly requires tuple placement in
struct fields, enum payloads, and nested aggregates. It requires complete
labeled initialization, but does not specify labeled destructuring aliases or
partial destructuring; those are not tracked as D2 gaps. Current code still
gates String-owning tuple placement in arrays and enum payloads. This WIP
extends local nominal struct fields to contain String-owning tuple values:
lowering stages the tuple owner, IR accepts only a matching String-owning tuple
field move, and Wasm recursively lays out and clears its String descriptors.
Wasm now permits borrow/share reference values whose every use is a next
field-address step in a projection rooted at a named owner. This allows
`record.values.0`/`.1` reads while keeping whole-owner borrows subject to the
named-owner/direct-call restrictions. Removed the obsolete IR tuple helper.
Added source/Wasm behavior coverage and an 8,192-iteration capped-memory case.
These changes have not been compiled or run by this agent and await Cargo-owner
verification. By-value nominal owner transport remains gated. String-owning
tuple placements in arrays and enums remain implementation work against the
original D2 acceptance, not scope exclusions. The enum placement work below
supersedes the enum portion of that checkpoint; tuple placement in arrays
remains open.

### D2 String-owning tuple enum payload implementation (Cargo verification pending)

Added the next enum placement slice: an enum variant can own a String-owning
tuple payload. Lowering now tracks owned enum parameters and locals through
scope cleanup. IR ownership provenance follows tuple descriptors into an enum
construction and return/call bindings, then into tuple bindings extracted by a
consuming match. Wasm
layout records descriptor offsets per enum variant, clears moved tuple sources,
clears the consumed enum cell after payload extraction, and releases only the
active variant's descriptors on normal or early scope exit. Nested
String-owning enum storage remains gated.

Added source/standalone-Wasm coverage for an enum constructor returned from a
function, owned enum parameter transport, consuming tuple destructuring, and
an early return. Added a separate 8,192-iteration Wasm memory-cap case that
repeats both early-return and normal consuming paths with two 4 KiB strings per
enum. The runnable language guide now demonstrates this path and states the
remaining array and direct-String-enum limits. These edits pass Rust syntax
formatting checks and `git diff --check`; Cargo has not been run. Request the
focused tuple ownership and memory stress tests from the designated Cargo
owner before treating the slice as verified.

The Cargo owner subsequently reported the enum-payload code compiled and 5/6
focused tests passed. The remaining fixture exposed three coupled IR cases:
enum scope exit was checked as Struct-only, return cleanup accounting did not
consume a captured owner on the return edge, and a heap aggregate call result
could not transfer directly into an owned aggregate parameter. These checks
now include String-owning enums and the exact typed consuming call handoff.
Formatting and diff checks pass; the owner should rerun the previously failing
focused test and stress target. No Cargo was run for this follow-up.

The next focused rerun still reported consuming-match ownership diagnostics.
The cause was twofold: the final `VariantExtract` consumed the enum cell but
the IR scope validator kept that owner live, and it treated that final scalar
payload extraction as an unrelated consume even when an earlier tuple payload
had already transferred to a local. The validator now removes the enum cell at
the consuming extraction and recognizes that paired payload transfer. Owned
tuple/enum locals captured into an exact matching owned call parameter are
also recognized as transfers, and Wasm clears the original captured local
descriptor after the call. Static format/diff checks pass; this correction is
unverified until the focused Cargo rerun.

The Cargo owner then reported a full workspace run at **1,112 passed, 9
failed**. The regression cluster came from the scope validator adding every
String-owning aggregate-typed local to heap-owner scope, even when it held
only static strings or no heap allocation; that also rejected pre-existing
mutable nominal struct assignment. Heap facts already seed owned aggregate
parameters and propagate actual heap ownership, so scope validation now uses
those facts plus List locals only. Enum switch-edge classification now also
counts direct String payloads, and consuming payload extraction recognizes a
direct String transfer. This addresses the logged TE018 families, but remains
unverified until the Cargo owner reruns the workspace.

An independent layout review confirmed that the IR ownership predicate is
intentionally recursive for cleanup provenance; this is not a Wasm support
promise. Wasm still admits the nested tuple-owner slice and rejects nested
nominal String-owning structs and nominal owners in enum payloads. Added a
focused CLI build regression for both LE900 cases. The guide's logged static
`local_string_fields` rejection was due to adding all String-owning *types* to
heap-owner scope; the fix above tracks actual heap facts instead. Formatting
and diff checks pass; Cargo verification remains pending.

### D1 generic nominal trailing methods (implementation checkpoint)

The parser retains owner type and const parameters on the synthetic trailing inherent extension. Project analysis matches declarations against concrete generic receiver identities, substitutes arguments into method signatures, queues receiver-specific method body facts, and gives each specialization a distinct function ID and lowered name. A combined specialization worklist drains generic function and generic method requests to a fixed point, including requests discovered while checking either specialized body; both request families have a 256-instance diagnostic limit. Regressions cover multiple type and const instances, mutual method calls, method-to-generic-function calls, the cap, and public/private/direct/symbol/transitive visibility. The guide demonstrates `Box<T>` method dispatch. The owner reports generic D1 focused tests passed **13/13**, the full workspace passed **1092 tests**, and guide source plus standalone Wasm both returned `Result: Ok(i32(42))`; this documentation update did not run Cargo. Nested expanding generic type arguments such as constructing a receiver whose type contains the current `T` nested inside another nominal type remain unsupported, so receiver-type expansion is not claimed. The broader D1 manifest acceptance remains in force; this is a remaining implementation limit, not a reduced requirement. See the handoff checkpoint (.local-design/archive/superseded/d1-generic-inherent-checkpoint.md is a local note, not in the repository).

### D2 enum ignored-payload cleanup (Cargo verification pending)

The Cargo owner reports the pre-fix full workspace at **1,122 passed**, with
the runnable guide passing. Two enum cleanup gaps were then identified. In a
consuming match, lowering extracted only bound fields; a final bound field
could consume the enum cell while ignored String-owning fields remained in it,
after which descriptor clearing lost those allocations without releasing
them. Lowering now extracts each ignored String-owning payload into a hidden
owned local, consumes the enum on the last extracted field, and lets ordinary
scope cleanup release the discarded value. Wasm enum layout now records direct
String payload descriptor offsets as well as nested aggregate offsets, so
`Result<string, Error>` cleanup and source-descriptor clearing see the active
String slot.

Added two 8,192-iteration source/Wasm memory-cap regressions: one matches an
enum containing two String-owning tuple payloads while discarding one whole
payload, and one discards the direct String payload of a locally bound
`Result<string, Error>`. Cargo has not been run for these fixes; the reported
1,122-test and guide results predate them. The next step is focused verification
of both new tests, the enum tuple ownership stress case, the returned String
Result CLI test, then the full workspace and guide by the designated Cargo
owner.

At the time of the previous checkpoint, the String-owning tuple-in-array slice
was suspended with only analysis and IR ownership-classification changes. The
following section records its resumed implementation; its evidence remains
unverified until the designated Cargo owner runs the source/Wasm regressions
and guide.

### D2 Result parameter reachability review and tuple-array continuation

The Cargo owner reports the latest full workspace at **1,125/1,125 passed** and
the runnable guide passing. A read-only audit of the Result parameter concern
found that owned `Result<String, E>` parameters are seeded as heap owners and
receive `EndStructLocal` cleanup on both normal and early returns. The IR call
transfer helper can forward such a parameter, but no accepted source path can
provide it with heap storage: heap Result construction is permitted only for a
direct Result return or the immediate consuming match; call-produced heap
Results must be immediately matched and cannot be forwarded as owned call
arguments; and Wasm entry/export signatures do not admit Result parameters.
Thus the standalone String-parameter stress does not test Result-parameter
cleanup, while the cleanup code exists for that state if constructed directly
in IR. Static Result payloads do not establish heap-parameter reachability.

The ignored Result-success payload stress now uses explicit `Ok(value)` with
the bound value unused. The immediate-match recognizer rejects compiler-created
wildcard-discard locals, so that case exercises the explicit payload binding
and its lexical cleanup. Its tag checks rely on the compiler-known Result
shape, which `Program::validate_types` verifies as exactly ordered `Ok` and
`Err` variants.

The next D2 implementation slice resumes the preserved String-owning tuple
array WIP. Analysis now admits tuple array elements; IR tracks String owners
from nested tuple construction into an array local/return and through owned
array parameters; Wasm layout and cleanup are being extended to enumerate
String descriptors in fixed arrays of tuples. Source/Wasm behavior coverage,
a repeated capped-memory cleanup case, and a guide example have been added.
These edits had not been compiled or run at that checkpoint.

### D2 tuple-array focused failures and follow-up

The Cargo owner reports two of four focused `tuple_nested_arrays` tests
failing. Both source fixtures violated the existing direct-local transport
contract: String-owning tuple values must first be initialized in a named
local. The tuple-array and borrow fixtures now bind tuple locals before
constructing arrays. The enum fixture now uses the supported String-owning
tuple payload and binds the enum before exercising the intended Wasm array
gate; this avoids the separate unsupported direct String enum-payload path.

The capped ownership stress now nests fixed arrays of String-owning tuples two
levels deep and exercises normal and early returns. An initial descriptor
table expansion ceiling of 65,536 entries was replaced by type-directed Wasm
cleanup: arrays use runtime loops, and enum payload cleanup dispatches on each
active tag. Layout metadata now scales with type shape rather than fixed-array
length. The tuple-array test helper
now accepts an explicit expected output, including `u32(42)` for these entry
points, rather than assuming every case returns `i32`. `TypeId` is imported
only in the Wasm test module to avoid a production unused-import warning.

The Cargo owner then reported 10/11 memory stress tests passing, with the new
nested-array case rejected by IR validation during owned-call argument
staging. Lowering moves an owned array into a temporary local before evaluating
later arguments; heap-owner propagation and escape validation recognized
String/struct/enum moves but omitted array moves. IR now recognizes exact-type
consuming moves between whole array locals in both paths, preserving owner
propagation into the callee and Wasm source clearing. Syntax checks pass; Cargo
verification remains pending.

The Cargo owner reports the full workspace at **1,129/1,129 passed** with
runnable guide source/Wasm parity after the array-local ownership transfer fix
and guide binding correction. This result predates the type-directed cleanup
rewrite below.

### D2 lazy nested aggregate cleanup and enum arrays (Cargo verification pending)

Removed the 65,536 descriptor-offset ceiling. Wasm now computes String
ownership from type definitions and emits cleanup recursively: fixed arrays
use runtime loops with per-nesting-depth scratch locals, structs walk field
offsets, and enums compare the active tag before cleaning that variant's
payload. The same cleanup path clears moved source descriptors without
releasing them and releases active descriptors on scope exit or reassignment.
The layout no longer materializes one offset per array element.

Wasm layout now admits String-owning enum payloads and enum array elements,
including enum payloads that contain fixed arrays of String-owning tuples.
Added source/Wasm coverage for enum arrays with both array and tuple payload
variants, an 8,192-iteration memory-cap stress case across normal and early
returns, and a guide example. Added a backend unit case for large array layout
without per-element descriptor expansion. The edits pass Rust syntax and diff
checks but have not been compiled or run; D2 acceptance and the latest guide
remain pending Cargo-owner verification and ownership review.

The Cargo owner reports the latest full workspace at **1,129/1,129 passed**
with runnable guide source/Wasm parity after the nested tuple-array move fix.
This run verifies the current tuple-array slice before the next enum-array and
scalable-layout work below.

### D2 enum payload review after 1,127/1,129

The Cargo owner reports the focused enum-array tests green and **1,127/1,129**
in the full workspace. Both remaining failures were stale rejection
expectations: the Wasm layout now accepts String enum payloads, and the
anonymous enum test's inline `Owned(string)` payload is supported. The negative
gate now targets a String-owning nominal struct nested in another struct; the
direct `Array<String>` gate and exported String ABI gates remain.

Review found the aggregate-parameter prologue copied the incoming value, then
cleared `pointer + 8` as though every heap-owning aggregate began with a String
descriptor. That corrupts a String enum payload (offset 8 can be its String
length). It now clears moved descriptors recursively using the parameter type
and active enum tag. Added source/Wasm coverage that passes a heap String enum
through an owned parameter and reads its length, extended the capped enum-array
stress with an active direct-String variant, and updated the language guide to
show that payload. These edits are unverified; no Cargo commands were run.

## D2 nested Result storage and prologue verification

Date: 2026-11-23. All Cargo runs used `-j1`; logs are in `.local-design/logs/`.

Decision (WP1): the Wasm layout no longer rejects `Result<String, E>` in a
struct field or fixed-array element. Evidence shows this is sound because IR
ownership validation (TE018) still rejects every heap-owning Result in nested
storage: struct-field construction, array elements, element replacement and
heap Results returned by calls all fail, and reading a nested Result needs a
consuming match that nested storage cannot provide. Only literal `Ok("...")`
(zero allocation provenance) and `Err(...)` values can be stored. Cleanup
dispatches on the active enum tag, and the releaser ignores a null allocation,
so cleanup is a no-op for these shapes. The two stale LE900 cases were removed
from `wasm_gates_string_exports_and_nested_storage`; every other gate stays
(direct `Array<String>`, nested String-owning structs, exported String
signatures, owned String-owning struct arguments).

Added: `crates/memobits-cli/tests/d2_nested_result_storage.rs` (3 tests: struct
fields, arrays read back and passed owned/borrowed, TE018 rejections), a capped
stress test in `tuple_destructure_memory_stress.rs` (normal and early return,
8,192 iterations), and a guide function `nested_result_storage` (error code 61).

Prologue review (WP2): the aggregate-parameter prologue clears the incoming
pointer by type and active tag only for owned parameters; scratch locals cover
`1 + 2 * depth` and the existing tests pass. No defect confirmed. Residual
risks: the `transferred` shortcut in the IR `VariantExtract` check skips the
read-only report for non-local bases (a separate TE018 gate, "String enum
payloads require a consuming match", rejects borrowed enum matches, verified
by hand), and `extracted_owned_payload` scans the whole block.

Verification: `d1_anonymous_shapes` 13/13, `tuple_nested_arrays` 4/4,
`tuple_destructure_memory_stress` 12/12, `d2_nested_result_storage` 3/3,
`cli wasm_gates` 2/2; full workspace 1,133 passed, 0 failed
(`wp4-workspace-test.log`). The guide prints `Result: Ok(i32(42))` from source
and standalone Wasm. `git diff --check` is clean. `cargo fmt --check` reports
pre-existing diffs in 16 other files (not auto-fixed).

## WP6: IR `VariantExtract` hardening (2026-11-23)

Changes in `crates/memobits-ir/src/lib.rs` (`validate_operand_escapes`, the
`VariantExtract` arm): (1) a non-local base whose variant owns String storage
is now rejected locally ("a heap String payload cannot be extracted from
borrowed, field or array-element storage") when the base is Load-derived
(read-only provenance) or an `Extract` that is not a recognized tuple
destructure; previously such bases skipped the report path through the
`transferred` shortcut and relied on the TE018 "String enum payloads require a
consuming match" gate. (2) `extracted_owned_payload` now scans only the
statements after the prior extraction instead of the whole block. Errors are
collected during the block walk and pushed after it because `report` holds the
mutable error borrow.

Tests added to `crates/memobits-ir/tests/validation.rs`: heap payload
extraction rejected from a borrowed enum, a struct field and an array element
(IR validator level), plus a scalar-payload control that must not be rejected.
`cargo test -j1 -p memobits-ir --test validation`: 56 passed
(`logs/wp6-ir-validation.log`).

Reruns (all -j1, logs `logs/wp6-*.log`): `d1_anonymous_shapes` 13/13,
`tuple_nested_arrays` 4/4, `tuple_destructure_memory_stress` 12/12,
`d2_nested_result_storage` 3/3, `cli wasm_gates` 2/2; workspace
`cargo test -j1 --workspace --no-fail-fast -- --test-threads=1`: 1,137 passed,
0 failed (1,133 + 4 new; `wp6-workspace-test.log`); guide source and standalone
Wasm: see `wp6-guide-run.log` / `wp6-guide-wasm-run.log`. No accepted program
changed behavior.

WP7 design proposal appended to `PLAN.md` ("Phase 2b design proposal"); no code.

## WP8 — Phase 2b slice 1: owned flat String-owning nominal struct argument (2026-11-23)

Scope: `type Label { text: string, n: u32 }` (String and primitive fields only,
no Error ancestry) moves into an owned internal parameter from a named local.
No other gate widened.

Code:
- `memobits-ir` (`scoped_string.rs`, re-exported in `lib.rs`): one shared
  predicate `is_string_owner_transport(types, ty)` (String-owning tuple or flat
  nominal struct) plus the shape rule `is_flat_string_owner_struct` /
  `OwnerFieldShape`, reused by analysis (which keeps its own type
  representation) and Wasm.
- `memobits-wasm/src/lib.rs`: `validate_string_struct_borrows` uses the shared
  predicate for the owned-parameter clause and the "must move directly from a
  named local of the same type" argument check; the owned-tuple Extract
  moved-source clearing (former tuple-module test) now uses the predicate.
- `memobits-analysis/src/lower.rs`: owned-argument lowering admits flat nominal
  owners; nominal temporaries are deliberately not staged into hidden locals,
  so direct temporaries stay rejected by the Wasm argument gate.
  `types.rs`: TE017 for an owned argument whose nominal struct mixes String
  fields with non-primitive fields.
- Tests: `crates/memobits-cli/tests/d2_owned_struct_transport.rs`; one stale
  case in `cli.rs` `wasm_gates_unsupported_string_struct_uses` updated
  (`take(Label { text })` now reports "must move directly from a named
  local"). Guide: `owned_string_struct_argument` in the language guide.

Verification: focused `logs/wp8-owned-struct-transport.log` (6 tests: positive
source+Wasm, 8,192-iteration capped-memory stress with normal and early
returns in caller and callee, double-release regression, negatives,
exports/plain struct, cross-block probe); workspace
`logs/wp8-workspace-test.log`: 1,143 passed, 0 failed; guide source and Wasm
`Result: Ok(i32(42))` (`logs/wp8-guide.log`). Mutation checks (temporary, reverted): skipping String release makes
the stress fail with RE007 allocation failure; skipping call-site moved-source
clearing makes the double-free regression test hang (so that test has a 60 s
guard).

Cross-block probe (borrowed heap-payload enum before extraction): an `if`/`else`
join of borrowed enums is rejected early by analysis (TE017 "reference-valued
branch results are not supported"); a match inside a branch, or on a local
alias used inside a branch, is rejected by the IR extraction check (TE018
"String enum payloads require a consuming match"). Nothing slips through.

## WP9 — Phase 2b slice 2: owned result of a flat String-owning nominal struct (2026-11-23)

Code: the result clause of `validate_string_struct_borrows` uses the shared
`is_string_owner_transport` predicate (no separate result rule); IR `Return`
treats a consuming return of a named local of such a type as a move
(previously tuple-only). Callers must bind the call result directly to a new
local; literal-only tail struct returns also build (no heap storage).
Tests (same file `d2_owned_struct_transport.rs`): result positive source+Wasm
(normal, early return, forwarding, unused binding), 8,192-iteration capped
stress with allocation before return and early returns, and 10 negatives
(temporary receiver, bare discarded call, var reassignment, array/tuple/`if`
position, tail call forwarding, borrowed-reference return, nested field).
Stale cases updated narrowly: `cli.rs` `wasm_gates_unsupported_string_struct_uses`
(`make() -> Label` case now a heap tail literal expecting "requires a direct
new local binding") and
`owned_string_tuple_transport_rejects_use_after_move_and_nominal_structs`
(exported `forward(Box) -> Box` now reports the exported-signature gate
"exported signatures cannot take structs or struct references", still LE900).
Guide: `make_label` / `owned_string_struct_result`.
Verification: `logs/wp9-owned-struct-transport.log` 9/9;
`cargo test -j1 --workspace --no-fail-fast` 1,146 passed, 0 failed
(`logs/wp9-workspace-test.log`; an earlier fail-fast run in the same log name
failed only on the exported-signature message above); guide source and Wasm
`Result: Ok(i32(42))` (`logs/wp9-guide-run.log`, `logs/wp9-guide-wasm-run.log`).
Slices 3-4 not started.

## WP10 / WP12 / WP13 — docs consistency, `mb check`, owner placement slice 3 (2026-11-23)

WP10: guide comment (enum payloads: "String payloads are supported") and four
`implementation-requirements.md` edits (D1 paragraph and row, operator
discrepancy line removed, `Array<T, N>` routine default) applied by a Haiku
subagent and verified by grep.
Follow-up: the only IR diagnostic naming a "heap String tuple" now reads
"String-owning aggregate call result must be assigned directly to a whole
local" (code TE018 unchanged; no test matched the old text).
WP12: `mb check [--project PATH] [--lib]` runs resolve, types, lowering, IR
validation and the Wasm layout gates (compiles in memory, writes nothing);
same diagnostics as `build`, `--output` rejected (PE004). PE005 is unused now.
Tests: `crates/memobits-cli/tests/check_cli.rs` (4: success without `target/`,
type error identical to build, LE900 gate, build-only option), `cli.rs` help
and missing-manifest cases updated. README, help text, inventory TOOL-01 updated.
Verification: `logs/wp10-12-check-cli.log` 4/4; `logs/wp10-12-workspace-test.log`
1,150 passed, 0 failed; guide source and Wasm `Result: Ok(i32(42))`
(`logs/wp10-12-guide-*.log`).
WP13 (slice 3): flat String-owning nominal struct as a tuple element and as a
fixed-array element, through the shared `is_string_owner_transport`.
Changes: wasm `member_layout` gains `allow_flat_string_owner` (true only for
tuple fields), `type_layout` allows arrays of flat owners via a new
`StructLayout::is_flat_string_owner`, and `member_layout` rejects arrays of
owners stored inside structs/tuples/enum payloads; IR `StructNew` accepts a
flat owner move only when the enclosing struct is a tuple; analysis staging
for tuple elements uses `is_string_transport_owner`. Tuple destructuring and
owned-call transport of tuples holding an owner stay TE017 (no analysis gate
change). Tests: `d2_owner_placement.rs` (3: source+Wasm positive, 8,192
iteration capped stress with normal/early returns incl. tuple literal and call
temporaries and nested arrays, 9 negatives); stale cases removed from
`d2_owned_struct_transport.rs` and `cli.rs`. Guide: `string_struct_elements`.
Decisions: tuple elements accept a literal or call-result struct (staged
hidden local, same path as tuple-of-tuple), array elements still reject call
results; nested `Array<Array<Label,N>,M>` builds and releases but reading
through `grid[i][j].borrow()` is a pre-existing LE900 limit. The generalized
nominal Extract clearing is still unreachable (TE017/TE022 block move-out).
Verification: `logs/wp13-placement.log` 3/3; `logs/wp13-workspace-test.log`
1,153 passed, 0 failed; guide source and Wasm `Result: Ok(i32(42))`
(`logs/wp13-guide-run.log`, `logs/wp13-guide-wasm-run.log`). Guide
mutation check (wrong expected value) returned `Err`, confirming it runs.

## WP14 / WP15 — nested String owners and String-owning anonymous records (2026-11-23)

WP14 (slice 4): the shared predicate `memobits_ir::is_string_owner_transport`
now admits a nominal struct whose fields are String, primitive, a nested
admitted owner (recursive, visited set so recursive by-value types stay
rejected) or a fixed array of such owners. `OwnerFieldShape::Owner` and
`is_string_owner_struct` replace `is_flat_string_owner_struct`; the analysis
mirrors (`types.rs` `admitted_string_owner_struct`, `lower.rs`
`is_flat_string_owner_struct_type`) recurse over their own type models. Wasm:
`struct_layout_at`, `member_layout` (arrays of owners inside aggregates, owner
struct as enum payload) and `type_owns_string_storage` use the predicate; the
cleanup code was already type-directed. IR `StructNew` accepts a nested owner or
array of owners moved from a named local; lowering stages a struct-literal field
owner into a hidden local (as for tuple elements), so `Outer { inner: Label { .. } }`
is accepted. Decisions: whole-owner `var` reassignment stays rejected (TE018);
an array literal or call result as an enum payload stays rejected (named local
only); `bag.items[0]` reads through a field-held array stay LE900 (element-borrow
limit, roadmap stage 2). The generalized Extract clearing is exercised by consuming
`match` of a whole enum local with an owner-struct payload under capped stress; no
field move-out path became reachable (TE022 still blocks it).
Tests: `d2_nested_owner_transport.rs` (positive source+Wasm, 8,192-iteration capped
stress, 12 negatives, export gate); stale gate cases removed from
`d2_owned_struct_transport.rs`, `d2_owner_placement.rs`, `cli.rs`,
`tuple_owned_temporaries.rs`. Guide: `nested_string_owners` (mutation-checked).
Logs: `logs/wp14-build2.log`, `logs/wp14-nested-owner.log`,
`logs/wp14-workspace-test.log` (1,156 passed, 0 failed).
WP15 (anonymous records): records are `"\0record"` structs, so the shared predicate
admits them once nesting works; no separate compiler change. Tests:
`d2_record_owner_transport.rs` (5: locals/args/results; struct field, array, tuple,
enum payload and nested record; capped stress; negatives; export gate). Guide:
`string_owning_records` in the anonymous-shapes section (mutation-checked). A record
binding needs an annotation when a literal like `1` would infer `i32` against a
`u32` field (TE002 otherwise).
Verification: `logs/wp15-record-owner.log` 5/5; `logs/wp15-workspace-test.log`
1,161 passed, 0 failed; guide source and Wasm `Result: Ok(i32(42))`
(`logs/wp15-guide-run.log`, `logs/wp15-guide-wasm-run.log`).

## WP16 / WP17 (2026-11-23)

WP16 (D2 closure tests): `crates/memobits-cli/tests/d2_tuple_acceptance.rs`, 4 tests
(label/ordinal same storage, written-order labeled initialization, missing-label
TE002, tuple exported-signature LE900), all source + standalone Wasm where
executed. No compiler change. Log: `logs/wp16-d2-tuple-acceptance.log` (4/4).
PLAN.md D2 table has no MISSING rows; closure left to the architect.

WP17 (D3 warning channel + migration): `memobits-diagnostics` gains
`Category::Migration` (prefix `MW`; `Severity::Warning` already existed). Parser
emits `MW001` (legacy `Option<T>` spelling, suggests `T?` or `(borrow T)?`) into
`ParseResult.warnings`; `Resolution.warnings` aggregates; `mb` prints warnings to
stderr before any error for check/build/run/resolve/analyze-project/
ownership-project/syntax/analyze/ownership. Exit status unchanged. Documented in
`crates/memobits-cli/README.md`. Guide migrated to `T?` / `(borrow i32)?` with an
explanatory comment. No test fixture needed migration: no existing test asserted
empty stderr with `Option<T>` (workspace stayed green). New tests:
`d3_optional_warnings.rs` (9), `memobits-syntax/tests/migration_warnings.rs` (1).
Verification: `logs/wp17-workspace-test.log` 1,174 passed, 0 failed (run before the
9th D3 test was added); `logs/wp17-d3-optional-warnings.log` 9/9; guide source and
Wasm `Result: Ok(i32(42))` with empty stderr (`logs/wp17-guide-*.log`). Cargo for
iteration and focused runs was run by the contractor directly; the full workspace
run was delegated to a Haiku subagent.

### WP18 C1 text traversal and spelling migration (2026-11-23)

- `loop ch in text`: type checker accepts `string` single-segment path receivers (types.rs `ForEach`), lowering walks a byte-offset counter (`lower_for_each`), new IR instruction `StringScalarRead { source, offset, width }` (IR validation, ownership transfer/loan reads, Wasm emission reusing `emit_string_scalar`). Loan, move and binding negatives come from the existing checks. No allocator or runtime file changed.
- MW002 (`String`) and MW003 (`Bytes<N>`) added in the parser warning channel. Finding: bare `String` was rejected with TE001 at the start of this run (test `uppercase_string_type_spelling_is_rejected_with_migration_guidance`); to follow the accepted decision it is accepted again with identical meaning (qualified `m::String` still rejected) and that test became `uppercase_string_is_a_compatibility_spelling_but_qualified_paths_are_rejected`. `docs/design/decisions.md` line on "only source type spelling" updated.
- Guide: new checked `text_loop` (error code 63) and compatibility comments; it already used `string` and `Array<u8, N>`. No maintained test fixture asserted empty stderr with legacy spellings, so none needed migration. Protected examples (hashing, utf8-validator, strings, others) untouched; they now print MW002/MW003 warnings.
- Tests: `crates/memobits-cli/tests/c1_text_traversal.rs` (11), `memobits-syntax/tests/migration_warnings.rs` (+1). Logs: `logs/wp18-c1-text-traversal.log`, `logs/wp18-workspace-prelim.log` (1,186 passed, 0 failed), final workspace and guide logs `logs/wp18-workspace-test.log`, `logs/wp18-guide-run.log`, `logs/wp18-guide-wasm-run.log`.
WP18 final: `cargo test -j1 --workspace --no-fail-fast -- --test-threads=1` (last Cargo run, after all edits) = 1,187 passed, 0 failed (`logs/wp18-workspace-test.log`). Guide source and standalone Wasm: `Result: Ok(i32(42))`, empty stderr (`logs/wp18-guide-*.log/.err`).

### WP18 correction (WP19, 2026-11-23)

The WP18 re-acceptance of bare `String` (and MW002) was an architect error against the committed decision. Restored: bare `String` is rejected with TE001 ("use lowercase 'string'"), test `uppercase_string_type_spelling_is_rejected_with_migration_guidance` restored, MW002 removed from the parser (reserved/unused), `Bytes<N>` MW003 kept. Counts in the WP18 entry above predate this correction; see `logs/wp19-*.log`.


### WP20 S test gaps (2026-11-23)

New file `crates/memobits-cli/tests/wp20_s_gaps.rs` (11 tests, source + standalone Wasm where executed, exact diagnostic codes for negatives): I1 grouped selector chain execution, grouped-import non-activation, transitive and prelude non-activation (TE007); G1 257-instantiation generic-function limit (TE007); G2 wrong annotated `Output` (TE002) directly and through a generic; OP1 mixed-type primitive arithmetic (TE002), signed `<< >>` and compound bitwise rejection for i8/i16/i64, unary `+`/`!`/`~`/`++`/`??`/ranges with matching extensions (TE007, TE002, SE001, SE002), all five primitive u32 compounds; D1 bodyless/empty trailing-method execution and named struct/enum reference payload rejection (TE017). No bugs found. Log: `logs/wp20-s-gaps.log` (11/11).

### WP21 D1 nested generic type arguments (2026-11-23)

Before: `Pair<Wrap<T>>`, `Wrap<Pair<T>>` or `Wrap<T>` in a method of `Wrap<T>` (signature or body, including `let` annotations and struct literals) failed with TE001 "unsupported or unresolved type 'T'" plus TE007 "inherent method signature is outside the executable type subset". Cause: `Checker::type_path` substituted only a bare `T`; nested type arguments were resolved from the written text. Fix (`memobits-analysis`): `TypeTable::substitute_generic_arguments` splices already-resolved concrete types into written arguments as internal `\0ty` paths (handled at the top of `TypeTable::resolve`), applied in `type_path` and `let` annotations; instance identity still comes from resolved arguments. The existing specialization worklist and 256-method cap are unchanged. Tests: `crates/memobits-cli/tests/d1_nested_generics.rs` (3: several receivers incl. const-argument receivers; public cross-module import and inactive-without-import; unbounded recursion with a 60 s child-process guard, rejected in about 30 ms). Guide: `nested_generic_methods` (code 64). Remaining limit: forwarding a receiver const parameter into a nested nominal argument (`Tag<N>`) reports NE003 unknown type 'N'. Unrelated pre-existing finding: a method call on a field projection receiver (`t.first.read()`) fails IR validation (TE018) even for non-generic types. Logs: `logs/wp21-*.log`.
WP21 final: workspace 1,202 passed, 0 failed (logs/wp21-workspace-test.log); guide source + standalone Wasm Result: Ok(i32(42)), empty stderr (logs/wp21-guide-*).


### WP22 residual fixes (2026-11-23)

1. Const parameter forwarding. Cause: the resolver's `Checker::ty` treated `N` in `Tag<N>` (parsed as a type path for non-template nominals) as an unknown type because const generic parameters were filtered out of the in-scope set. Fix: `memobits-resolve/src/names.rs` tracks in-scope const parameters (function, type and inherent-extension items) and accepts them as bare type arguments only; `memobits-analysis/src/types/typetable.rs::substitute_type` substitutes the receiver's const value into such arguments during specialization. A const name is still not a type elsewhere (NE003), unknown names stay NE003, mismatched values are TE002.
2. Field-projection receivers. Cause: `lower_selected_call` lowered the receiver with `lower_expr`, which loads the whole struct for `Field`/`Index` bases (TE018). Fix (`memobits-analysis/src/lower.rs`): non-owned receivers on `Field`/`Index` bases use `lower_place` + `address_chain` with the receiver's access, so loans are field-level (disjoint sibling legal, overlap BE005, immutable owner BE005). Owned `self` on a field/element is now rejected earlier with the existing TE022 partial-move diagnostic (`types.rs`, both inherent and interface-selected call sites via `reject_extraction`).
3. Tests: `wp22_residual_fixes.rs` 12/12 (const forwarding x5, borrow on field/nested/element/generic field, share on places and immutable owner, loans, owned self TE022, whole-local unchanged, String-owning element 256-iteration loop, interface-selected). Guide: `nested_generic_methods` extended (Gauge/Lane const forwarding, field-place borrow/share). Logs: `logs/wp22-*.log`.

### WP23 M1 behavior-preserving extraction (2026-11-23)

Created wasm `validation.rs`, `layout.rs`, analysis `lower/calls.rs`, `types/interfaces.rs` by verbatim moves (only `mod`/`use`/`pub(super)` added; rustfmt on new files only). Line counts: wasm lib.rs 6139 -> 5309, lower.rs 3170 -> 2942, types.rs 7080 -> 6933. Equivalence: harness diff empty over 14 examples (stdout/stderr/exit, 13 identical wasm sha256); workspace 1,214 passed / 0 failed before and after with identical sorted pass lists. Report: `m1/equivalence-report.md`; logs `logs/m1-{before,after}-tests.log`. Left in place: operator/generic-evidence candidate selection (inlined in many `expr_impl` arms), owner-cleanup layout helpers.

## WP24 (contractor, 2026-11-23): MW001 removed, strings migrated
- Removed MW001 emission (`warn_legacy_option`) from memobits-syntax; channel and MW003 intact. Tests converted to assert `Option<T>` is silent (d3_optional_warnings.rs 10/10, migration_warnings.rs 2/2); channel proven via MW003. Docs updated (cli README, guide comment, inventory OUT-01/ENG-05, implementation-requirements D3, PLAN D3 row WAIVED).
- examples/projects/strings migrated `String` -> `string`; source and Wasm both print `Result: i32(0)`, empty stderr.
- Workspace: 1,215 passed, 0 failed. Guide source and Wasm: `Result: Ok(i32(42))`, empty stderr.
- Logs: logs/wp24-syntax.log, wp24-d3.log, wp24-build.log, wp24-workspace.log.

## WP25 (contractor, 2026-11-23): examples cleanup
- Item 1: "## Expected output" ```text block in every examples/projects/*/README.md (new READMEs for enf-lexer, language-guide); `crates/memobits-cli/tests/examples_documented.rs` runs check, source run, build and standalone run (artifact run passes `--project` so host-capability's profile applies) for each project in a temp dir, requires exit 0, empty stderr, stdout equal to the block; fails when the block is missing.
- Item 2: calculator, computation, numeric, strings, arrays, enums, structs now `Result<i32, Error>` with `Ok(value)` and distinct `Err` codes (outputs: 265, 175, 42, 22, 493, 1094300, 63). host-capability exempt (H1 pins `Result: i32(7)`), explained in its README. `match_cli.rs` enums expectation updated; numeric `[export]` (`add`) unaffected.
- Item 3: hashing and utf8-validator migrated to `Array<u8, N>`; `mb check` clean for all 14 projects. Root README examples list rewritten; stale `Bytes<N>`/`Option<u32>`/`String` text fixed.
- Item 4: `git mv examples/design/language-guide.mb docs/design/proposed-language-guide.mb` with historical header; links updated (README, enf-lexer-slice.md, language-feature-inventory.md, guide comment); examples/design removed.
- Workspace 1,217 passed, 0 failed. Logs: logs/wp25-examples.log, logs/wp25-workspace.log.

## WP26 (contractor, 2026-11-23): examples restructure

- Layout: `examples/{guide,topics,apps,analysis}`. `git mv`: language-guide -> `guide`; arrays, enums, host-capability, module-imports, numeric, structs -> `topics/`; astar, enf-lexer, hashing, utf8-validator -> `apps/`. `examples/projects` removed.
- `topics/basics`: calculator + computation + strings as modules `arithmetic`, `loops`, `text` (Err codes 1 to 6), `Ok(462)`. New `topics/generics-operators` (`Vec2` with core::ops Add/Sub/PartialEq, `weigh_twice<T> where T: Weigh`, `combine<T> where T: Add`), `Ok(41)`.
- Guide split into `numbers`, `text`, `tuples`, `aggregates`, `ownership`, `collections`, `enums_outcomes`, `generics`, `operators`; `main.mb` keeps `main` with the same Err codes and `Ok(42)`. No item had to stay in main.mb; helpers shared across modules (`byte_is`, `byte_length`, `no_byte`, `make_words`, `Row`, `total`) are `pub` with explicit `use`.
- References updated (tests, READMEs, AGENTS.md, docs/design, live .local-design docs); new `examples/README.md`; `examples_documented.rs` discovers guide/topics/apps; `.gitignore` gets `examples/**/target/`.
- Logs: `.local-design/logs/wp26-*.log`.

## S1 (contractor, 2026-11-23): built-in type spelling, additive compiler + migration
- Parser (`memobits-syntax/src/lib.rs`): `ty()` now parses `T ! E` (-> `Result<T, E>`) over `ty_postfix()` (the old type parser, `?` suffixes bind there); `bool`/`char`/`array<..>` map to the existing Bool/Char/Array paths at parse time. `as` casts use `ty_postfix` (no `!`). Parenthesized reference span for `(borrow T)?` is now taken before `)?` so diagnostics point at `borrow T`. `?!` and Attempt removal NOT done (S2). Old spellings still work.
- New tests: `memobits-syntax/tests/s1_type_operators.rs` (4), `memobits-analysis/tests/s1_type_operators.rs` (1, new vs old spelling give identical types/signatures), `check_cli.rs::bang_result_entry_runs_in_source_and_wasm` (`fn main() -> i32 ! Error`, source + standalone Wasm).
- Migration tool: `.local-design/migrate/migrate_types.py` (see PLAN.md "S1 status"). Applied to crates (tests + inline src test modules + `CORE_OPS_SOURCE`), examples, docs/design (not decisions.md), READMEs.
- Intentionally left on old spellings (S1 covers the old-spelling paths): `memobits-syntax/tests/migration_warnings.rs`, `memobits-cli/tests/d3_optional_warnings.rs` (restored from HEAD), Bytes<N> sources in `c1_text_traversal.rs` warning tests and `cli.rs` (`type Buffer = Bytes<1>`), `Result<i32, borrow Error>` in analysis `outcomes.rs`, `parser.rs` and `types.rs` malformed `Array<..>`/`Bytes<..>` cases.
- Logs: logs/s1-*.log.

## N-PAT (contractor, 2026-11-23): nested patterns
- Syntax: `PatternKind` is now `Wildcard | Binding(name) | Variant { path, slots: Vec<Pattern> } | Tuple(Vec<Pattern>)` (`PatternSlot` removed); sub-patterns at any depth, `(p)` groups, literal/struct patterns and guards stay SE002. Resolver collects bindings at any depth.
- Checking (`types.rs` `check_pattern`, new `types/patterns.rs`): each sub-pattern is typed against its payload (enums, `T?`, `T ! E`, inline enums, tuples); a lone identifier is a bare variant when the expected enum has it, else a binding (top-level bare binding keeps TE030). Coverage by a Maranget pattern-matrix usefulness algorithm: TE032 for arms no value reaches (old messages kept for flat cases), TE031 names up to four uncovered example patterns (`missing \`Ok(None)\``; flat text changed to `\`Shape::Rect(_, _)\``). Tuple scrutinees are matchable.
- Lowering (`lower_match`, no new IR op): decision tree of `EnumTag`/`Switch` blocks over references derived with `VariantAddr`/`FieldAddr` (root switch reads the owner itself, as the `string ! E` validator shape requires); per-leaf binding code then a jump to the arm body, lowered once. Owned leaf: `VariantExtract`/`Extract` moves (last consumes), unbound owned payloads extracted and ended, unbound whole owner ended (`EndStructLocal`), exactly once per arm; in-place leaf copies primitives, lends aggregates. Ignored heap `Ok` payload of `string ! E` keeps its TE018 gate (hidden local named `discarded match payload`).
- Gate note: a `_` arm over an owner holding heap Strings (e.g. `T::B(n) => n, _ => 0`) was TE018 ("owned local scopes differ"); it is now accepted because the arm ends the owner. No other existing gate changed (workspace tests unchanged except updated messages).
- Tests: `crates/memobits-cli/tests/nested_patterns.rs` (12; incl. two 8,192-iteration capped-memory tests, normal and early return), `crates/memobits-analysis/tests/nested_patterns.rs` (8), parser tests (2 new, 1 updated), `match_enums.rs`/`match_cli.rs` message updates. Mutation check: removing the unbound-owner release is rejected statically (TE018 scope mismatch), see logs/npat-mutation.log.
- Guide: `nested_patterns` (code 707) in `enums_outcomes`; docs: enum-implementation.md "Nested patterns (N-PAT)", examples/topics/enums README, inventory PAT-01/PAT-02.
- Verify: workspace 1,245 passed, 0 failed (`logs/npat-workspace.log`); fmt and `git diff --check` clean; guide source and standalone Wasm `Result: Ok(i32(42))`, empty stderr. Logs: `logs/npat-*.log`.

## S2 (contractor, 2026-11-24): spelling change completed
- Compiler: `T ?! E` is `T?` then `!` (same type as `T? ! E`); `T ! (borrow E)` grouping parses (error operand). Operator types parse to reserved template paths `?`, `!`, `array`; the Attempt and Bytes templates and Done/Skipped/Failed are gone. Primitives are `bool`/`char` internally; type names render `bool`, `char`, `string`, `array<u8, 4>`, `u32?`, `(borrow T)?`, `i32 ! Error`, `u32 ?! Error`, `(i32 ! Error)?`. `Option<..>`, `Result<..>`, `Attempt<..>`, `Bool`, `Char`, `Array<..>` fail with TE001 plus replacement guidance (resolver lets them through so analysis reports TE001); `Bytes` is an ordinary unknown type (NE003). MW001-MW003 removed; the warning channel (`Parser::warn`, ParseResult/Resolution warnings, CLI printing) is kept with a syntax unit test and no producer.
- Entry adapter: metadata version 2 (`Family::Result` / `Family::OptionalResult`, new `inner_offset` byte; header 13 bytes). `T ?! E` reads the Option cell at the payload offset (tag 0 Some, 1 None). Runtime `EntryOutcome::{Ok, OkSome, OkNone, Err}`; CLI renders `Ok(v)`, `Ok(Some(v))`, `Ok(None)`, `Err(Type, code=N)`; bool now renders `bool(true)`.
- Migration: Attempt/Done/Skipped/Failed uses migrated by hand (~35 sites: guide enums_outcomes, outcomes.rs, cli.rs, nested_patterns.rs, roots.rs); tool applied to parser.rs and s1 type-operator tests; `Bool(` expectations and string-literal `Bool`/`Char`/`Array<` in tests bulk-fixed; docs, READMEs, inventory and requirements updated.
- Tests: removed `memobits-syntax/tests/migration_warnings.rs`, c1 MW003 tests (replaced by `bytes_is_an_ordinary_unknown_type`), d3 warning tests; `d3_optional_warnings.rs` renamed `d3_optional_spellings.rs` (TE001 guidance for each removed spelling); new tests for `?!` (syntax, analysis, entry runtime decode, CLI entries). Workspace 1,243 passed, 0 failed (logs/s2-workspace.log); fmt and `git diff --check` clean; all 13 examples `mb check` with no warnings; guide source and Wasm `Result: Ok(i32(42))`, empty stderr.

## T1 (contractor, 2026-11-24): source-level tests, assert
- Syntax: `test fn name() {}` (contextual `test`; ItemKind::Function gains `test: bool`); `pub`, parameters, non-Unit result, generics rejected (SE002). Resolve: `Target::Test` loads every project module; Application/Library resolution strips tests (`Resolution::ignored_tests`), so normal artifacts and reachability are unchanged; test names bind no global (uncallable, hint in NE001); declaration lookup skips tests.
- `assert(cond)`: types.rs `explicit_assert` (TE010 count, TE002 type; precedence mirrors `drop` in types.rs and resolve names.rs), lower.rs `explicit_asserts` -> new IR `InstructionKind::Assert { condition }` (validated bool, no output; ownership/loans read the operand), Wasm `trap_if` with new `TrapReason::AssertionFailed = 12` (runtime message "assertion failed"; docs/design/wasm-backend.md table).
- CLI: `mb test [--project] [--fuel|--no-fuel-limit] [FILTER]`, `mb test FILE.wasm [FILTER]`, `mb build --tests [--output]` (default target/memobits/tests.wasm), `mb check --tests`; export names `test::<module>::<name>`; runtime gained `exported_functions`. `mb check`/`mb build` also compile the test target when loaded modules contain tests. Report: `running N tests`, `test <q> ... ok|FAILED` (+ reason and `-->` snippet), `test result: ok|FAILED. P passed; F failed; X filtered out`; exit 1 on failure or compile error, 0 otherwise (zero tests ok).
- Tests: `crates/memobits-cli/tests/test_command.rs` (16), `crates/memobits-syntax/tests/test_functions.rs` (4), trap-code mapping in `trap_reports_cli.rs`, `examples_documented.rs` now also runs `mb test` per project. Guide: `text_length_and_concat` test in `examples/guide/src/text.mb` + README section (existing numbered checks not converted: T2).
- Docs: crates/memobits-cli/README.md "Source-level tests", CLI help, decisions.md "Shipped T1 details", inventory TOOL-01/ENG-04/ENG-05. Logs: logs/t1-*.log.

## T2 (contractor, 2026-11-24): guide and examples converted to tests; check scope
- Check scope (architect rule): `mb check` always compiles the roots and then every project module and every test (`compile_tests`, `Target::Test`); `mb build`/`mb run` check only modules reachable from the roots and ignore tests. Code: `crates/memobits-cli/src/main.rs` (check-only `compile_tests` call; HELP text), docs: CLI README, decisions.md "Shipped T1 details" and the old "Until then" check-code note. Tests in `test_command.rs`: broken test fails check/test/check --tests but not build/run; unreachable broken module fails check but not build/run (17 tests in file, was 16).
- Guide: 64 numbered check codes (66 check functions) plus 9 internal bool helpers became 75 `test fn` + the existing `text_length_and_concat` = 76 tests (`mb test` ok, 76 passed). `walk_text` became a unit helper with asserts plus test `text_walk`. Facts: 297 original facts (tail conjuncts and `return false` guards, scripted comparison) -> 283 reappear verbatim as a single `assert(...)`; the other 14 are hand-converted (9 helper-call facts now their own tests, `numbers` if/else chain -> 12 asserts, `heap_text_result`, `local_heap_string_fields`, `optional_sugar`); 290 `assert`s from the script plus the manual ones. Mutation spot-check: flipping one assert fails with its line. `main` is now a small program (Row total 30 + byte_length("aé€") 6 + first of make_words(6) = 42) returning `Ok(42)`; source and Wasm `Result: Ok(i32(42))`, empty stderr. README code table removed, replaced by "Running the guide's tests"; AGENTS.md guide rule updated.
- Other examples (tests before = Err self-check codes -> after): basics 6 -> 8, generics-operators 5 -> 4, module-imports 1 -> 1, numeric 1 -> 2, astar 3 -> 2 (main keeps Err(1) for no route), hashing 4 -> 4, utf8-validator 8 -> 8 (main validates a sample, Ok(0)), enf-lexer 10 groups -> 8 (main lexes one input, Ok(0)); arrays/structs/enums had no checks, 2 added each; host-capability 0. All outputs unchanged. Each README has a `## Tests` section with command and summary line; `examples_documented.rs` requires the exact summary line, count >= 1 except host-capability (documented 0).
- Logs: logs/t2-*.log.

## A1 (contractor, 2026-11-24): alloc layer (`use alloc::List;`, `[build] alloc`)
- `alloc` is a Rust-owned virtual module in `memobits-resolve` (`virtual_source`, declares `pub type List;`, removed from the resolution after reference checks). `List<T>` is gated in `names.rs`: needs `use alloc::List;` (direct/grouped/prelude) or `use alloc;` + `alloc::List<T>`; otherwise NE003 `unknown type 'List'` with note ``add `use alloc::List;` to use List``. `templates::lookup_applied` also accepts the path `alloc::List`. No alias support. A project module named `alloc` is ME011. The applied `List<T>` stays reserved like `array<T, N>`; a bare user type `List` (module not importing it) still works (unchanged behavior).
- `[build] alloc` (default true): `Build.alloc`, `Manifest::alloc()`; reaches resolve (ME012 on any `alloc` import, note names the setting) and analysis `Checker.alloc` (TE033 for `concat`, `push_str`, `to_utf8_string`). Wasm backend untouched: it already emits allocator functions, heap globals and a growable memory only when a heap operation is reachable, so alloc=false artifacts have none (no `memory.grow`, memory max == min; core-only example: 7 functions, memory 17..17 pages; a concat program has the 3 helpers and max 0x3ffff).
- Standalone single-file commands accept `use alloc...` but do not enforce the import (no resolver).
- Migration: 62 sources via `.local-design/migrate/migrate_alloc_list.py` (Rust test literals + 2 guide modules), plus hand edits (cli.rs user `List` type renamed `Counter`). Guide: `use alloc;`, `qualified_list_path` test, header comment; 77 tests.
- Tests: `crates/memobits-cli/tests/alloc_layer.rs` (11), project manifest test, example `examples/topics/core-only` (3 tests, `Ok(i32(57911))`).
- Logs: logs/a1-*.log.

## E1a (contractor, 2026-11-24): owned elements in `array<T, N>`

- Design note: PLAN.md "E1 design note" (gates, storage/cleanup, E1b touch points, risks).
- Lifted gates: wasm `layout.rs` `type_layout` (String array element), wasm `validation.rs` `supported_type` (array of String) and `validate_string_struct_borrows` (call-argument chains through any depth of `ElementAddr`/`FieldAddr`/reborrow rooted at a named owner local: `grid[i][j].borrow()`, `bag.items[0].borrow()`, `d.title.size()`; forwarding a borrowed parameter stays rejected), wasm `lib.rs` `field_addr_rooted_at_local` (element links), IR `lib.rs` (`ArrayNew`/`feeds_owned_array_element` use `owns_string_storage` so String elements move in; `Share` projections of a heap owner are checked loans; `VariantAddr` of a String payload is allowed except for `string ! E` entry results, so a borrowed or element enum matches in place), IR `scoped_string.rs` (whole-array `var` reassignment, `array_binding` accepts reassignment), analysis `lower.rs` (String `Index` receiver is a read place; array literal owner elements are staged in a hidden local like tuple elements, so struct literals and direct call results work).
- New diagnostics: TE017 for `[x; N]` of a String-owning element (replaces the generic TE018 repeat messages); TE022 note on element move-out naming `replace`, `swap`, `pop` (not available yet); TE022 for overwriting an owning element in place (`items[0] = s`).
- Tests: `crates/memobits-cli/tests/e1_owned_elements.rs` (5): positive source+Wasm (82), capped-memory stress, negatives (move-out x3, repeat x2, overwrite, overlapping/dynamic loans, loan blocks array move and reassignment), disjoint loans + out-of-bounds trap (RE007 source and Wasm), in-place match of a borrowed String enum across blocks. Stale expectations updated narrowly: repeat cases in `d2_owner_placement`, `d2_nested_owner_transport`, `d2_record_owner_transport` (TE017); `d2_owned_struct_transport` (`[make()]` and borrowed in-place match cases now accepted); `d2_nested_result_storage` (TE022 or TE018); `cli.rs` (String array literal now builds).
- Stress: 8,192 iterations, 4,096-byte strings, memory capped to initial+1 pages, normal and early returns for `array<string, 2>` (caller/callee/reassign/returned), arrays of `Label` owners, nested `grid`, call-result elements; expected sum matched in source and Wasm. Mutation check (temporary, reverted): disabling `EndStructLocal` cleanup fails the capped run with RE007 (`logs/e1a-mutation.log`).
- Guide: `owned_array_elements` in `examples/guide/src/collections.mb` (78 tests, README count updated).
- Inventory COL-01/COL-02/OWN-03 updated.

## E1b (contractor, 2026-11-24): general `List<T>`

- Representation: analysis `Ty::List(Box<Ty>)`, IR `Type::List(Box<Type>)` (was `List(Primitive)`); element stride from Wasm layout (`aggregate_layout`). Element types: primitives of every width, bool, char, string, owner structs, tuples, enums, arrays (`List<array<u32,2>>`, `List<(string,u32)>`, `List<string?>` verified). Gated with a diagnostic: nested `List<List<T>>` (TE017; needs List moves inside collections), reference elements (TE017), List struct fields (existing TE018).
- Wasm: `list_descriptor::append` replaced the primitive `push` helper (reserves one slot, grows by doubling, moves existing bytes bitwise, releases only the old block, returns the slot address; the caller stores or `memory.copy`s the element and clears the moved heap source). `ElementAddr` accepts a List owner/reference (bounds from the descriptor length, RE007 trap). Cleanup is type-directed: new `emit_list_elements_cleanup` plus a `Type::List` arm in `emit_string_storage_cleanup` (loops over `len`, releases each element, then the block); `type_has_string_storage`/`max_string_array_depth` count Lists. Drop, `clear`, whole-list reassignment, scope exit and early returns all use it. A moved-from List descriptor is zeroed (`list_descriptor::clear`) so a later visit walks nothing. `pop` of an owner `memory.copy`s the element into the Option payload (slot is not released; length shrinks).
- IR/ownership: `ListPush` owner value is `Consume`; heap-string validator accepts a consumed/captured owner into a List (`feeds_owned_list_push`); `ListPop` output bound to a local seeds heap ownership; `option_matches` generalizes the scalar-option check; `get`/`ListRead`/`CollectionSearch` stay primitive-only.
- Analysis: `items[i]` typed for Lists and List references; list literals `[a, b]` with an expected `List<T>` lower to a hidden List local plus pushes in written order (`lower_list_literal`, shared `owned_element` staging with arrays; inline enum elements are staged too); `loop x in items` binds copies for primitives and a read-only `borrow T` reference for other elements (wasm `validation.rs` treats such locals as lent elements, like borrowed parameters); `get` on non-primitive is TE022 pointing at `items[i]`; `contains`/`index_of` on non-primitive is TE017; element overwrite and move-out keep the TE022 notes.
- Loans: live element loans block push/pop/clear/move/reassign at owner granularity (BE005); mutation inside `loop x in items` is BE005.
- Tests: `crates/memobits-cli/tests/e1b_lists.rs` (6): primitives of all widths, owner lists (strings, structs, enums, arrays) in source+Wasm, 8,192-iteration capped-memory stress (512-byte strings, memory capped to initial+1 pages; List<string> growth/pop/clear/reassign/return/lend, owner struct lists, enum lists; normal and early returns), negatives, OOB traps, alloc=false. Stale expectations updated: `cli.rs` empty-list diagnostics (List<i32>/[1] are now valid; nested List and `[true]` replace them), analysis `enums.rs` message keeps "Array". `stack.rs` descriptor-layout tests kept working by zeroing only moved-from descriptors.
- Mutation check (temporary, reverted): skipping element cleanup fails the capped run with RE007 (`logs/e1b-mutation.log`).
- Guide: `list_element_types`, `list_of_strings`, `list_of_owner_structs`, `list_of_tuples_and_arrays` in `collections.mb` (82 tests). Docs: list-slice.md, CLI README, inventory COL-02/03/04/05/06.
- Remaining / open: nested `List<List<T>>`; `replace`/`swap` and element overwrite (R1); fixed-array iteration over owners; Lists as entry results (unchanged gate); `List<(borrow T)?>`-style elements; forwarding a lent loop element (`size(x)` for a string-owning struct) stays rejected like a borrowed parameter forward.
- Logs: logs/e1b-*.log.

## R1 (contractor, 2026-11-24): replace/swap, owning overwrite, owner-array loops
- New IR instruction `SwapPlaces { left, right }` (two Share references of one type; bitwise exchange, no release). `replace(place, v)` = stage `v` in a hidden owner local (registered for cleanup), form the checked address, `SwapPlaces` with a Share borrow of the local, result = that local (old value, moved by the consumer). Owning overwrite `place = v` (String/List/String-owning aggregate elements and fields) = same exchange, then `end_owned_locals` releases the old value once. Primitive places use the same path (hidden primitive local). Existing S2 String-field fast path unchanged.
- Order: place indices once -> value -> bounds-checked addresses -> exchange. RHS reads of the old value are fine (loans end first); early `return` in the RHS leaves the place intact and the checker/cleanup release staged values. `swap(a, b)`: both place paths left to right, then both addresses, then exchange. Dynamic indices into one collection (and same local/constant index) are BE005 via the loan checker (conservative; no runtime-equal check; documented as a later extension).
- Built-ins with user-precedence like drop/assert (names.rs, types.rs). Diagnostics: TE002 type mismatch, TE004 immutable owner (help names the built-in), TE006 non-place, TE007 swap type mismatch, TE017 reference/Unit places, BE005 overlap/live loans. Old TE022 for `items[i] = owner` removed; `concat` allowed as RHS of an Index String place.
- Other: `loop x in array` over non-copyable elements binds read-only borrows; nested-List TE017 message now "nested lists are not supported yet"; IR `direct_share_owner` accepts share array/List/enum locals; Wasm validation lets SwapPlaces operands through the String-struct field/projection gates; TE022 move-out note updated. Known limit: `if`/`match` expression as an owner RHS fails the heap validator (TE018); evaluate into a local.
- Tests: `crates/memobits-cli/tests/r1_replace_swap.rs` (6): all place kinds source+Wasm (69), RHS reading old / early return, loop over owner arrays, OOB trap, 8,192-iteration capped-memory stress (4,096-byte strings; arrays/lists of strings and Label structs, nested field, share param; memory initial+1 pages), negatives. Mutation (temporary, reverted): skipping the release of the staged local at Wasm cleanup fails the capped run with RE007 (logs/r1-mutation.log); skipping it in lowering is caught statically (TE018). Stale expectations updated: cli.rs (`if` String field now builds), e1/e1b overwrite negatives removed, e1b nested-list text.
- Guide: ownership.mb (3 tests), collections.mb (2 tests); 87 tests. Docs: decisions.md "Shipped E1 and R1 details", CLI README, inventory OWN-02/OWN-07.
- Logs: logs/r1-*.log.

## D1 (contractor, 2026-11-24): tech-debt cleanup
- Item 1 (predicate): the shape rule and its recursion/visited set now live once in `memobits-ir` `scoped_string.rs` (`is_nominal_string_owner`, `OwnerTypeModel`, `OwnerTyView`, `OwnerStructDef`; tuple rule and `is_string_owner_transport` unchanged). Analysis `lower.rs` (`FactOwnerModel`) and `types.rs` (`TyOwnerModel`) are thin adapters; `OwnerFieldShape` and `is_string_owner_struct` are no longer public. Equivalence run (`.local-design/d1/equivalence.sh`, guide + topics/* + apps/*: check/run/test/build/run Wasm/syntax/analyze/ownership + wasm sha256): `before` vs `after1` identical (diff -r empty, 338 files each).
- Item 2: `Local.kind: LocalKind` (`Ordinary` | `DiscardedMatchPayload`) replaces the "discarded match payload" name compare (`scoped_string.rs`); `hidden_local_of_kind` in `lower.rs`; all `Local { .. }` literals in tests gained `kind: memobits_ir::LocalKind::Ordinary`. Equivalence `after2` identical to `before`.
- Item 3: dedicated LE900 in `memobits-wasm` `layout.rs`: "Error-derived type 'T' cannot own heap Strings yet: ..." (direct String, nested struct, array or enum); `d2_nested_owner_transport.rs` expectation updated.
- Item 4: owner temporaries as owned call arguments now staged (`lower/calls.rs`: the "named locals only" exclusion for nominal String structs removed). Stale negatives removed from `d2_owned_struct_transport.rs` (3), `d2_nested_owner_transport.rs`, `d2_record_owner_transport.rs`, `cli.rs`; the wasm validation gate itself is unchanged (still guards non-staged sources).
- Item 5: `replace(place, if/else-if/match ...)` works for owners: `Builder::value_sink` makes the next `if`/`match` deliver each branch value into a hidden local (`deliver_to_sink`, `lower_branch_into`, `lower_block_with`); no heap value crosses a join. Block tails with block-local owners work (delivered before the block's locals end). Limit: `if`/`match` owner values outside `replace` still TE018.
- Item 6: BE005 on `swap` of two projected places gets the note "swap needs two disjoint places; dynamic indices into the same collection are not provably disjoint" (`loans.rs`, `feeds_swap`; not added for overwrite/`replace`).
- Item 7: `Resolution::ignored_tests` removed (nothing read it).
- Item 8: fixed under the staging mechanism: `construction_aliases` (wasm `lib.rs`) skipped only `EndStringLocal` after a `StructNew` with staged String fields; it now also skips `EndStructLocal` and recognizes staged struct/array fields, so `Bag { name: s, items: [l1, l2], inner: l3, k: 7 }` builds. Not changed: a struct literal as a function tail expression.
- Tests: `crates/memobits-cli/tests/d1_cleanup.rs` (8: Error message, owner temporaries source+Wasm, temporaries capped-memory stress with early returns, replace branches, replace branches capped stress, swap note, mixed literal, mixed literal capped stress); stress = 4,096 iterations, 1,024-byte strings, memory initial+1 pages. Mutation (temporary, reverted): not registering the replacement slot for cleanup is caught statically (TE018, `logs/d1c-mutation.log`). Guide: `owner_temporaries_as_arguments`, `replace_with_branch_values`, `mixed_owner_struct_literal` (90 tests).
- Docs: CLI README, inventory OWN-02/OWN-07/AGG-03, decisions.md "Shipped E1 and R1 details". Logs: logs/d1c-*.log.

## G1 (contractor, 2026-11-24): remaining ownership limits
- Item 1 (done): `if`/`else if`/`match` owner values (string, List, String-owning struct/tuple/enum/array) work in every value position (binding, call argument, assignment RHS, function tail, `return`). `take_value_sink` / `finish_value_sink` (analysis `lower.rs`) generalize the D1 `Builder::value_sink`: when no caller installed a sink, the `if`/`match` creates a hidden "branch value" local, each branch (including block tails with block-local owners, nested `if`/`match`, early `return` inside a branch) moves its value into it before the join, and the local is registered for cleanup after the join and returned as a consumed local. No heap value crosses a join; unchosen branch inputs remain owned by their locals (moved-from sources are cleared at run time) and are released with their scopes. Not changed: primitive/borrow results still join through block parameters; discarding an `if` owner value as an expression statement is still TE017 (existing rule).
- Item 2 (done): struct literal (named or record) as a function tail or `return` operand: `owned_result` stages a `StructNew` output in a hidden local (`is_struct_literal_value` keeps captures/calls unstaged). The IR/Wasm gate "requires a direct new local binding" is unchanged; four stale negatives removed from `cli.rs`.
- Item 3 (done): `List<List<T>>`. Gate removed in `typetable.rs`; `check_list_element_support` accepts List elements (arrays of Lists stay TE017). `list_read_receiver`/`list_mutation` accept `outer[i]` places (root must be `var` or `share`); lowering (`list_place`/`list_target`) evaluates the index path, then the element, then forms a checked share address held in a hidden local that `ListPush/ListPop/ListClear` target; `len`/`get`/`contains`/`loop` use the borrowed element address (`get` holds it in a local); `outer[i].borrow()/.share()` accepted for List elements. IR: `validate_type_shape` admits List elements, the List-move capture rule admits a capture consumed by `ListPush`, enum payload validation and Wasm `layout.rs` admit a List payload so `pop()` yields `List<T>?` (`Some(list)` and user enums with List payloads stay gated by the List-move rule). Cleanup needed no new code: `emit_string_storage_cleanup` already recurses type-directed through List elements; growth is bitwise.
- Tests: `crates/memobits-cli/tests/g1_limits.rs` (6): all forms source+Wasm (367), tail struct literals (29), nested lists (265), capped-memory stress for if/match + tail structs (4,096 iterations, 1,024-byte strings, memory initial+1 pages, normal and early returns, per_iteration = 19t+28) and for nested lists (`List<List<u32>>` growth/pop/clear/overwrite/replace, `List<List<string>>`, early returns), negatives. Mutations (temporary, reverted): not registering the branch-value sink for cleanup -> TE018 "return leaves a heap String local in scope" (`logs/g1-mutation-branch.log`); not releasing arm-local owners -> TE018 "owned local scopes differ at a control-flow join" (`logs/g1-mutation-arm.log`); skipping inner-List release in `emit_list_elements_cleanup` -> capped run fails with RE007 guest heap allocation failed (`logs/g1-mutation-nested.log`).
- Stale tests updated: `cli.rs` (4 negatives for struct-literal-in-branch/tail removed, nested-List negative replaced), `d2_owned_struct_transport.rs` (if-with-call-results negative removed), `e1b_lists.rs` (nested-List negative removed).
- Guide: `if_and_match_produce_owner_values`, `struct_literal_as_function_result` (ownership.mb), `nested_lists` (collections.mb); 93 tests; source and standalone Wasm `Result: Ok(i32(42))` with empty stderr.
- Docs: decisions.md "Shipped E1 and R1 details" (G1 facts), inventory OWN-02/AGG-03/COL-03, CLI README. Logs: logs/g1-*.log.

## G2 (contractor, 2026-11-24): divergence join + `try ... else`
- Bug fixed: `if` required `compatible(then, else)` in one direction only, so `if c { a } else { return x; }` reported TE013 ("string and never"). The `if` rule now accepts either direction (like `match` arms); the join type is the non-diverging branch. Owner values needed no lowering change (the G1 value sink already skips diverging branches). Works for primitives, strings, owner structs, Lists, nested ifs, `continue`/`break` in loops, and match arms (diverging first arm too).
- `try`: reserved word. Parser (`crates/memobits-syntax/src/lib.rs`: `try_parts`, `try_match`, `TryArms`) desugars to an ordinary two-arm `match` with marker patterns `$try_ok(v)` / `$try_err(name)`; the checker (`types.rs` `check_try_pattern`) resolves them by the scrutinee's built-in enum (`Ok`/`Err` or `Some`/`None`; `T ?! E` selects the `!` layer). Forms: `try e else name { h }`, `try e else { h }`, `target = try e;` (plain `=`, no-op on failure), `try e;` (discard). The discard form binds the success value (not `_`) because heap `T ! E` needs an explicit `Ok(value)` arm. Precedence: operand = unary level (`expr(13)`), nearest-`else`, statement-start `try ... else {}` ends at `}`. Without `else` in any other position: SE002. Diagnostics: TE013 (handler type), TE029 (non-fallible), TE030 (name on `T?`), BE001 (RHS moved the assignment target).
- Heap error payloads: Error-derived types cannot own heap storage (LE900), so only success payloads exercise release paths. Existing gates seen: `Ok(Some(heap))`, `Ok(list)` returns and struct literals inside `Ok(...)` are TE018/LE900 (unchanged).
- Tests: `crates/memobits-cli/tests/g2_try.rs` (6): divergence all forms (190), results/options (136), heap payloads (138), nested try + loops with continue/break (151), capped-memory stress (4,096 iterations, 1,024-byte strings, memory initial+1 pages, per_iteration = 15t+1027, source + Wasm + capped), negatives (13); `crates/memobits-syntax/tests/g2_try.rs` (8 parser tests). Mutation (temporary, reverted): not registering arm-bound owners for cleanup -> TE018 "return leaves a heap String local in scope" / "owned local scopes differ at a control-flow join" (`logs/g2-mutation-arm-binding.log`).
- Examples: guide `main` uses `try words.get(0) else { return Err(..); }`; `poll` in enums_outcomes uses `try`; new tests `try_else`, `try_without_else`, `diverging_branches` (96 tests); enf-lexer and utf8-validator mains converted.
- Docs: decisions.md "Shipped G2 details", inventory LANG-04/LANG-07, CLI README.

## G3 (contractor, 2026-11-24): range loops
- Syntax: `..` / `..=` lexer tokens; `StatementKind::RangeLoop { binding, start, end, inclusive, body }` parsed only in the `loop name in ...` header (`range_bound` parser flag, cleared inside brackets); a range anywhere else is SE002 "a range `a..b` or `a..=b` is not a value"; the struct-pattern `..` check now tests the `..` token. Bounds are full expressions (`a + 1..b * 2`).
- Checker (`types.rs` `range_bounds_type`): one integer type; an untyped literal bound takes the other bound's type (otherwise i32); TE002 mismatch, TE017 non-integer; immutable loop variable. Other passes: `lib.rs` loop-control, `constants.rs`, `names.rs`, `flow_expr`.
- Lowering (`lower.rs` `lower_range_loop`): bounds once in order into hidden `range cursor` / `range end` locals; half-open header `cursor < end`; inclusive uses a hidden `range remaining` flag (`a <= b`) and clears it instead of incrementing when `cursor == end`, so no `+ 1` runs at the type maximum. Cursor is copied into the variable and advanced before the body (continue re-enters the header).
- Tests: `crates/memobits-cli/tests/g3_ranges.rs` (6: all eight widths at extremes, full u8/i8/u16 ranges, near-max u64 and near-min i64, negatives, empty ranges, literal typing, evaluation order, break/continue/return/nesting, capped-memory owner run with 4,096 iterations, negatives), `crates/memobits-syntax/tests/g3_ranges.rs` (5 parser tests). Guide `range_loops` (numbers.mb; 97 tests); topic examples `basics/loops.mb` and `arrays/main.mb` converted.
- Docs: decisions.md "Shipped G3 details", inventory LANG-05/NUM-06/COL-06, CLI README. Logs: logs/g3-*.log.

## G4 (contractor, 2026-11-24): string interpolation
- Syntax: string literal bodies are split by `split_interpolation` in the lexer (`{{`/`}}` literal braces, `{identifier}` placeholder; lone `}`, unterminated/empty `{`, any non-identifier inside braces is SE001 with a span on the braces). The parser builds `ExprKind::Interpolation(Vec<InterpolationPart>)` only when a placeholder exists; otherwise the unescaped text is the old `StringLiteral` (no artifact change). Resolve (`names.rs`), loop-control, constants and `flow_expr` walk the new node.
- Checker (`types.rs`): TE033 under `alloc = false`; value types integer widths/bool/char/string (also through references); floats TE017 "not supported yet" (decision: a shortest round-trip float formatter is disproportionate in the hand-assembled guest backend; reported to the architect); other types TE017. Loans/moves come from the ordinary read.
- IR: new `InstructionKind::InitInterpolatedString { target, parts }` (`InterpolationPart::{Text, Value}`), wired through validation, scoped-string ownership, the move/loan passes, `value_use_counts`, wasm instruction gate.
- Lowering (`lower/interpolation.rs`): each interpolation shape becomes a synthesized function `$interpolate$N` appended after source functions (IDs of source functions unchanged); the literal lowers to an ordinary call whose result is staged in a hidden owner local, so every String position (binding, argument incl. `.borrow()` temporaries, return/tail, struct field, tuple/array/List element, `Some(..)`, branch/match values, `var` replacement) works with exact cleanup. Fixed a gap: `lower_with_temporary_owner`, `is_direct_string_call`, `calls.rs` temporary-receiver cases and `.borrow()` of a temporary treat interpolation like a String-returning call.
- Wasm (`interpolation.rs`): 64-bit length sum, single `reserve` + descriptor store, then `memory.copy` / `int_write` / `char_write` / inline `true|false`; helpers `int_len`, `int_write`, `char_write` emitted only when reachable; text pieces share the literal static-data table. A trap (HeapAllocation) only before the block is reserved.
- Tests: `crates/memobits-cli/tests/g4_interpolation.rs` (13: all integer widths with min/max and decade boundaries vs Rust formatting (~230 cases), bool/char/unicode widths, placeholder shapes and brace escapes, read-without-move, every value position, `mb test`, static literal under alloc=false, TE033 in check/build/run, 16 SE001 forms, unsupported types/unknown names, BE005/BE001 loans, 4,096-iteration stress with early returns/continue/break/short-circuit/struct fields/List in memory capped to initial+1 pages (source, Wasm, capped Wasm), allocation-failure trap), `crates/memobits-syntax/tests/g4_interpolation.rs` (4). Guide `text.mb`: `string_interpolation`, `interpolation_braces`, `interpolation_follows_loans` (100 tests).
- Equivalence: `.local-design/g4/equivalence.sh` (adapted from d1; a baseline binary built from `git archive HEAD` runs the same example sources from the repo root so embedded paths match): `.local-design/g4/before` vs `.local-design/g4/after` identical (14 Wasm sha256, 112 command captures) before the guide gained interpolation tests.
- Docs: decisions.md "Shipped G4 details", inventory STR-06, CLI README, utf8-text-slice.md. Logs: logs/g4-*.log.

## G5 (contractor, 2026-11-24): module-level constants
- Syntax: `ItemKind::Const { public, name, ty, value }` (`[pub] const NAME: T = expr;`, annotation required, SE002 otherwise); `const` is a reserved word; `[v; NAME]` repeat counts may name a constant (`IntegerLiteral.raw` holds the name until folded); new `ExprKind::TypedNumber { raw, ty }` (a numeric literal with a fixed type, created only by the const pass).
- Pass: `crates/memobits-resolve/src/consts.rs`, called at the end of `resolve()` (after names/imports/visibility) over every loaded module. A typed evaluator mirrors the checker's literal typing and the static-expression rules (LE001/LE002/LE003, casts per NUM-04, u32 bit/shift per NUM-05, floats IEEE with f32 rounding, comparisons, `&&`/`||`/`!`, unary `-`/`+`); new codes LE004 (cycle, names the path) and LE005 (not a constant: call, function/type name, block/if/match, array, interpolation); TE017 for unsupported const types and for non-`u32` array lengths. A rewriter (scope-aware: params, lets, destructures, loops, match arms, generics shadow) inlines values: bool/char/string become ordinary literals, numbers become `TypedNumber`; `{NAME}` folds into text (all-const interpolation is a static literal); `array<T, SIZE>` / `Lane<SIZE>` / `[v; SIZE]` become integer literals; `NAME = ...` is TE004; a `match` arm identifier equal to a visible constant is TE017 (G7 decides constant patterns). Const items and the `use` items that imported them are removed, so analysis never sees them (analysis only gained `TypedNumber` handling: type, lowering, constant analysis, static index check, flow).
- Resolve: consts join the module's binding names (ME005), reference validation (ME006/ME007; ME008 when used as a type; ME009 as entry/export); single-name type arguments of nominal types may name an imported const (`names::Requires::TypeOrConst`). Standalone `mb analyze` / `mb ownership` fold a single file's constants (`fold_standalone_constants`).
- Tests: `crates/memobits-cli/tests/g5_const.rs` (13: every type at extremes source + Wasm, expressions/casts/operators, cross-module + out-of-order + qualified/aliased imports + visibility, array length / const argument / repeat count / range bound / constant index, interpolation, shadowing, alloc=false string consts with no heap growth, exact error codes for overflow/zero/shift/literal/type/annotation/types, cycles (single, three-way, cross-module, reported once), non-constant initializers, namespace + read-only + patterns, `mb test` + standalone commands, static checks at use sites), `crates/memobits-syntax/tests/g5_const.rs` (4). Guide: `module_constants` (numbers.mb), `constant_array_length` (collections.mb; imports `numbers::DAYS_PER_WEEK`): 102 tests, source and standalone Wasm `Result: Ok(i32(42))` with empty stderr.
- Equivalence: `.local-design/g5/equivalence.sh` run with ROOT = a `git archive HEAD` copy (const-free sources, identical embedded paths) once with a baseline HEAD binary (`g5/before`) and once with the new binary (`g5/after`): identical (14 Wasm sha256, 112 command captures).
- Docs: decisions.md "Shipped G5 details", inventory IDEA-04 (const shipped; globals/static still open), CLI README. Logs: logs/g5-*.log.
- Open / for the architect: a `match` identifier equal to a constant is TE017 until G7 (could be argued to allow shadowing); imported single-name type arguments lose the ME008 "not a type" message only when the import is a constant (other imports keep it); unused constants are still evaluated and report errors; float interpolation stays unsupported for constants.

## G6 (contractor, 2026-11-24): numeric APIs
- Shared semantics: `crates/memobits-syntax/src/numeric.rs` (`IntKind`, wrapping/saturating/checked, shifts, bitwise, `is_literal_tree`) used by `memobits-analysis/src/constants.rs` (static folds incl. `wrapping_*`, `saturating_*`, `bit_*`; width-aware LE003 `u8 shift count must be less than 8`) and `memobits-resolve/src/consts.rs` (const items, all widths).
- Checker (`types.rs`): bitwise/shift operators and compound assignment for all integers (count `u32`, TE002; non-integer TE007), new `integer_method` for `bit_*`/`wrapping_*`/`saturating_*`/`checked_*` (checked returns `T?`; skipped when a user extension defines the same name); literal-only bitwise/shift expressions keep the `u32` default.
- IR/lowering: new `BinaryOp`s (`WrappingSubtract`, `WrappingShiftLeft/Right`, `Saturating*`, `Checked*`), validation relaxed to all integer widths (u32 count for shifts, `T?` output for checked); `wrapping_neg`/`checked_neg` lower as `0 - x`.
- Wasm: `crates/memobits-wasm/src/numerics.rs` (normalization of 8/16-bit results, i64 flag arithmetic, checked results in the scalar-option frame cell); trap message now "shift count must be less than the bit width".
- Gates removed / tests updated: `wp20_s_gaps.rs` (signed shifts rejected -> accepted, i32 count and f64 compound still rejected), `cli.rs` u32 bit-ops negatives and trap message. Docs: decisions.md "Shipped G6 details", inventory NUM-03/05/06, CLI README, wasm-backend.md. Guide: numbers.mb wrapping/saturating/checked/bit tests (105 tests).
- Tests: `crates/memobits-cli/tests/g6_numerics.rs` (18). Logs: logs/g6-*.log.

## G7 (contractor, 2026-11-24): patterns
- Syntax: `PatternKind::{Literal(Box<Expr>), Constant { path, value }, Or(Vec<Pattern>)}`, `MatchArm.guard: Option<Expr>`; parser: `pattern()` = alternatives separated by `|`, `literal_pattern()`, `if` guard before `=>`; `[v; name]` accepts any identifier (`is_identifier` shared with `name()`).
- Resolve: names pass covers or-patterns and guards; the const pass (`consts.rs`) turns a bare name / `m::NAME` that is a visible constant into `PatternKind::Constant` (float constants TE017; try handler names excluded) and scans guards.
- Checker (`types.rs`): scrutinees may be scalar/string (in place); `check_literal_pattern`, `check_or_pattern` (per-alternative scope, same names/types, locals of later alternatives remapped onto the first and truncated), `check_guard` (bool; owned matches get guard twins and `guard_alternatives`), `MatchArmFact { pattern, alternatives, guarded, guard_alternatives }`, `MatchPattern::{Literal, Or}`, `PatternLiteral`; limits TE017 (`unviewable_binding`, `literal_in_string_tuple`). `patterns.rs`: `Lit`, `Or`, bool constructors.
- IR/Wasm: new `InstructionKind::StringEquals { strings: [Operand; 2] }` (validation, ownership transfer, loans, wasm gate, a length check plus byte loop).
- Lowering (`lower.rs`): rows per or-free alternative (`MatchRow.full/guard_full`), `bind_arm`, guarded leaf (guard views -> `Branch` -> real bind -> body, failing edge continues with the remaining rows), literal column with `literal_test`, scalar/string scrutinee cells, `bind_in_place` re-lends a whole-value binding.
- Tests: `crates/memobits-cli/tests/g7_patterns.rs` (20: every literal kind at all widths/extremes, nested literals incl. static/heap strings, in-place string compare, or-patterns, guards with fallthrough/short-circuit/division guard, constants across modules, variant-vs-const precedence, exhaustiveness/reachability/type negatives, limits, repeat counts, 4,096-iteration owned guard stress at initial+1 pages with early returns, or+guard heap stress, heap temporary scrutinee, mutation check that keeping the payload traps under the cap); parser test replaced; `match_enums.rs`, `match_cli.rs`, `g5_const.rs`, `nested_patterns.rs` updated for removed gates. Guide: `literal_patterns`, `constant_patterns`, `or_patterns`, `guards` (109 tests).
- Docs: decisions.md "Shipped G7 details", inventory PAT-02, CLI README, enum-implementation.md, topics/enums README, syntax README. Logs: logs/g7-*.log.
- Open / for the architect: guard cannot see String-owning aggregates (TE017); `string ! E` literal arms stay TE018; variant with String + other payloads and an unbound String still fails validation (pre-existing); each leaf re-lowers the guard expression (code size only).

## G8 (contractor, 2026-11-24): `~` and `Self`
- `~x`: lexer symbol `~` and prefix operator (same level as `-`/`!`); `numeric::complement` (shared by `consts.rs` and `constants.rs`); checker: integer only (TE007 "`~` requires an integer, found T"), expected int type goes to the operand, literal-only operand defaults to `u32` (`is_literal_tree` includes `~`); IR `UnaryOp::Complement` (validated: integer in = out); Wasm `numerics::emit_complement` (xor -1 + normalize). Primitive-only: no `Not` interface added.
- `Self`: `memobits-syntax/src/self_type.rs`, run at the end of `parse`; inside `extend` (all three forms) substitutes the target type (arguments included) in types, struct literals (type arguments filled), destructure paths and `Self::Variant` paths (expressions, patterns); outside `extend` and in interface declarations SE002 (the later NE003 also fires for the same span). No static-style calls exist, so none handled.
- Interface decision: `Self` in interface declarations rejected ("not supported yet"): existing machinery (bounds, `T::Output` projections, `of Interface` selection) has no `Self`-return model; would need new dispatch semantics.
- Tests: `crates/memobits-cli/tests/g8_complement_self.rs` (12); `wp20_s_gaps` updated (`~x` on a nominal type is TE007, was SE001). Guide: `bitwise_complement`, `self_in_extend_blocks`, `self_in_interface_extensions` (112 tests).
- Docs: decisions.md "Shipped G8 details", inventory NUM-06 / FN-02 / IDEA-06, CLI README. Logs: logs/g8-*.log.
- Open / for the architect: untyped `~0` is `u32` (hashing convention) not `i32`; duplicate SE002+NE003 for misplaced `Self`; method calls with struct arguments are still gated (pre-existing, TE017), so Self-typed parameters are tested through `Add` operands.

## F1 (contractor, 2026-11-24): method arguments, call results, literals, `Self`
- Method arguments: `check_call_argument` (analysis `types.rs`) is the single per-argument check used by free calls, inherent methods (including generic nominal) and `of I` interface-selected calls; lowering uses the new `lower_call_argument` (`lower/calls.rs`) for `lower_call` and `lower_selected_call` (receiver rules untouched). Removed the TE017 on `q.eqx(r)` and the bogus TE002 "expected R, found borrow R" for `.borrow()` arguments.
- Call results: `stage_fresh_call` (`lower.rs`) stages a fresh call output of type String / String-owning aggregate in a hidden `call result` owner local. Applied in `owned_element` (array, List literal, `push`, replace value), tuple elements, enum payloads (`Some`/`Ok`/user variants), `owned_result` (function tail and `return`), and the `push_str` suffix. IR validation is unchanged (the rule "assigned directly to a whole local" now holds because the call is bound to the hidden owner). Positions that already worked (binding, assignment, owned argument, struct field, branch sinks) keep their old IR shape.
- Literals: new `memobits-syntax/src/literals.rs` (lexer): `0x`/`0X`, `0b`, `0o`, `_` separators in every integer and float literal; canonical decimal `u128` spelling goes to the AST, so everything downstream (const, patterns, ranges, folding) is unchanged. Errors SE001: empty digits, `_` right after prefix, trailing `_`, invalid digit (`0xFFu8` fails: no suffixes), missing exponent digits, value above `u128::MAX`. `ExprKind::Number` / `IntegerLiteral.raw` now hold the canonical text (`1_000` -> `1000`).
- `Self`: `memobits-resolve/src/names.rs` skips NE003 for the name `Self` (SE002 already reported at that span).
- Tests: `crates/memobits-cli/tests/f1_followups.rs` (11): method arguments (inherent, `of I`, generic nominal, owned/borrow/share, struct/tuple/enum/array/List/String/Option) over source + standalone Wasm and diagnostics; call results in every position; tail/`return`; capped-memory stress (memory max = initial+1 page, 4,096 iterations x 4,096-byte strings, early returns inside methods) + mutation check (no `xs.clear()` traps with "guest heap allocation failed"); literal table at every width with extremes (29 rows), const/pattern/array-length/repeat/float contexts, 16 lexer negatives, 9 range-check negatives (TE008), `Self` single diagnostic. Stale tests updated: `d2_owned_struct_transport.rs` (the `fn forward() -> Label { make() }` gate case removed), `memobits-syntax/tests/parser.rs` (type-argument count raw is `1000`). Guide: `numbers.mb` `radix_literals`, `ownership.mb` `call_results_in_every_value_position`, `method_arguments_follow_function_rules` (115 tests).
- Docs: decisions.md "Shipped F1 details" (and G8 `Self` note), inventory TYPE-01 / OWN-01 / FN-02, CLI README. Logs: logs/f1-*.log.
- Open / for the architect: AST `Number` raw text is canonical (separators/radix removed) so diagnostics print decimal; `1._5` still lexes as `1 . _5` (field access error, not SE001); a tuple holding an enum that owns a String is still a validation error (F2 composition); `string ! E` call results still need the immediate match; List-returning call results keep their own gate.

## F2 (contractor, 2026-11-24): heap payload composition
- Ownership model: `List<T>` joined `String` as a heap leaf in the shared owner predicates (IR `owns_string_aggregate`, `is_nominal_string_owner` adapters in IR/analysis lowering/types, tuple rules, analysis `contains_string_owner`); `heap_strings()` seeds every local whose type holds a List inside an aggregate; `owns_string_storage` includes a bare List; `local_move_source` accepts List-to-List moves; List captures feeding `EnumNew`/`StructNew`/`ArrayNew`/`ListPush` pass the IR List-move check. Wasm: struct List fields (`layout.rs`), List array elements (`supported_type`), `construction_aliases` (staged List/enum fields, `EndListLocal`), borrow validation counts enums/Lists and accepts lent places from element/field/variant addresses.
- Lowering (`lower.rs`): `lower_variant` stages fresh owners (`enum owner payload`); `stage_fresh_call` also stages List results; struct literals stage List and enum fields; tuple elements stage enum/array/List owners; List places for `Field` chains (`list_place`, `list_read_receiver`, `list_mutation`); array element gate lifted (`arrays.rs`, the tuple-with-List gate removed).
- `string ! E`: removed the special validator rules (`returns_heap_ok` immediate-match check, the `Result` exclusion in `owned_aggregate_call_argument` and `lower_call_argument`, `is_heap_result_enum`, the VariantAddr consuming-match check); it is an ordinary String-owning enum. Literal pattern on `Ok` works.
- Mixed variants: IR String `VariantExtract` accepts a non-final extraction when a later extraction of the same owner consumes the cell. Tuples with enums: `tuple_owns_string`, `supported_nested_string_tuple` and the tuple transport gate accept enum/array/List fields (nominal-struct fields keep the TE017 gates); StructNew accepts a consumed enum owner local.
- Guards: removed `unviewable_binding` / `literal_in_string_tuple` (TE017); Wasm borrow validation treats locals assigned only from Borrow element/field/variant addresses as lent places and roots chains at them.
- Range echo: `memobits_syntax::literal_spelling` (thread-local original spelling per literal span, verified against the canonical text) used by `literal_text` (integer patterns) and the constant array index message; the negative-literal pattern operand span now covers the digits only.
- Tests: `crates/memobits-cli/tests/f2_payloads.rs` (14; source + standalone Wasm per item, capped stress for payloads/storage/guards with 4,096 iterations and early returns, mutation check that keeps a list-carrying variant and a heap `string ! E` in a never-emptied List and traps); stale negatives updated in `d2_nested_result_storage.rs`, `g1_limits.rs`, `tuple_nested_arrays.rs`. Guide: 7 new `test fn`s (122 tests).
- Docs: decisions.md "Shipped F2 details" (G1/G2/G7/F1 limits marked lifted), inventory OWN-01 / PAT-02 / OUT-04 / COL-03, CLI README. Logs: logs/f2-*.log.
- Open / for the architect: a nominal struct with a direct String/List field plus a heap-owning enum or tuple field cannot move by value into a call (TE017 with a clear note; widening the shared transport predicate to enum fields was judged a separate step); moving a List out of a field/element is still TE022; `literal_spelling` is a thread-local side table (AST `Number` text stays canonical).

## F3 (contractor, 2026-11-24): float interpolation, literal spellings, struct transport
- Float formatting: `{x}` for f32/f64 prints Rust `Display` text. Guest algorithm: Burger-Dybvig shortest digits on 40-limb big integers, no tables (`crates/memobits-wasm/src/float_format.rs`, eight functions from a small text assembler, 1,168-byte static scratch), emitted only when a float placeholder is reachable (+~1.7 KB on a minimal program); constants fold with Rust's formatter (`consts.rs`). TE017 for floats removed from analysis types, resolve consts and the IR validator.
- Exactness: f64 table >7,000 values and f32 table >3,000 values (boundaries, every power of ten and two, +-1 ulp neighbors, 2,500 seeded random bit patterns per width), NaN/inf/zeros, all identical to `format!("{}", v)` from source and from standalone Wasm; unit test over ~10,000 more values.
- Equivalence: `.local-design/g5/equivalence.sh` against a HEAD build (guide float test excluded from the compared copy): 14 artifacts and 337 command outputs identical (logs/f3-equivalence-*.log).
- Tech debt: `NumberLiteral { canonical, written }` is the payload of `TokenKind::Number` / `ExprKind::Number`; thread-local `SPELLINGS` and `literal_spelling` deleted; diagnostics unchanged.
- Transport gate: shared predicate gained `OwnerTyView::Heap` (enum/tuple that owns heap storage; plain enums/tuples are primitive fields) in the IR, analysis-types and lowering adapters; a struct with String/List plus enum/tuple fields moves into calls. Capped stress (4,096 iterations, consumed/ignored/early-return/returned, memory capped to initial+1 page) plus a leak mutation that traps. F2's gate test is now positive.
- Perf/config: workspace `Cargo.toml` builds the wasmi crates at opt-level 3 without debug assertions in dev/test (table tests: seconds instead of minutes).
- Tests: `f3_floats.rs` (9), `memobits-syntax/tests/f3_literals.rs`, unit test in `float_format.rs`; G4/G5/F2 float and gate negatives rewritten. Guide: `float_interpolation` in text.mb (123 tests).
- Docs: decisions.md "Shipped F3 details" (G4 float note updated), inventory STR-06, CLI README. Logs: logs/f3-*.log.
- Open / for the architect: matching a List-payload enum field of a struct in place (`match m.k { Many(l) => .. }`) fails IR validation (TE018) even without calls; a struct with only an enum/tuple field is still not a transport owner; format specifiers remain open.


## H1 (contractor, 2026-11-25): function values (no captures)
- Syntax: `fn(T, borrow U) -> R` types (AST path `\0fn`, result last, `\0unit` when omitted); `ExprKind::Function` (`fn(x: i32) -> i32 => e`, `fn(x) { .. }`, `fn(x) => e`); `=> expr` bodies for functions, `extend` methods and tests (optional trailing `;`). Resolver walks them (`names.rs`, `consts.rs`, `canonical_type_inner`), `self_type.rs` rewrites `Self` inside them.
- Checker (`types.rs`): `Ty::Function` was already the type of a function name; now a first-class value type. `anonymous_function` checks the body as a separate function with the enclosing scopes parked in `outer_scopes`; a hit there records a capture and reports TE017 "closures that capture variables arrive in the next step". Anonymous functions get ids from the shared specialization registry and are lifted (`FunctionFacts::anonymous`, parent facts list `anonymous_functions`). `generic_function_value` specializes a generic function from the expected function type (duplicates the evidence/registration code of `generic_identity_call` on purpose, so existing function ids and Wasm bytes do not move). Equality, `borrow`/`share` function parameters and List parameters/results in function types are diagnosed.
- Lowering: a function named as a value is `Constant::Function(id)`, a direct call keeps `Source::Function`; an anonymous function is lowered in a nested `Builder` when the parent meets it and parked in `AnonymousFunctions`; the program loops move it to its id slot. Function values are scalars everywhere a primitive is copied (`Type::is_scalar`): `owned()` copies, List `push`/`get`/`pop`/loop, match bindings.
- IR: `Type::is_scalar`, `Constant::Function` (validated against the function's signature), function types allowed as fields/payloads/elements/reference targets, Copy of a function value, a loaded callee only reads. `scoped_string.rs`: `call_targets` (a call through a value reaches every address-taken function of the same signature) feeds the heap-ownership graph, call result validation and owned transfers.
- Wasm: new `function_values.rs` erases function types to `u64` (heap facts are computed first on the typed program), table/element sections (slot 0 empty, elements at offset 1), `i64.const slot`, bounds check with trap reason 13 `InvalidFunction` (runtime `TrapReason::InvalidFunction`, docs/design/wasm-backend.md table + new "Function values" section), `call_indirect` with one Wasm type per distinct signature; exported/entry signatures with function values are LE900.
- Decisions taken (report to the architect): `extern` functions are values (plain Wasm imports; source `mb run` links them, standalone Wasm cannot run host imports as before); test functions are never values (NE001 hint extended); a field call falls through to the field only when no method of that name exists (method wins, builtin method names win); `borrow`/`share` function parameters are TE017 until H2; function types with List parameters/results are TE017; an `=>` anonymous function without `->` and without an expected type infers its result from the body; a trailing `;` after a named `=>` body is optional; function value equality is TE007.
- Evidence: `crates/memobits-cli/tests/h1_function_values.rs` (18), `crates/memobits-syntax/tests/h1_function_values.rs` (4); capped-memory run (memory max = initial + 1 page, 4,096 iterations x 1,024-byte strings, early returns, owners through `fn(string)`, `fn(Label)`, `fn(Outer)`, `fn(borrow string)`, `fn(u32) -> string`, `fn(u32) -> Label`) passes; the same program leaked before the heap analysis followed indirect calls (RE007 "guest heap allocation failed"). Guide `functions.mb` (6 tests, 129 total), guide source and standalone Wasm print `Result: Ok(i32(42))` with empty stderr. Equivalence (`.local-design/g5/equivalence.sh` vs the HEAD build): 338 artifacts/outputs identical except the guide (new module, shifted main.mb lines). Logs: logs/h1-*.log.
- Open / for the architect: `borrow fn`/`share fn` parameters and captures are H2; List parameters/results in function types stay gated (the IR requires direct internal calls for Lists); a type check on `call_indirect` is the native Wasm trap (unreachable for typed values); `mb analyze FILE` still cannot check generics/extensions (standalone mode), unchanged.

## H2 (contractor, 2026-11-25): non-escaping closures (`borrow fn` / `share fn`)
- Design: see decisions.md "Shipped H2 details" (probe-based capture inference, captures as trailing borrow/share parameters, `ClosureNew`, loans via provenance, frame environment, thunk table, one indirect-call convention with trailing i32 environment).
- Items: 1-5 done; 6 done as user-written helpers (no built-in `each`).
- Tests: h2_closures.rs (18: primitives, strings/structs/Lists, let-bound, nested/recursion, function-typed params, alloc=false, Lists in function types, wasm convention, capped 4,096-iteration heap run + mutation check, loan/escape/access negatives). Guide 134 tests, source and Wasm `Result: Ok(i32(42))` with empty stderr.
- Changed tests: h1_function_values (capture test replaced), cli.rs (4 indirect-List gates removed).
- Open: `f(make(), 0)` through a value passes a temporary List owner (direct `take(make())` is separately gated); a `borrow fn` parameter cannot be written `.borrow()`; probe checks multiply for deep closure nesting; error-name promotion depends on mutation diagnostics quoting the variable.


## H2b (contractor, 2026-11-25): structural capture analysis
- Replaced probe-and-promote capture inference (`Probe` mode, `capture_view`, promotion keyed on quoted variable names, cost ~(promotions+1)^depth) with one analysis pass per function literal (`BodyMode::Infer` in `closure_body`, `anonymous_function` in `crates/memobits-analysis/src/types.rs`). Enclosing names are bound as hidden share parameters; the checker records uses (`lookup`) and writes (`note_write` at: assignment/compound-assignment targets and projections via `check_place_writable`, `replace`/`swap` places, `push`/`pop`/`clear` (`types/lists.rs`), `push_str`, `.share()` conversions, a share reference passed to a `share` parameter, `share self` method receivers, nested literals' share captures). Results are cached per literal for the outermost literal's lifetime (`capture_cache`), so each body is analysed once and checked once for real. `root_note` stays as diagnostic text only.
- Behavior: 16 scratch programs (`/tmp/h2b/cases`, mutation through projections, nested closures, read-only use, function-typed captures, swap/replace, push/push_str/clear, share args, shadowing, immutable/borrow-param captures) produce byte-identical `mb check`/`mb run` output before and after, except `share self` receiver in a closure, which now works (was TE018 "borrow cannot strengthen reference access").
- Timing (debug `mb check`, nested `share fn` literals): 6 levels 65 ms -> 15 ms, 8: 626 ms -> 20 ms, 10: 7.1 s -> 24 ms, 12: 77 s -> 35 ms.
- Temporary List owner through a function value (`f(make(), 0)`, `indirect(f, make(), 0)`) and direct `take(make(), 0)`: all accepted on source and Wasm; no stale negative remained (the H2 note that the direct form is gated was out of date). Capped-memory test (initial + 1 page, 4,096 iterations, 1,024-byte strings in List owners, four routes) plus a mutation check that keeps a String per round and traps.
- Tests: `h2_closures.rs` 18 -> 28 (deep nesting 6/12 levels with a 2 s bound, nested projection, share self, nested closure, read-only capture of a variable mutated outside, builtin mutators/overwrite/swap/replace/share args, function-typed captures, List owner leak + mutation, List owner acceptance). Logs: `logs/h2b-*.log`.

## H3 (contractor, 2026-11-25): generics
- Design: see decisions.md "Shipped H3 details" (`types/generics.rs`: structural unifier over written parameter types, two-pass argument checking, per-bound evidence with the parameter name, one shared specialization registration for calls and function values; `where T: A + B` parsed as one bound per interface).
- Items: 1-6 done. Explicit call-site type arguments, method-level type parameters, `where` on type declarations and const parameters as values stay open (documented).
- Tests: `h3_generics.rs` (16); cli.rs gate tests updated (generic forms that used to be rejected now work); guide +5 (139); example generics-operators 6 tests.
- Logs: logs/h3-*.log.


## H4 (contractor, 2026-11-25): Box<T>
- Design: see decisions.md "Shipped H4 details" and docs/design/box.md. Checker type `Ty::Box`; IR stores a one-element `List<T>` (deviation from the single-pointer-word layout in the WP text: 12-byte descriptor); `Box(v)` is a list literal, `unbox(b)` is move-into-hidden-list + `ListPop` + `VariantExtract`; auto-deref is `Projection::Deref` (= `ElementAddr` of element 0) driven by `FunctionFacts::box_exprs`; `match` consumes an owned box or lends through the element; nested patterns see through in in-place matches; `.borrow()` deref coercion via `box_coercions`; Wasm `recursive.rs` emits one release function per recursive owner type.
- Items: 1-5 done (see limits in decisions.md: built-in methods do not auto-deref, owned-match payload boxes cannot be passed directly as owned arguments, single-word layout not done).
- Tests: `h4_box.rs` (18); guide +2 (141); example apps/tree (4 tests).
- Logs: logs/h4-*.log.


## H4b (contractor, 2026-11-25): iterative release, single-word Box, built-in method auto-deref
- Design: decisions.md "Shipped H4b details", docs/design/box.md, docs/design/wasm-backend.md. (1) `recursive.rs`: `release_T` + shared `drain`; deferral of box/list positions that mention a recursive type onto intrusive worklists (global heads; links in the free-list word of box block headers and the `data` word of list descriptors; no allocation); constant call-stack depth. (2) IR `Type::Box`, `box_cell.rs` (4-byte cell), Box built with `EmptyList`/`ListPush`, emptied with `ListPop`, addressed by `ElementAddr` index 0; the List-based interim is gone. (3) built-in `len/get/contains/index_of/is_char_boundary/byte_at/scalar_at/push/pop/clear` through a named box (`Checker::builtin_receiver`, `lower_read_receiver`/`list_place` Deref). (4) consuming-match nested patterns through a box payload stay TE017 (needs partial-move tracking inside the box); `[prelude]` mapping of Box/List not supported (ME005, name collides with the virtual alloc module).
- Tests: `h4_box.rs` (25), wasm layout test (box 4 bytes vs list 12), guide +2 (143).
- Logs: logs/h4b-*.log.


## H5 (contractor, 2026-11-25): owned (escaping) closures
- Design: see decisions.md "Shipped H5 details". Per function type with owned capturing closures (whole-program discovery in `check_*` passes, `types/owned_fn.rs`) the checker represents the type as a tuple-module IR struct wrapper `{ call: fn, env: Box<Env> }` (`Env` = compiler enum, `Plain` + one variant per closure literal). New IR `ClosureOwned` (box -> callable word) and `ClosureReadOnly`; the Wasm thunk of an owned closure adds variant field offsets to the environment pointer; trap reason 14; mutating flag in bit 31 of the slot word only in modules that have such closures.
- Items: 1 done (positions, move captures, mutation rule dynamic), 2 done (type-directed release through the ordinary owner predicates; copy of an env closure rejected; plain function values copyable by `let`), 3 done (lend to `borrow fn`/`share fn`, second-class closures cannot become owned), 4 done (heap block in the alloc layer, TE033 with `alloc = false`, per-shape release = enum variant release), 5 done (adders, counters, Lists, struct fields with captured strings, generic helpers).
- Tests: `h5_owned_closures.rs` (16); h1/h2 stale negatives updated; guide +5 `test fn`s.
- Open / for the architect: representation is chosen per exact function type by whole-program discovery, so the first capturing closure of a signature changes copy rules for every value of that type (see decisions); the mutation rule is dynamic (trap 14), not static; `f = make()` (assignment to a whole owner local) is the general struct-owner gate, use `replace`; unannotated `let f := fn(..)` with captures stays second-class.
- Logs: logs/h5-*.log.


## BK1 (contractor, 2026-11-25): guest allocator size classes
- Design: decisions.md "Shipped BK1 details", wasm-backend.md "Guest allocator (BK1)". `string_heap.rs`: 52 size classes (4-byte steps to 32, four per octave to 65,536) with an i64 bitmap and heads in a 216-byte static table (`heap_table` in lib.rs); exact-size first-fit list (`FREE_GLOBAL`) above the limit; header format unchanged, so the H4b worklist is unaffected.
- Benchmarks (debug build, source run): 60,000 small frees then 60,000 100-byte allocations 9.1 s -> 0.05 s (old default-fuel run exhausted fuel); 20,000: 1.2 s -> 0.03 s. e1b_lists 0.58 s -> 0.63 s (noise). Code size: +453 bytes in heap programs (guide, apps/tree, topics/basics); heap-free examples byte-identical.
- Tests: `bk1_allocator.rs` (5). Equivalence harness: 12 of 15 artifacts byte-identical, outputs identical everywhere. Logs: logs/bk1-*.log.

## H5b (contractor, 2026-11-25): uniform function value ownership and `var fn`
- Decision implemented: decisions.md "Owned closure mutation and function value ownership" (user chose C); facts in "Shipped H5b details". H5 interim notes above (per-type switch, trap 14, plain copies) are superseded.
- Representation: every function type is the wrapper `{ call, env: Box<Env> }` interned on first use (no discovery passes; `types/owned_fn.rs` is now a thin table accessor). `Ty::Function` carries a `var` flag; `fn` and `var fn` of one signature share the wrapper.
- Removed: whole-program passes, `ClosureReadOnly`, `ClosureOwned.mutating`, trap 14 / `MutatingClosure`, bit-31 flag and call masks, `plain_values`/`plain_locals` copies in lowering, `callee_is_mutable`.
- Checker: `var fn` parsing (`\0fn`,`var` path), TE017 + help for a mutating closure in a `fn` position, TE004 for calling/lending a `var fn` through an immutable place, `fn` to `var fn` coercion in `compatible`, TE017 for `var fn` to `borrow fn` and for `borrow var fn` parameters, TE018 message for assigning a whole function value, array `loop f in table` over function elements borrows.
- Tests: new `h5b_function_ownership.rs` (8); `h1_function_values.rs` (get/field-read/copy cases rewritten to in-place calls, `replace`, `borrow fn` lending), `h5_owned_closures.rs` (counters are `var fn`, trap test replaced by a read-only call test, per-type test moved to h5b). Guide `functions.mb` (+1 test, 149).
- Open: a `var fn` in an enum payload / `T?` cannot be called through a `match` binding (read-only); whole-value assignment still needs `replace`.


## F4 (contractor, 2026-11-25): whole-owner reassignment, const values, method type parameters, type bounds
- Items 1-4 done. Design: decisions.md "Shipped F4 details". (1) `x = v` on a whole `var` local / `share` parameter of a String-owning struct, record, tuple, enum or a function value (`fn`/`var fn`): `lower.rs` stages the RHS into a hidden owner local (`stage_replacement`), then emits IR `Assign { initialize: false }` (non-parameter local; the ownership pass re-initializes a moved-from local, the Wasm `Assign` releases the old value once and clears the source) or the R1 `SwapPlaces` exchange (share parameter). `string`/`List`/`Box`/array locals and stored share handles keep their existing paths (examples equivalence harness byte-identical). IR validation allows struct/enum `Assign` without `initialize` on a mutable non-parameter local. The H5b TE018 "function value cannot be assigned as a whole" is removed; `share fn` parameters get a clear TE018 ("cannot be reassigned as a whole yet"). (2) const parameters as values: `PathTarget::Const(value)`, `Checker::generic_consts` for repeat counts, resolver (`names.rs`, `consts.rs`) accepts the name inside generic items, TE004 for assignment. (3) method-level parameters: syntax `InterfaceMethod.generic_parameters/bounds` (inherent methods only), `Checker::infer_call` shared with function calls (`types/generics.rs`), `generic_method_call` registers a `GenericMethodSpecialization` keyed on receiver, function type, both argument lists and evidence; generic methods have no eager id/body check. (4) type `where` bounds: `Def::Generic.bounds`, `TypeTable::generic_bounds`, `Checker::type_bound_evidence`/`check_type_bounds` (annotation, `type_path`, declared signatures/fields/payloads via `validate_declared_type`), evidence stored on the specialized extension candidate and forwarded to method specializations.
- Tests: new `crates/memobits-cli/tests/f4_followups.rs` (8, source + standalone Wasm; capped-memory run of 4,096 iterations with 4,096-byte strings; mutation check in logs/f4-mutation.log and logs/f4-mutation2.log: skipping the release in Wasm `Assign` fails the capped run with RE007). Stale negatives updated in `cli.rs`, `d2_owned_struct_transport.rs`, `d2_nested_owner_transport.rs`, `d2_record_owner_transport.rs`, `h5b_function_ownership.rs`. Guide: ownership.mb +1, functions.mb +1, generics.mb +3 (154 tests); no guide/example used `replace` only as a whole-reassignment workaround (all remaining uses read the old value).
- Open: `share fn` parameter whole reassignment; explicit call-site type arguments; generic methods in interface declarations and `extend T of I`; pre-existing: a struct whose array-of-String field is built from a named array local fails IR validation (TE018) regardless of reassignment; `T::Output`-style projections in bounded-type methods need the evidence of every bound on `T` only (no nested projections).
- Logs: logs/f4-*.log.


## S5-1 (contractor, 2026-11-25): `mb fmt`
- Shipped: `mb fmt [--check] [--project PATH | FILE...]` (decisions.md "Source formatting" and "Shipped S5-1 details"; rules in docs/design/formatting.md; CLI README "Formatting"). Engine `crates/memobits-syntax/src/format.rs`: token-driven layout (document printer with groups, indents and line suffixes), comments attached to tokens from the gaps between tokens, the syntax tree used only for generic `<>` marking and item starts; every result self-verified (re-parse, tree equal modulo spans via `same_syntax`, comment sequence, second pass identical); failure is PE008 and the file is untouched.
- Guarantees evidence: all 42 parseable repository `.mb` files, 2,712 Memobits programs embedded in Rust tests (string literals that parse), each re-flowed five ways (one line, one token per line, three random layouts), and 1,401 programs with comments sprinkled between arbitrary tokens twelve ways: formatting succeeds, tree and comments preserved, idempotent. `docs/design/proposed-language-guide.mb` does not parse (historical proposal) and is skipped.
- Examples formatted (formatting only): guide (10 modules), topics core-only/enums, apps astar/enf-lexer/utf8-validator; `mb run`/`mb test`/`mb analyze`/`mb ownership` output byte-identical before/after (.local-design/logs/s5fmt-before vs s5fmt-after; `.local-design/s5fmt-snapshot.sh`); `mb check` byte counts differ in two projects only because the `memobits.traps` section stores positions (all other Wasm sections identical). Guide still 154 tests; source run and standalone Wasm `Result: Ok(i32(42))` with empty stderr.
- Tests: `format_corpus.rs` (4), `format_cases.rs` (23), `crates/memobits-cli/tests/s5_fmt.rs` (6), `examples_documented.rs::every_example_is_formatted`.
- Open / for the architect: five interpretations of the binding style are listed in decisions.md "Shipped S5-1 details" (adjacent one-line items stay adjacent, inline bodies stay inline, match arm commas, `where` placement, tuple commas); dense inline block comments can trip the self-check (PE008, file untouched); method chains are not broken at `.`.
- Workspace: `cargo test -j1 --workspace --no-fail-fast -- --test-threads=1` 1,615 passed, 0 failed (logs/s5fmt-workspace.log); `cargo fmt --all -- --check` and `git diff --check` clean.
- Logs: logs/s5fmt-*.log.

