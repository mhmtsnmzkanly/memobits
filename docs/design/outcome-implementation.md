# Compiler-known outcomes (B4)

Owned `T?`, `T ! E`, and `T ?! E` execute inside Memobits
functions. `T ?! E` is exactly `T? ! E` (that is, `T? ! E`); there is no
separate three-state type, and values are built and matched as `Ok(Some(v))`,
`Ok(None)` and `Err(e)` with nested patterns. Zero-argument application entries
support `T ! E` and `T ?! E` with primitive success payloads. The full B4 contract is in
[decisions.md](decisions.md).

## Implemented gates

- The shared registry in `memobits-syntax/src/templates.rs` declares template
  parameter kinds and variant payloads. Syntax accepts the registered argument
  lists, including the integer length of `array<T, N>`. Analysis resolves type
  arguments through local and module aliases, then interns each outcome by
  template identity and resolved arguments. Nested instances participate in
  recursive value layout checks. User-defined generics remain unavailable.
- Syntax records `borrow T` and `share T` arguments with their access mode and
  full span. Name resolution checks referent names and visibility at any
  nesting depth. Analysis allows a written borrow argument only in a direct
  local `(borrow T)?` binding annotation. Other written reference
  arguments produce TE017 at the argument span, and inferred reference
  payloads produce TE017 at the payload expression. Integer slots still
  require literals. Contextual owned primitive payloads can still load
  a value through a standalone reference.
- `Some`, `None`, `Ok` and `Err` use the
  concrete expected instance when one is available. An alias-qualified
  constructor such as `Work::Ok(value)` supplies its own instance. Local
  bindings, functions, and imports shadow the short names. Payload evidence
  alone can determine all arguments for `Some(value)`, including nested
  `Some` calls. Bare `None` and well-formed short `Ok`/`Err` constructors
  without a concrete instance in context produce TE002. The Error bound never
  supplies an omitted argument by default.
- Constructor and pattern arity, payload types, variant membership, and match
  coverage use the ordinary enum checks. Short match patterns use the
  scrutinee's concrete outcome instance. Qualified patterns through aliases must
  name that same instance. Payloads evaluate once and follow ordinary enum
  ownership rules, including consumption of aggregate operands. If a payload
  exits the current control flow, no enum value is constructed.
- `type ParseError: Error { pub line: u32 }` declares a nominal error type.
  Bases resolve in the declaring module and can name aliases or other derived
  errors. Fields are laid out from the root through each ancestor in
  declaration order, followed by the new fields. The root supplies the public
  field `code: u32`. Every field needs an explicit initializer. Inherited
  private fields remain private to the module that declared them for reads,
  writes, literals, and destructuring (TE025).
- A base outside the Error hierarchy is rejected with TE017. An inherited
  field name cannot be redeclared, even if the ancestor field is private
  (TE023). Derivation cycles, including cycles through aliases, are rejected
  with TE026. Inherited fields also participate in recursive value layout
  checks (TE026).
- A resolved `E` must be the compiler-known `Error` or a type derived from it.
  Aliases to those types qualify. A matching field layout does not qualify.
  Invalid written arguments get TE002 at the argument span. When a short error
  constructor supplies the only evidence for `E`, analysis checks that
  evidence against the bound before reporting any missing arguments.
  Derived errors use ordinary struct construction, field access, destructuring,
  and moves, including when constructing and matching outcome payloads.
- Direct internal calls accept a derived error reference for a borrow or share
  parameter of any nominal ancestor, including ancestors named through aliases.
  Pass an existing reference or create one with `.borrow()` or `.share()`.
  A share can be reborrowed for a borrow parameter. A share parameter still
  requires exclusive access. The call reborrows the same place with ordinary
  loan conflict and last-use rules. IR validation checks the nominal parent
  chain and inherited field prefix. Wasm passes the original address and places
  each type's new fields after the padded layout of its parent, so even a
  whole-value assignment through an ancestor share preserves descendant fields
  and the destination's concrete identity.
- Every Error value has a hidden 32-bit, module-local type tag at offset zero.
  The inherited `code` follows the tag. Ordinary value moves and aggregate
  copies carry the tag. Whole-value stores through an Error share copy the
  statically visible fields while preserving the destination tag.
- Project resolution checks imported alias-qualified variants by following
  aliases in their defining modules. An unknown variant on a visible alias
  produces ME006 and use of a private alias from another module produces ME007.
  Public signatures and type definitions also check nested type arguments for
  private types (ME010). Base references use ordinary module visibility
  (ME007), and public derivations cannot expose a private local base (ME010).

## Function-local borrow Option

```memobits
fn main() -> i32 {
    var owner := 7;
    let wrapped: (borrow i32)? = Some(owner.borrow());
    let moved := wrapped;
    let old := match moved { Some(r) => r.copy(), None => 0 };
    owner = 9;
    old + owner
}
```

- Use an immutable local binding with a direct `(borrow T)?` annotation
  to construct `Some` or `None`. The referent can be a supported non-Unit
  primitive, struct, enum or fixed array, including a referent named through
  an alias. `Some` consumes an existing borrow handle or a fresh borrow
  conversion. A share needs an explicit borrow reborrow before wrapping.
- Initializing another immutable local from a wrapper moves it. A consuming
  match binds the original read-only reference in the `Some` arm. The binding
  supports ordinary borrow operations, including reborrowing for an internal
  borrow parameter. Use `.copy()` to make a primitive match result from
  the reference. Wasm stores the referent address as the `Some` payload.
- The live wrapper and any live extracted handle retain the referent loan.
  Mutating, sharing or moving the owner conflicts while that loan is live.
  The loan ends after the last use, including before the arm body if the
  payload is discarded or its binding goes unused. `None` carries no loan.
- Wrapper types in aliases, fields, nested arrays or outcomes, signatures and
  returns remain gated. So do mutable wrapper bindings, taking a reference
  to wrapper storage, and wrapper-valued block, branch or match results.
  Extracted handles follow the existing restrictions on reference results
  and rebinding. These gates prevent a handle to a block-local owner from
  leaving that scope. IR validates the supported payload shape and the local
  transport restrictions. Each wrapper local has at most one static
  initialization site. Ownership treats initialization as a definition that
  replaces the slot's previous availability and provenance. A second site
  would therefore permit reassignment of an immutable wrapper. The same site
  can execute on each loop iteration.

## Application entry adapter

- The supported success payloads are `bool`, integers through 64 bits, and
  `f32` and `f64`. The application adapter accepts zero-argument
  `T ! E` and `T ?! E` entries, including aliases. `T?`
  entries, outcomes with aggregate success payloads, other aggregate
  application signatures, and aggregate library exports get LE900.
- The internal version 2 adapter exports `main` with two Wasm `i32` results
  (address and size) and its backing memory as `__mb_entry_memory_v1`. The
  caller-owned return cell follows the configured guest stack. The guest call
  retains the full configured stack budget.
- The `memobits.entry` custom section carries a version byte, outcome family,
  success primitive tag, payload offset, optional inner offset (zero for
  `T ! E`; for `T ?! E` the offset of the scalar inside the `Option` cell, whose
  tag byte at the payload offset is 0 for `Some` and 1 for `None`), and the
  little-endian result size
  and declared Error ID. A bounded UTF-8 name follows the header. Version 2
  (it replaced the three-state family of version 1 with `T ?! E`) records only the declared `E`. Owning a concrete error through an ancestor
  type requires a separate conversion feature. The host checks the stored tag
  against the declared ID before displaying the qualified concrete name and
  `code`.
- The runner checks metadata size and values, rejects duplicate sections and
  control characters in names, and checks the adapter signature, memory,
  returned size, address alignment, bounds, and active variant before
  rendering. Source and standalone artifact runs share the decoder. `Ok(v)`,
  `Ok(Some(v))`, `Ok(None)` and `Err` are normal returns printed on stdout
  (`Result: Ok(i32(42))`, `Result: Ok(Some(bool(true)))`, `Result: Ok(None)`,
  `Result: Err(Error, code=5)`). Guest traps use runtime
  diagnostics. This adapter is private to the current backend and runner.

## Remaining gates

1. Expand embedded-loan tracking to wrapper assignment and branch results by
   carrying all possible origins and checking owner scope. Calls, nesting,
   borrowing wrapper storage and destructuring through larger aggregates
   each need their own validation, provenance and escape checks. Share
   payloads also require exclusive access tracking across each supported
   transfer.
2. Explicit owned conversion to an Error ancestor remains unimplemented and
   still has no spelling. The accepted design preserves concrete identity after
   conversion. The entry metadata and decoder must support reporting that
   identity when it differs from declared `E`.
   Ancestor reference coercion is currently limited to direct internal call
   arguments. `message: string` depends on string support.

## Acceptance evidence

Analysis tests cover alias interning, nested outcomes, inference and arity
failures, shadowing, the Error bound, exhaustiveness, and aggregate moves.
They also cover ancestor-first layout, non-error bases, duplicate inherited
fields, derivation cycles, recursive value layouts, and rejection of invalid
ancestor calls. Local borrow Option tests cover consuming transport, wrapper and extracted
loan conflicts, rejected scope escapes, malformed IR transport, and Wasm
execution of both variants with last-use release. Loan tests also cover
last-use release, overlapping call arguments,
live loans, and immutable share handles. Wasm tests exercise transitive
reborrows, whole ancestor stores on array elements, and invalid IR ancestry.
Resolver tests cover imported aliases, invalid variants, and
nested public signature privacy. CLI tests cover cross-module derivation and
coercion, field privacy, and source and standalone artifact
execution with a primitive entry result. A counter checks once-only
evaluation of success and failure payloads.

CLI tests also cover every outcome variant, standalone artifact parity,
and checked and stack traps during outcome execution. A cross-module regression
returns a leaf error after whole stores through both its immediate ancestor
and root shares. It checks the concrete identity, the updated code, and the
preserved leaf fields. Runtime tests exercise malformed metadata, invalid
addresses and sizes, invalid tags and bool payloads, and mismatched identities.
