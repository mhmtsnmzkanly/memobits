# Compiler-known outcomes (B4)

Owned `Option<T>`, `Result<T, E>`, and `Attempt<T, E>` execute inside Memobits
functions. The full B4 contract is in [decisions.md](decisions.md).

## Implemented gates

- The shared registry in `memobits-syntax/src/templates.rs` declares template
  parameter kinds and variant payloads. Syntax accepts the registered argument
  lists, including the integer length of `Array<T, N>`. Analysis resolves type
  arguments through local and module aliases, then interns each outcome by
  template identity and resolved arguments. Nested instances participate in
  recursive value layout checks. User-defined generics remain unavailable.
- `Some`, `None`, `Ok`, `Err`, `Done`, `Skipped`, and `Failed` use the
  concrete expected instance when one is available. An alias-qualified
  constructor such as `Work::Done(value)` supplies its own instance. Local
  bindings, functions, and imports shadow the short names. Payload evidence
  alone can determine all arguments for `Some(value)`, including nested
  `Some` calls. Bare `None` and well-formed short Result or Attempt constructors
  without a concrete instance in context produce TE002. The Error bound never
  supplies an omitted argument by default.
- Constructor and pattern arity, payload types, variant membership, and match
  coverage use the ordinary enum checks. Short match patterns use the
  scrutinee's concrete outcome instance. Qualified patterns through aliases must
  name that same instance. Payloads evaluate once and follow ordinary enum
  ownership rules, including consumption of aggregate operands. If a payload
  exits the current control flow, no enum value is constructed.
- A resolved `E` must have the compiler-known Error root's type identity.
  Aliases to that root qualify. Structs with a matching shape do not qualify.
  Invalid written arguments get TE002 at the argument span. When a short error
  constructor supplies the only evidence for `E`, analysis checks that
  evidence against the bound before reporting any missing arguments.
  The root has the public field `code: u32`.
- Project resolution checks imported alias-qualified variants by following
  aliases in their defining modules. An unknown variant on a visible alias
  produces ME006 and use of a private alias from another module produces ME007.
  Public signatures and type definitions also check nested type arguments for
  private types (ME010).

## Remaining gates

1. Implement Error derivation, ancestor-first fields, and cycle checks. Derived
   declarations are parsed and rejected with TE017. Only the compiler-known
   root currently qualifies as `E`. Concrete runtime error identity and
   borrowed ancestor access remain pending. The spelling of owned ancestor
   conversion is open. `message: String` depends on string support.
2. Implement reference type arguments and embedded-loan tracking together.
   Dependency tracking must preserve loans through construction, aggregate moves,
   branch joins, calls, destructuring, and matching, including nested outcomes.
   B3 borrowing of an enum's storage remains available for owned payloads.
3. Implement outcome entry results and artifact metadata so source and artifact
   execution report the same success, absence, and concrete error identity.
   Guest traps remain separate from returned errors. Outcomes currently cross
   internal calls, with aggregate entry and export signatures still gated by
   LE900.

## Acceptance evidence

Analysis tests cover alias interning, nested outcomes, inference and arity
failures, shadowing, the Error bound, exhaustiveness, and aggregate moves.
Resolver tests cover imported aliases, invalid variants, and nested public
signature privacy. CLI tests validate Wasm and compare source and standalone
artifact execution with a primitive entry result. A counter checks once-only
evaluation of success and failure payloads.

Completing B4 also requires tests for inherited fields and error identity,
last-use release and rejected escapes or loan conflicts through branches and
calls, and source/artifact parity for outcome entry results.
