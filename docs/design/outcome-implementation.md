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
  whole-value assignment through an ancestor share preserves descendant fields.
- Project resolution checks imported alias-qualified variants by following
  aliases in their defining modules. An unknown variant on a visible alias
  produces ME006 and use of a private alias from another module produces ME007.
  Public signatures and type definitions also check nested type arguments for
  private types (ME010). Base references use ordinary module visibility
  (ME007), and public derivations cannot expose a private local base (ME010).

## Remaining gates

1. Add concrete runtime error identity to values and artifact metadata.
   Ancestor reference coercion is currently limited to direct internal call
   arguments. Implicit owned conversion, downcasts, and conversions between
   unrelated types are rejected. Explicit owned ancestor conversion still has
   no spelling.
   `message: String` depends on string support.
2. Implement reference type arguments and embedded-loan tracking together.
   Dependency tracking must preserve loans through construction, aggregate moves,
   branch joins, calls, destructuring, and matching, including nested outcomes.
   B3 borrowing of an enum's storage remains available for owned payloads.
3. Implement outcome entry results and artifact metadata so source and artifact
   execution report the same success, absence, and concrete error identity.
   Guest traps remain separate from returned errors. Outcomes and derived
   errors can cross internal calls. Aggregate entry and export signatures
   still produce LE900.

## Acceptance evidence

Analysis tests cover alias interning, nested outcomes, inference and arity
failures, shadowing, the Error bound, exhaustiveness, and aggregate moves.
They also cover ancestor-first layout, non-error bases, duplicate inherited
fields, derivation cycles, recursive value layouts, and rejection of invalid
ancestor calls. Loan tests cover last-use release, overlapping call arguments,
live loans, and immutable share handles. Wasm tests exercise transitive
reborrows, whole ancestor stores on array elements, and invalid IR ancestry.
Resolver tests cover imported aliases, invalid variants, and
nested public signature privacy. CLI tests cover cross-module derivation and
coercion, field privacy, and source and standalone artifact
execution with a primitive entry result. A counter checks once-only
evaluation of success and failure payloads.

Completing B4 also requires tests for concrete error identity, embedded-loan
release, escapes and conflicts through branches and calls, and source/artifact
parity for outcome entry results.
