# Enum implementation sequence

The accepted design uses nominal enums, `type Name [ Variant, Variant(T, U), ... ]`,
with variants written `Type::Variant` and Rust-inspired semantics
(`decisions.md`). Enums reuse the struct and array machinery: they are inline
frame-cell aggregates that move as whole values. This document separates what
executes from what is still gated and orders the work into packages B1 to B4.

## Package sequence

**B1 — enum types as values, no `match` (implemented; see the B1 checkpoint).**
Declarations, variant construction (`Shape::Empty`, `Shape::Circle(1.5)`),
and enums as ordinary aggregates: bindings, whole assignment, moves, owned,
`borrow` and `share` parameters, results, `if`/block joins, struct fields,
array elements and repetition. The IR gets `Type::Enum`, `TypeDefKind::Enum` and
`EnumNew`; the backend gets the tag and payload layout. Enums are not
observable at language level yet: there is no equality, no field access and no
tag read until B2.

**B2 — owned `match` with exhaustiveness (planned).**
`match v { Shape::Empty => .., Shape::Circle(r) => .., Shape::Rect(w, h) => .. }`
over an owned scrutinee. Flat patterns only: a variant path with identifier or
`_` payload bindings, plus a `_` arm. Exhaustiveness is a set difference over
the variants (missing variants are named). All arms share one result type under
the `if` rule. The scrutinee is consumed; each arm binds its payload by moving
it out. See "The B2 plan" below.

**B3 — borrow matching and enum parameters everywhere (planned).**
`match v.borrow() { .. }` and `match` through `borrow E` / `share E`
parameters, with payload bindings that are references. Loans: payload bindings
keep a loan on the scrutinee's place until their last use, with a variant
payload path in the loan (like a field path). Mutable matching (`share`) is
decided here. Enum values also appear in more positions (field bases, call
results used as scrutinees).

**B4 — compiler-known `Option`, `Result`, `Attempt` and the `Error` hierarchy (planned).**
The standard generic enums, written once as prelude declarations and
monomorphised per instantiation in analysis, so IR and Wasm see plain enums.
Needs minimal generic enum syntax (`Option<i32>`), bringing `Some`/`None`/`Ok`/
`Err` into scope, and reference payloads (`Option<borrow i32>`) on top of B3's
loans.

## Design notes confirmed in the code

- **Type table.** Structs and enums share one id space. `memobits-analysis`
  builds one table (`types/typetable.rs`); `TypeId`s follow module order, then
  declaration order, whatever the kind. Aliases are followed everywhere a type
  is named, so `type S = Shape;` and `S::Circle(1.0)` work. The table entry
  carries `fields` for a struct or `variants` for an enum.
- **IR types.** `Type::Enum(TypeId)` beside `Type::Struct(TypeId)`;
  `Program::types` holds `TypeDef { path, span, kind }` with
  `TypeDefKind::Enum { variants: Vec<VariantDef> }` and
  `VariantDef { name, payload: Vec<Type> }`. A variant's index is its
  declaration position and is its tag value. Payload types are non-Unit
  primitives, structs, enums and arrays of those, at any depth; reference
  payloads are invalid until B3/B4. Validation rejects an empty enum, a
  duplicate variant name, an out-of-range type id, a struct id naming an enum
  (and the reverse), and by-value recursion through arrays, structs and enum
  payloads.
- **Construction.** `InstructionKind::EnumNew { ty, variant, payload }` takes one
  consumed operand per payload type of that variant (none for a unit variant);
  the output type is `Type::Enum(ty)`. Source order is decided by the operands'
  earlier instructions: payload arguments are evaluated and captured left to
  right, then handed over in declaration order. Aggregates move in, primitives
  are copied (a primitive read through a reference is copied implicitly, as for
  call arguments). The validator checks the type id, the variant index, the
  operand count, each operand's type and consumption, and the output type.
- **Variant paths.** The resolver validates `Enum::Variant` (NE004 for a local
  enum, ME006 for an imported one) and visibility: a variant is as public as its
  enum, so `pub type` enums have public variants and private enums stay private
  (ME007). Analysis re-resolves the written prefix as a type (so `use`d names,
  qualified module paths and aliases all work) and records a `VariantUse` fact
  for each construction. A unit variant is a path expression; a payload variant
  is a call whose callee is the path.
- **Owned-value positions.** Like struct literals, a unit variant must be in a
  position that takes an owned value (initialiser, assignment, argument, result,
  field, element, branch value). A bare `Shape::Empty;` is TE017. A payload
  variant call is an ordinary call expression.
- **Layout.** See "Representation and layout".
- **Loans and moves.** Nothing new in `memobits-ownership`: `EnumNew` consumes
  its payload operands, an enum local moves as a whole value (BE001 afterwards),
  and `Borrow` of an enum owner creates a loan rooted at the enum's place. B1
  has no projection into an enum, so every access overlaps the whole enum:
  assigning, moving, reading or sharing an enum while a reference to it is live
  is BE005, and two `share`s of one enum in a call are BE005.

## Representation and layout

An enum value occupies one inline cell (a frame cell for locals and values,
exactly like arrays and structs). A reference to an enum is the cell address
(`i32`); an owned enum parameter or result is a pointer, copied in by the callee
or written through the hidden result pointer; join parameters are frame cells;
`Assign`/`Capture`/`Store` of a whole enum are `memory.copy`; construction is in
place when the value is bound immediately (`construction_aliases`).

```
offset 0        tag (u8 for up to 256 variants, u16 up to 65536, else u32)
payload_start   align_up(tag_size, payload_align)
                payload fields of the active variant, each at its own
                alignment, starting at payload_start
size            max over variants of the payload end (at least the tag size),
                rounded up to the enum alignment
align           max(tag_size, payload_align)
```

`payload_align` is the largest alignment of any payload field of any variant,
so one payload start serves every variant. Unit-only enums are just the tag
(size and alignment 1 or 2). Nested aggregate payloads are stored inline with
their own size and alignment, exactly like nested struct fields
(`FieldStorage::Aggregate`). All arithmetic is checked: a size that does not fit
32 bits is a layout-overflow diagnostic, a frame over `[build].stack_size` is
LE900 ("enum frame layout of N bytes exceeds the configured stack size").

The tag value of a variant is its declaration index. The layout is an internal
detail and **not a stable ABI**: bytes outside the active variant's payload
(padding, and the tail of a smaller variant) are unspecified and must never be
compared or copied for their meaning. An enum cannot appear in an exported
signature (LE900), so no host observes the layout.

## The B2 plan (representation written down now)

B1 defines the cell layout and the tag value so B2 only adds instructions.

- **Tag read.** `InstructionKind::EnumTag { base }` with `base` an enum owner
  (used with `Read`) or a reference to one; the output is a `u32` read with the
  tag's own width at offset 0 and zero-extended. It is a pure read and takes no
  loan of its own beyond what the base operand already holds.
- **Branching.** `TerminatorKind::Switch { tag, targets, default }`:
  `targets: Vec<(u32, Edge)>` maps variant indices to edges, `default` is
  optional. The validator checks that every variant has a target or a default
  exists, and that edges carry matching join arguments. The backend lowers it to
  a `br_table` (dense tags) or a compare chain. Analysis proves exhaustiveness,
  so a `Switch` never needs a runtime failure path.
- **Payload projection.** `VariantAddr { loan, base, variant, field, access }`
  is the enum twin of `FieldAddr`: a reference to payload field `field` of
  variant `variant`, at `base + payload_offset`. It is only meaningful on a path
  dominated by the `Switch` edge for that variant; the validator checks index
  ranges and types, not dominance (the Wasm backend treats it as a plain offset).
  Loans get a path step `Step::Variant(variant, field)` next to `Field` and
  `Index`, so payload bindings of different fields stay disjoint.
- **Owned match.** The scrutinee is consumed. In an arm, each payload binding is
  taken with an `Extract`-style move-out (`VariantExtract { base, variant,
  field }`, the enum twin of `Extract`, consuming the scrutinee on the last
  extraction in the arm) so the existing "whole value consumed exactly once"
  rule holds. Unbound payloads of the matched variant are dropped; there is no
  drop machinery to run because payloads are plain data.
- **Syntax and typing.** `ExprKind::Match { scrutinee, arms }` with patterns
  limited to `Type::Variant`, `Type::Variant(name, _, ..)` and `_`. The result
  type follows the `if` rule (all arms agree; `Never` arms are ignored).
  Duplicate and unreachable arms are diagnosed; missing variants are listed in
  the exhaustiveness error.
- **Equality.** `==` on enums stays unavailable (TE007) until it is decided
  separately; it can then be a `match` desugaring over the tag.

## B1 checkpoint

### Executes

- `type Name [ A, B(T), C(T, U) ]`, trailing commas accepted; payload types are
  non-Unit primitives, arrays, structs and enums in any nesting and any
  declaration order (aliases may name them). Public enums are usable across
  modules with `use` and qualified paths; private enums are not (ME007).
- Construction `Shape::Empty`, `Shape::Circle(1.5)`, `shapes::Shape::Rect(a, b)`
  (and through a `use`d name or alias), in owned-value positions. Payload
  arguments are checked for arity (TE010) and type (TE002), evaluated left to
  right, aggregates moved in, primitives copied.
- Enum values as `let` / `var` bindings, whole assignment (`s = Shape::Empty;`),
  moves (BE001 after a move), owned / `borrow` / `share` parameters and `var`
  owned parameters, results, `if` and block joins, early `return`, struct fields
  of enum type, `Array<Shape, N>` elements, array literals and repetition
  (`[Shape::Empty; 4]`, the element expression evaluated per element), enums
  inside enum payloads, and loops that build enums.
- `.borrow()` / `.share()` of a whole enum to parameters or local reference
  bindings, with the usual loan checks (conservative: any access overlaps the
  whole enum).
- Wasm execution of all of the above; tag at offset 0 and payload offsets as in
  "Representation and layout".

### Gated, with the diagnostic

| Form | Code |
| --- | --- |
| Inspecting an enum: `match`, `==` / `!=`, ordering, arithmetic on an enum | TE007 (`match` is not yet in the grammar) |
| Field access `e.x`, indexing `e[0]` on an enum | TE024, TE007 |
| Unit variant used as a temporary (`Shape::Empty;`, `Shape::Empty + 1`) | TE017 |
| `.copy()` of an enum | TE017 |
| Moving an enum out of a field or element (`let t := h.s;`, `let t := a[0];`) | TE022 |
| Reference payloads and references to enum payloads or tags | not expressible (B3) |
| Enums in `main` / `[export]` signatures (parameters, results, references) | LE900 |
| Enum frame over the configured stack size | LE900 |
| Enum size over 32 bits | layout-overflow diagnostic |

### Rejected by analysis

| Problem | Code |
| --- | --- |
| Empty enum `type E []` | TE027 |
| Enum that contains itself by value, directly or through arrays, structs and other enums | TE026 ("recursive enum") |
| Unknown payload type | TE001 (or the resolver's NE003) |
| Duplicate variant names | NE006 (resolver) |
| Unknown variant of a local enum | NE004 (resolver); of an imported enum ME006; standalone check TE028 |
| Wrong payload argument count | TE010 |
| Wrong payload argument type | TE002 |
| Payload given to a unit variant (`Shape::Empty(1)`, `Shape::Empty()`), or a payload variant written without arguments (`Shape::Circle`) | TE028 |
| Private enum referenced from another module | ME007 (resolver) |
| Whole assignment to a `let` enum | TE004 |
| Use after move | BE001 |
| Assignment, move or second exclusive access while a reference is live | BE005 |

### Not in B1

Everything in B2 to B4 above. In particular there is no example project: an
enum is not observable without `match`, so the first runnable enum example
arrives with B2. B1's behaviour is covered by tests in every layer; the tag and
payload bytes are checked by in-crate backend tests that read memory through the
test-only `__test_memory` export, not by any language-level tag access.
