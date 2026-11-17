# Struct implementation sequence

The accepted design uses nominal structs, `type Name { field: Type, ... }`, with
struct literals `Name { field: value }`, field reads `p.field`, and per-field
visibility. Fields are module-private unless marked `pub`. This document
separates what executes from what is still gated, and orders the remaining work
into packages (A1 to A4), each of which must land with its own gates and tests.

## Package sequence

**A1 — declarations, literals, primitive field reads, visibility (implemented).**
Named struct declarations with non-Unit primitive fields; struct literals as
`let` initialisers, with every field given exactly once in any order; reads of
primitive fields inside expressions; `.copy()` of a primitive field; and `pub`
types and fields across `use` and qualified paths. Everything else stays gated.

**A2 — `var` structs, field assignment, whole-struct moves, struct parameters, borrow/share, struct results (planned).**
`var` struct bindings and `p.x = v` / `p.x op= v` writes, gated today with TE017.
Whole-struct moves (`let q := p;`, passing and returning a struct), struct
parameters and results, and `borrow`/`share` of a struct owner and its fields.
Owned struct arguments and results follow the array model: the callee owns a
copy in its own frame cell, and struct-return storage belongs to the caller.

**A3 — nested structs, array fields, arrays of structs (planned).**
Struct-typed and array-typed fields (a struct inside a struct, `Array<T, N>`
fields) and `Array<S, N>` with struct elements. These need the layout to nest
(size and alignment computed recursively) and element moves to follow the same
TE022 rule as arrays.

**A4 — destructuring and field-disjoint loans (planned).**
Whole-value destructuring `let P { x, y: alias } := p;` (and `var` for mutable
bindings), which names every accessible field, as decided in `decisions.md`.
Field-disjoint loans: borrowing two different proven fields of one struct
independently. Until then every field loan overlaps the whole struct.

## Design notes confirmed in the code

- **Type table.** Struct identity is `module::Name`. `memobits-analysis`
  builds one type table (`crates/memobits-analysis/src/types/typetable.rs`) for
  all modules checked together. `TypeId`s follow module order, then declaration
  order. Aliases are followed wherever a type is named, so they add no
  definitions of their own.
- **IR.** `Program::types` holds `TypeDef { path, span, kind }` with
  `TypeDefKind::Struct { fields: Vec<FieldDef> }`. A value has type
  `Type::Struct(TypeId)`. Field types are non-Unit primitives only.
- **Construction.** `InstructionKind::StructNew { ty, fields }` takes one consumed
  operand per field in declaration order. Source evaluation order is kept by the
  earlier instructions that produce the operands, so initialisers run in source
  order even when the literal is written differently.
- **Field addresses.** `InstructionKind::FieldAddr { loan, base, field, access }`
  is the bounds-check-free twin of `ElementAddr`. It yields a `Reference` to the
  field type and is read with `Load`. A primitive field read is therefore
  `FieldAddr(Borrow)` followed by `Load`, and a read does not consume the owner.
- **Layout.** Fields sit in declaration order at natural alignment: each field
  starts at the next offset aligned to its own size, and the struct's size is
  rounded up to its largest alignment (`crates/memobits-wasm/src/lib.rs`,
  `struct_layouts`). A struct value owns an inline cell in the activation
  frame (bounded by the configured `[build].stack_size`), shared with arrays. Overflow is a backend diagnostic (LE900), never a host
  allocation.
- **Loans.** A `FieldAddr` loan is rooted at the whole struct local. A live
  reference to any field therefore conflicts with a write to any other field of
  the same struct (BE005). This is conservative; field-disjoint loans are A4.
- **Primitive copies.** `decisions.md` says primitive fields are copied
  implicitly, so `let q := p.x;` is valid. See the implicit primitive copy
  checkpoint below.

## A1 checkpoint

### Executes

- `type Name { field: T, pub field: T }`, with trailing commas accepted and
  non-Unit primitive field types. Aliases (`type N = i32;`) may name field types
  and struct types.
- Struct literals `Name { f: v, ... }` as the initialiser of a `let` binding,
  with or without an annotation (`let p: P = P { .. };`). Every declared field is
  given exactly once, in any order. Initialisers are evaluated in source order.
- Primitive field reads `p.f` in arithmetic, comparisons, unary operators,
  `if`/`else if` conditions (including `Bool` fields), `&&` / `||`, and array
  indices.
- `p.f.copy()` into any owned position, including bindings with annotations.
- Public types and fields across modules, through `use`, qualified paths, and
  type aliases. A type whose fields are all `pub` may be constructed and read from
  another module.
- Zero-field structs (`type U {}`) are valid values.

### Gated, with the diagnostic

| Form | Code |
| --- | --- |
| `var` struct binding, field assignment `p.x = v` / `p.x op= v` | TE017 |
| Whole-struct use as a value: `let q := p;`, `p;`, `q = p;`, passing or returning | TE017 |
| Struct literal outside a `let` initialiser (temporaries, branch values, array elements, `P { .. }.x`) | TE017 |
| Struct parameters, results, `borrow`/`share` parameters, struct-typed signatures including `pub` `main` | TE017 |
| `.borrow()` / `.share()` of a struct, `.copy()` of a struct | TE017 |
| Field access on a non-local base (`f().x`), and `1.field` | TE017 |
| Struct-typed fields, array-typed fields, arrays of structs (`Array<P, N>`, `type G = Array<P, 2>`) | TE017 |
| Enum types used as value types | TE001 (declaration TE016) |
| Destructuring `let P { x } := p;` | SE002 |
| Struct literal directly in an unparenthesised `if` condition | SE002 |
| Frame layout over the configured stack size for a struct | LE900 |

### Rejected by analysis

| Problem | Code |
| --- | --- |
| Unresolved type name (`let p := Missing { .. }`) | TE001 |
| Field value of the wrong type, or a literal out of range for its field (`u8`) | TE002, TE008 |
| Missing field, unknown field, field initialised twice, or a non-struct name in a literal; a field declared twice | TE023 |
| Field read on a non-struct value or an unknown field | TE024 |
| Reading a private field, or constructing a struct with private fields, from another module | TE025 |
| A struct containing itself by value, or a type alias cycle | TE026 |
| Duplicate type declaration | TE014 |
| Private definition referenced from another module | ME007 (resolver) |
| Unknown name in a literal path | NE003 (resolver) |

### Ownership

Field reads do not consume the owner. A struct local moved into another binding
makes later field access BE001. Building a struct consumes its field operands.
A live field reference blocks reassignment of the whole struct (BE005).
Two field references to different fields of one struct also conflict (BE005).

### Not in A1

Everything in packages A2 to A4 above. In particular, `var` structs, whole-struct values, struct parameters and results, nested
or array-typed fields, destructuring, and field-disjoint loans are all still
gated.

## Implicit primitive copy checkpoint

Primitive fields are copied implicitly. `let q := p.x;`, tails, `return p.x;`,
owned arguments (`f(p.x)`), array elements, branch tails, assignment and struct
field initialisers all read the field through `FieldAddr` + `Load` + `Copy` and
leave the struct whole and usable. `.copy()` on a field is optional. TE022
("a struct field cannot be moved out by field access") no longer fires for
primitive fields; the check remains in place for field types that are not
primitive, which become reachable with nested and array-typed fields in A3.
