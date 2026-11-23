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

**A2 — `var` structs, field assignment, whole-struct moves, struct parameters, borrow/share, struct results (implemented; see the A2 checkpoint).**
`var` struct bindings and `p.x = v` / `p.x op= v` writes, whole-struct moves
(`let q := p;`, passing and returning a struct), struct parameters and results,
and `borrow`/`share` of a whole struct. Owned struct arguments and results
follow the array model: the callee owns a copy in its own frame cell, and
struct-return storage belongs to the caller. Field-level references stay gated.

**A3 — nested structs, array fields, arrays of structs (implemented; see the A3 checkpoint).**
Struct-typed and array-typed fields (a struct inside a struct, `array<T, N>`
fields) and `array<S, N>` with struct elements. The layout nests (size and
alignment computed recursively) and sub-aggregate moves follow the TE022 rule
of arrays.

**A4 — destructuring and field-disjoint loans (implemented; see the A4 checkpoint).**
Whole-value destructuring `let P { x, y: alias } := p;` (and `var` for mutable
bindings), which names every accessible field, as decided in `decisions.md`.
Field-disjoint loans: borrowing two different proven fields of one struct
independently, and likewise distinct constant array indices.

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
  the same struct (BE005). A1 to A3 were conservative here; A4 gives loans a
  projection path (see the A4 checkpoint).
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
  `if`/`else if` conditions (including `bool` fields), `&&` / `||`, and array
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
| Struct-typed fields, array-typed fields, arrays of structs (`array<P, N>`, `type G = array<P, 2>`) (lifted by A3) | TE017 |
| Enum types used as value types (lifted by B1, see `enum-implementation.md`) | was TE001 / TE016 |
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

Everything in packages A2 to A4 above. The A1 gate table above predates A2:
its `var`, field assignment, whole-struct, parameter, result, reference and
literal-position rows are lifted by the A2 checkpoint below.

## A2 checkpoint

A2 reuses the aggregate machinery written for arrays instead of adding struct
copies of it. The IR validator, the frame-cell allocator, owned-parameter copy
in, hidden result pointers, join parameters as frame cells, `Assign`/`Capture`
as `memory.copy`, and in-place construction (`construction_aliases`) already
worked on "array or struct" values; A2 removed the struct bans and generalised
the remaining array-only checks (`is_aggregate`, `aggregate_bytes`).

### Executes

- `var` struct bindings and `var` owned struct parameters.
- Field writes `p.x = v` and `p.x op= v` (`+= -= *= /= %=`, the scalar rules;
  `bool` fields take `=` only). Through `var` owners, owned `var` parameters,
  `share` parameters, and `var` share bindings.
- Whole-struct moves: `let q := p;`, `q = p;` (a `var` target), a literal or call
  result as the right-hand side, `return p;`, struct-valued `if`/block results.
  After a move the source is unavailable (BE001) until reassigned.
- Parameters `p: P` (moves the caller's value; `var p: P` lets the callee mutate
  its own copy), `p: borrow P` and `p: share P`. Call sites write `p.borrow()` /
  `p.share()`; the signature decides access. Field reads work through `borrow`
  and `share`; `share` also writes fields and may assign a whole struct
  (`p = P { .. };`, a `memory.copy`). Local reference bindings (`let r := p.borrow();`,
  `var s := p.share();`) and reborrows to an equal or weaker access.
- Results `-> P` for a literal, a local, an owned parameter or a call, used as an
  initialiser, assignment right-hand side or owned argument (`use_p(make())`).
- Mixed-width fields (`u8`, `i64`, `f32`, `bool`, `i16`, `f64`) keep their
  layout through all of the above; narrow stores never touch neighbours.

### Lowering and evaluation order

Per `decisions.md`, a field write evaluates the base, then the right-hand side,
then performs the store: `FieldAddr(Share)` and `Store` are adjacent and come
after the right-hand side's instructions. A compound write reads the field first
(`FieldAddr(Borrow)` + `Load`), then evaluates the right-hand side, then stores.
Consequence for `p.x = f(p.share())` and `p.x += f(p.share())`: they are
accepted. The share loan lives only for the call, which has ended before the
address for the write is formed, so the call's effects happen first and the
store lands last; the compound form uses the field value read before the call.
A reference that is still live across the write (a `let r := p.borrow();` used
afterwards) conflicts as usual (BE005).

### Backend

A struct reference is the owner cell's address (`i32`). A struct-typed
parameter or result is a pointer: an owned parameter is copied into the callee's
own cell in the prologue; a struct result is written through the hidden trailing
pointer (the call's own value cell in the caller's frame) by one `memory.copy`
in `return`. Block parameters of struct type are frame cells; a join edge copies
the argument. `FieldAddr` accepts a struct owner or a reference to one.
`main` and `[export]` functions with struct, struct-reference or struct-result
signatures are rejected by the backend with LE900 ("cannot take structs or
struct references", "cannot return structs"); there is no external struct ABI.

### Diagnostics

| Problem | Code |
| --- | --- |
| Field write to a `let` struct, an owned non-`var` parameter, a `borrow` parameter or binding, or a `let` share binding | TE004 |
| Write to a private field of another module's struct | TE025 (existing) |
| Field write of the wrong type, unknown field, compound write on `bool` | TE002, TE024, TE007 |
| Use after whole-struct move | BE001 |
| Field write, whole assignment or move while a borrow is live; two `share`s (or share + borrow) of one struct in one call | BE005 |
| `make().x`, `P { .. }.x`, a struct literal as a temporary | TE017 |
| `p.x.borrow()` / `p.x.share()` (field-level references) | TE017 |
| `p.copy()` (whole-struct copy) | TE017 |
| Struct-typed fields, array fields, arrays of structs (lifted by A3) | TE017 |
| Struct or struct reference in `main` / `[export]` signature | LE900 |
| `var` on a `borrow`/`share` parameter | TE017 |

### Loans

A field address is a loan rooted at the whole struct local, so any live reference
to a struct blocks writes to any of its fields and moves of the struct (BE005).
(A4 narrows this to the field's own path.)

### Still gated

Struct-typed fields, array-typed fields, arrays of structs (lifted by A3, below); destructuring
and field-disjoint loans (A4); `p.x.share()` and `p.x.borrow()`; whole-struct
`.copy()`; field access on a call result or literal; structs and struct
references in exported signatures (LE900); returning or storing references;
rebinding a reference handle.

## Implicit primitive copy checkpoint

Primitive fields are copied implicitly. `let q := p.x;`, tails, `return p.x;`,
owned arguments (`f(p.x)`), array elements, branch tails, assignment and struct
field initialisers all read the field through `FieldAddr` + `Load` + `Copy` and
leave the struct whole and usable. `.copy()` on a field is optional. TE022
("a struct field cannot be moved out by field access") no longer fires for
primitive fields; the check remains in place for field types that are not
primitive, which become reachable with nested and array-typed fields in A3.

## A3 checkpoint

A3 makes every combination of arrays and structs nest, using chained
projections on intermediate references, exactly as nested arrays already did.
No new IR instruction and no new ownership rule were needed.

### Design

- **Projections.** A place is a root local plus a chain of steps, each an index
  or a field name (`a[i].pts[j].x`). Lowering evaluates and captures the root
  and every index left to right (`lower_place`), forms the whole chain of
  checked addresses only afterwards (`address_chain`: `ElementAddr` for an
  index step, `FieldAddr` for a field step, each yielding a `Reference` to the
  next level with the requested access on every level) and ends in `Load`
  (read), `Store` (write) or the chain's final reference (a lent
  sub-aggregate). Previously separate paths for elements and fields (reads,
  assignments, `.borrow()`/`.share()`) are one path; `lower_field_assign` and
  the element-only chain were merged.
- **Evaluation order.** For `a[f()].pts[g()] = h()`: f, g, then h, then the
  share chain and the store adjacent, so every bounds trap fires after the
  right-hand side's effects (the D2 rule for elements, now on every level). A
  compound write reads the place through a Borrow chain first. Field steps
  have no bounds check.
- **Struct literals.** A field initialiser is an owned-value position, so a
  nested literal, a call result or a named aggregate (a move) feeds a field.
  An array element or repetition element may be a struct literal; repetition
  evaluates it per element.
- **Types and IR.** `Ty::Array` accepts struct elements and the type table
  accepts struct and array fields. The IR validator accepts non-Unit
  primitive, struct and array types for fields and array elements, and
  rejects by-value cycles (`struct 'A' contains itself by value`), so the
  backend never sees one. Analysis reports recursion, directly or through
  arrays and other structs, as TE026 on the offending field.
- **Layout.** `struct_layouts` lays out dependencies first. A nested struct or
  array field is stored inline at its own natural alignment
  (`FieldStorage::Aggregate(size)`, written with `memory.copy` from the
  field operand's value cell); array layout is element size times length with
  `checked_mul`, and a struct size is rounded to its largest alignment, so an
  array of structs strides by the struct size. Layout cost depends on type
  depth only. A frame over `[build].stack_size` is the usual LE900 diagnostic,
  a type whose size overflows 32 bits a layout-overflow diagnostic.
- **Loans.** Every `FieldAddr`/`ElementAddr` loan is rooted at the root local, so
  in A3 any live reference to a sub-aggregate blocks writes anywhere in the
  root. A4 replaced this with projection paths: writing `l.b.x` while
  `l.a.borrow()` is live is now accepted (see the A4 checkpoint).
- **References to primitive fields.** `l.a.x.share()` / `a[i].x.borrow()` stay
  TE017, matching `m[i][j].share()` for arrays ("references to primitive
  elements and struct fields are not supported"). The IR could express them,
  but the rule is kept consistent across arrays and structs until the
  field-disjoint loan work decides how element and field references are lent.

### Executes

- Struct-typed fields: `type Line { a: P, b: P }`; nested literals
  `Line { a: P { x: 1, y: 2 }, b: make_p() }`; reads `l.a.x`; writes
  `l.a.x = v`, `l.a.x += v` (through a `var` owner or a `share` reference);
  whole-field replacement `l.a = P { .. }` and `l.a = other` (moves `other`).
- Array-typed fields: `type Poly { pts: array<i32, 4> }`; `p.pts[i]` reads and
  writes with bounds checks, `p.pts[i] += v`, `p.pts = [..]`.
- Arrays of structs `array<P, 3>`: literals, repetition
  `[P { x: 0, y: 0 }; 8]`, `a[i].x` reads and writes, `a[i] = P { .. }`, and
  arbitrary nesting (arrays of structs holding arrays of structs).
- Sub-aggregates lent to `borrow P` / `share P` / `borrow Array<..>` parameters
  with `l.a.borrow()`, `a[i].share()`, `p.pts.borrow()`, and bound to local
  reference handles (`let r := l.a.borrow();`, `var s := a[i].share();`).
- Aggregates with sub-aggregates pass by value (moves) as parameters, results,
  `if` values and elements like any other aggregate.

### Diagnostics

| Problem | Code |
| --- | --- |
| Moving a sub-aggregate out: `let q := l.a;`, `let r := a[i];`, `f(l.a)` to an owned parameter, `return l.a;`, tail `l.a`, `l.b = l.a;`, `[a[0], a[1]]`, `l.a;` | TE022 ("a struct or array field/element cannot be moved out by field access/indexing; ... partial moves are deferred") |
| Struct containing itself by value, also through arrays (`type A { xs: array<A, 2> }`) | TE026 |
| `l.a.x.share()`, `a[i].x.borrow()`, `p.pts[0].share()` | TE017 |
| Write through a `let`, `borrow` or immutable root (`l.a.x = 1` on `let l`) | TE004 |
| Constant index out of range at any level | TE008 |
| Dynamic index out of range at any level | RE007 (trap, after the right-hand side) |
| Write to `l.a.x` while `l.a.borrow()` is live (an overlapping path; `l.b.x` is accepted since A4) | BE005 |
| Nested aggregate in a `main` / `[export]` signature | LE900 |
| Frame (including nested cells) over the configured stack | LE900 |

### Still gated

Whole-struct `.copy()`; references to primitive fields and elements; field
access or indexing on a call result or literal (`make().a.x`); aggregates in
exported signatures (LE900). Destructuring and field-disjoint loans landed in A4.

## A4 checkpoint

Structs are complete for this phase. A4 adds whole-value destructuring and
field-disjoint loans; nothing else about the language surface changed.

### Destructuring

Syntax: `let P { x, y: alias } := value;`, or `var` for mutable bindings. The
type name may be a path (`geom::Point`) or an imported or aliased name. Every
field is named exactly once; `x` is shorthand for `x: x`. The value is consumed
whole: a source local is moved (later use is BE001), a call result or literal
is simply consumed. Each field binds a new owned local of the field's type,
primitive or aggregate (aggregates may move out because the whole value goes
with them). `var` makes every binding mutable. A struct from another module
needs every field `pub` (otherwise TE025). The initialiser is evaluated once,
then the bindings are made in pattern order.

**IR representation.** `InstructionKind::Extract { base, field }`: `base` is a
struct owner, the output is a fresh owned value of the field type. Lowering
evaluates the initialiser to one operand (a local or a temporary) and emits, per
pattern entry, `Extract` plus an initialising `Assign` to the new local. All
extractions read the base with `Read` except the last, which uses `Consume`, so
the ownership pass sees the whole value consumed exactly once. A zero-field
pattern consumes a local source with a `Capture`. No hidden local is needed.
The IR validator keeps partial moves unrepresentable: an aggregate-typed
`Extract` with a `Read` base must be followed, in the same block, by a consuming
`Extract` or `Capture` of the same base. Nothing else moves a field out of a
struct, and `FieldAddr` + `Load` still refuses aggregates. The backend loads a
primitive at its field offset, or `memory.copy`s an aggregate field into the
output value's own frame cell.

| Form | Code |
| --- | --- |
| Missing field (`let P { x } := p;`), unknown field, a field named twice, a binding name introduced twice, a non-struct type name | TE023 (the message lists the missing fields) |
| Nested pattern (`a: P { x, y }`), `..` omission, `:=` missing | SE002 |
| Reference source (`let P { x, y } := r;` with `r: borrow P`) | TE002 |
| Field or element source (`let P { x, y } := l.a;`) | TE022 |
| Value of another struct type | TE002 |
| Private field in another module's struct | TE025 |
| Assignment to a binding made by `let` | TE004 |
| Use of the source after destructuring | BE001 |

### Field-disjoint loans

Provenance and loans carry a place: a root (local, temporary, reference
parameter, external) plus a path of steps `Field(i)`, `Const(n)` (an index
produced by an integer `Constant`) and `Dynamic` (any other index).
`Borrow` keeps the path; `FieldAddr` and `ElementAddr` extend it. Two places
overlap when they have the same root and, comparing the steps both paths have,
no pair is provably different. Distinct fields and distinct constant indices
are different; a dynamic index may equal any index; a prefix overlaps
everything below it, so moving or reassigning a root conflicts with any live
loan below it. The rule applies to loan creation, loads, stores, owner moves,
assignments, terminator operands and call arguments. Examples:

- accepted: `l.a.borrow()` live while writing `l.b.x`;
  `f(l.a.share(), l.b.share())`; `f(m[0].share(), m[1].share())`;
  `m[0].share()` live while reading `m[1][2]`; `g.rows[0].share()` live while
  writing `g.rows[1][2]` or `g.tag`.
- rejected (BE005): the same field twice; `f(m[i].share(), m[j].share())`;
  `a[i].share()` live while writing `a[0]`; any live loan below a root while the
  root is moved or reassigned; `l.borrow()` live while writing `l.b.x` (a
  parent overlaps its children).

Two refinements keep chains precise. An address value used exactly once as the
base of another address instruction (`g.rows` in `g.rows[0]`) is path
computation, not an access of its own place, so it is not checked at creation;
the last address of the chain carries the access. A loan that is live only
because a live reference derives from it (an ancestor) does not conflict by
itself, the live descendants cover the memory still reachable.

References carry their places. A reborrow through a `borrow`/`share` parameter
extends the parameter's root path, so inside a callee `p.a.borrow()` live while
`p.b.x = 1` is accepted, and `p.a` against `p.a` is not. Different parameters
are different roots (the call site has already proven them disjoint), and every
external root (a call result reference) overlaps every other external root with
no path. Loops: constants identify a fixed index, a dynamic index never matches
a previous iteration, and the existing re-entered-`Share`-site rule is
unchanged, so a loan live across a back edge keeps its path.

### Still gated

Whole-struct `.copy()` (TE017); references to primitive fields and elements
(`l.a.x.share()`, TE017); field access or indexing on a temporary
(`make().a.x`, TE017); implicit partial field moves (TE022); nested or partial
destructuring patterns (SE002); aggregates in exported signatures (LE900).
