# memobits-ir

Data structures for a typed, explicit control-flow representation. A `Program`
indexes functions by `FunctionId`; each function has its own `LocalId`,
`ValueId`, and `BlockId` spaces. `CanonicalFunction` retains package, module,
and definition names separately. `parameter_locals` maps each signature
parameter to the local slot initialized on entry. An operand records whether it reads, consumes,
borrows, or shares its source. Branches carry block arguments so value-producing
expressions can join without a second type-inference pass.

`Program::validate` checks indices, definitions, edge arguments, and selected
type relationships. Entry blocks cannot have parameters, and `And`/`Or` must be
lowered as control flow so short-circuit evaluation is preserved. It does not
prove that values dominate their uses, that function bodies type-check
completely, or that ownership rules hold. Producers should return a program
only after semantic analysis succeeds. Spans on
synthetic instructions or edges can be `None`; source-originated uses retain
their original spans.

The IR includes reference-typed parameters and explicit `Borrow`, `Load`, and
`Store` instructions as a data model. Validation checks their structural types
and prevents loaded reference values from being consumed or escaping as owned
values (a loaded primitive reaches an owned position through `Copy`). It does not check loan lifetimes or implement borrow/share semantics;
the ownership gate now checks reference-handle availability and loan conflicts. The Wasm backend still rejects these operations.

`Program::types` holds nominal user-defined types (`TypeDef`, identified by
`TypeId` and a `CanonicalType` path); `Type::Struct(TypeId)` names one. A struct is
created by `StructNew` (one consumed operand per field, declaration order) and a
field is addressed by `FieldAddr { loan, base, field, access }`, the bounds-check-free
twin of `ElementAddr` that yields a `Reference` to the field type and is read with
`Load`. Validation checks type and field indices, operand count and types, access
modes and shared loan IDs. Struct fields are non-Unit primitives for now (so
recursive or nested struct types are rejected), and struct parameters, results,
block parameters, references and whole-struct loads are not valid yet.

Run tests with `cargo test --offline -p memobits-ir`.
