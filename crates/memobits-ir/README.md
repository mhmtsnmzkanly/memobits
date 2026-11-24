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
the ownership gate checks reference-handle availability and loan conflicts.
The Wasm backend emits these operations for supported internal references.
Reference returns and references stored inside aggregate values remain gated.

`Program::types` holds nominal user-defined types (`TypeDef`, identified by
`TypeId` and a `CanonicalType` path); `Type::Struct(TypeId)` names one. A struct is
created by `StructNew` (one consumed operand per field, declaration order) and a
field is addressed by `FieldAddr { loan, base, field, access }`, the bounds-check-free
twin of `ElementAddr` that yields a `Reference` to the field type and is read with
`Load`. Validation checks type and field indices, operand count and types, access
modes and shared loan IDs. `FieldAddr` accepts a struct owner or a `Reference` to a
struct (with at most the referent's access). Struct fields and array elements are non-Unit primitives, structs, enums, or arrays of
those at any depth; a struct that contains itself by value, directly or through arrays
and other structs, is rejected by validation. Mixed `FieldAddr` / `ElementAddr` chains
(`a[i].pts[j].x`) address nested aggregates level by level. Structs may be owned,
`borrow` or `share` parameters, function results and block parameters, and a
reference may refer to a struct; a whole-struct `Load` is invalid (fields are
addressed and loaded one by one). `Extract { base, field }` is the single way a field
leaves a struct as an owned value (whole-value destructuring): it reads a struct owner
with `Read`, or with `Consume` on the last extraction, and yields a fresh value of the
field's type. Validation requires that an aggregate extraction with a `Read` base is
followed in the same block by a consuming use (`Extract` or `Capture`) of the same base,
so the whole value is consumed exactly once and no partial move can be expressed.

`Type::Enum(TypeId)` names an enum, defined by `TypeDefKind::Enum { variants:
Vec<VariantDef { name, payload }> }` in the same type table (and id space) as structs. A
variant's index is its tag. `EnumNew { ty, variant, payload }` creates a value with one
consumed operand per payload type of that variant; validation checks the type id and kind,
the variant index, operand count, types, modes and the output type. Payload types follow
the struct field rules (non-Unit primitives, structs, enums, arrays; no references); an
empty enum, duplicate variant names and by-value recursion are rejected. Enums are
aggregates for borrow/share references, owners, parameters, results and block parameters;
a whole-enum `Load` is invalid. `EnumTag { base }` reads the tag of an enum owner (`Read`) or enum reference as a `u32`;
`VariantExtract { base, variant, field }` is the enum twin of `Extract` (same
consume-the-whole-value rule: an aggregate extraction with a `Read` base must be followed
in the block by a consuming use of the base); `TerminatorKind::Switch { tag, ty, targets,
default }` branches on a tag of enum `ty`. Validation checks the `u32` tag and enum type,
unique in-range variants, that every variant has a target or a default exists, and each
edge's block-parameter arguments. `VariantAddr { loan, base, variant, field, access }` (B3) is the enum twin of `FieldAddr`: a
reference to one payload field of an enum owner or enum reference, valid on the arm's path
(dominance is not validated); the validator checks variant and payload ranges, base mode and
access, the output `Reference` type and loan-id uniqueness. `EnumTag` also accepts a `Borrow`
mode on any enum reference.

Compiler-known outcomes use the same enum operations. `TypeDef::entry_outcome`
identifies `T ! E` and `T ?! E` (that is, `T? ! E`) instances for application entry validation and
emission. Nominal Error ancestry is tracked on struct definitions.

Run tests with `cargo test --offline -p memobits-ir`.
