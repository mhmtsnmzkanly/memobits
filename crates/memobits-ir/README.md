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
values. It does not check loan lifetimes or implement borrow/share semantics;
the ownership gate now checks reference-handle availability and loan conflicts. The Wasm backend still rejects these operations.

Run tests with `cargo test --offline -p memobits-ir`.
