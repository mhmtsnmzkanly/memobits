//! Data-only typed control-flow IR. Construction and semantic proof belong to
//! analysis passes; `validate` performs structural and selected type checks.
use memobits_diagnostics::Span;
use std::collections::HashSet;

mod scoped_string;
pub use scoped_string::{
    is_nominal_string_owner, is_string_owner_transport, HeapStrings, OwnerStructDef, OwnerTyView,
    OwnerTypeModel,
};

/// Reserved canonical module prefix used for imported host functions.
pub const HOST_IMPORT_MODULE: &str = "\0host";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FunctionId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LocalId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ValueId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BlockId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LoanId(pub u32);
/// Index into `Program::types`. Types are nominal: two definitions with equal
/// fields but different canonical paths are different types.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypeId(pub u32);

/// A definition's identity is independent of aliases and lexical spellings.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CanonicalFunction {
    pub package: String,
    pub module: Vec<String>,
    pub name: String,
}

/// A user-defined type's identity is independent of aliases and lexical spellings.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CanonicalType {
    pub package: String,
    pub module: Vec<String>,
    pub name: String,
}

/// One declared struct field. Fields are laid out in declaration order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldDef {
    pub name: String,
    pub ty: Type,
}

/// One enum variant: a name and its payload types, in declaration order. A
/// unit variant has an empty payload.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantDef {
    pub name: String,
    pub payload: Vec<Type>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeDefKind {
    /// Fields are non-Unit primitives, structs, enums or arrays of those.
    /// By-value recursion is rejected by validation.
    Struct { fields: Vec<FieldDef> },
    /// A tagged union with at least one variant. A variant's index is its
    /// declaration position and doubles as its tag value. Payload types follow
    /// the field rules of structs, with a local borrow Option exception.
    Enum { variants: Vec<VariantDef> },
}

/// Nominal links for the compiler-known Error hierarchy.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorAncestry {
    Root,
    Derived(TypeId),
}

/// Compiler-known outcome families permitted at an application entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EntryOutcome {
    Result,
}

impl EntryOutcome {
    pub fn variants(self) -> &'static [&'static str] {
        match self {
            Self::Result => &["Ok", "Err"],
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeDef {
    pub path: CanonicalType,
    pub span: Span,
    pub error_ancestry: Option<ErrorAncestry>,
    pub entry_outcome: Option<EntryOutcome>,
    pub kind: TypeDefKind,
}

impl TypeDef {
    fn is_scalar_option(&self, name: &str, payload: Primitive) -> bool {
        self.path.name == name
            && self.error_ancestry.is_none()
            && self.entry_outcome.is_none()
            && matches!(&self.kind, TypeDefKind::Enum { variants }
                if matches!(&variants[..], [some, none]
                    if some.name == "Some" && some.payload == [Type::Primitive(payload)]
                        && none.name == "None" && none.payload.is_empty()))
    }

    fn borrow_option_referent(&self) -> Option<&Type> {
        if !(self.path.name.starts_with("(borrow ") && self.path.name.ends_with(")?"))
            || self.error_ancestry.is_some()
            || self.entry_outcome.is_some()
        {
            return None;
        }
        let TypeDefKind::Enum { variants } = &self.kind else {
            return None;
        };
        let [some, none] = variants.as_slice() else {
            return None;
        };
        match some.payload.as_slice() {
            [Type::Reference {
                access: Access::Borrow,
                inner,
            }] if !matches!(inner.as_ref(), Type::List(_))
                && some.name == "Some"
                && none.name == "None"
                && none.payload.is_empty() =>
            {
                Some(inner)
            }
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Primitive {
    Unit,
    Bool,
    Char,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Primitive(Primitive),
    /// Owned UTF-8 text. Its storage representation is private to the backend.
    String,
    /// Owned homogeneous list with private descriptor storage.
    List(Box<Type>),
    Function(Signature),
    Reference {
        access: Access,
        inner: Box<Type>,
    },
    /// Fixed-length homogeneous array stored inline in its owner.
    Array {
        element: Box<Type>,
        len: u32,
    },
    /// A user-defined struct stored inline in its owner; the definition lives
    /// in `Program::types`.
    Struct(TypeId),
    /// A user-defined enum stored inline in its owner as a tag and a payload
    /// area; the definition (`TypeDefKind::Enum`) lives in `Program::types`.
    Enum(TypeId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Access {
    Owned,
    Borrow,
    Share,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParameterType {
    pub access: Access,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub parameters: Vec<ParameterType>,
    pub result: Box<Type>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UseMode {
    Read,
    Consume,
    Borrow,
    Share,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Source {
    Local(LocalId),
    Value(ValueId),
    Function(FunctionId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Operand {
    pub source: Source,
    pub mode: UseMode,
    /// The original source use, if one exists.
    pub span: Option<Span>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum LocalKind {
    /// A source binding, parameter or ordinary compiler temporary.
    #[default]
    Ordinary,
    /// Compiler-created sink for a match payload that the pattern ignores
    /// (`_`). Ownership validation does not treat an ignored heap payload as
    /// an accepted immediate consuming match.
    DiscardedMatchPayload,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Local {
    pub name: String,
    pub ty: Type,
    pub mutable: bool,
    pub kind: LocalKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constant {
    String(String),
    Integer(String),
    Float(String),
    Bool(bool),
    Unit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Plus,
    Negate,
    Not,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    WrappingAdd,
    WrappingMultiply,
    /// Modular subtraction at the operand width.
    WrappingSubtract,
    /// Left shift with the count masked to the operand width.
    WrappingShiftLeft,
    /// Right shift with the count masked to the operand width.
    WrappingShiftRight,
    /// Addition that clamps to the operand type's minimum or maximum.
    SaturatingAdd,
    SaturatingSubtract,
    SaturatingMultiply,
    /// Checked operations produce the scalar option `T?` (`None` on overflow,
    /// division by zero, or a shift count at or above the width).
    CheckedAdd,
    CheckedSubtract,
    CheckedMultiply,
    CheckedDivide,
    CheckedRemainder,
    CheckedShiftLeft,
    CheckedShiftRight,
    BitwiseAnd,
    BitwiseXor,
    BitwiseOr,
    ShiftLeft,
    ShiftRight,
    Divide,
    Remainder,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,
    And,
    Or,
}

/// The base operand of a projection, seen as a plain loan when the access is a
/// share (the heap-String check treats borrows and shares of an owner alike).
fn projection_base(base: &Operand, access: Access) -> Operand {
    let mut base = base.clone();
    if access == Access::Share && base.mode == UseMode::Share {
        base.mode = UseMode::Borrow;
    }
    base
}

/// One piece of an `InitInterpolatedString`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterpolationPart {
    /// Static UTF-8 text.
    Text(String),
    /// A read-only String borrow, or an integer, `Bool` or `Char` value that
    /// is formatted as decimal digits, `true`/`false` or its UTF-8 bytes.
    Value(Operand),
}

/// Initialisation of a freshly created array. Elements are never observably
/// uninitialised.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArrayInit {
    /// One consumed operand per element, in element order.
    Elements(Vec<Operand>),
    /// All elements zero. Reserved for repeat lowering.
    Zeroed,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstructionKind {
    Constant(Constant),
    /// Initialize an immutable lexical String owner by concatenating two borrows.
    InitConcatString {
        target: LocalId,
        strings: [Operand; 2],
    },
    /// Initialize an immutable lexical String owner from text and formatted
    /// values: the total length is computed first, the block is allocated
    /// once and every part is written in order. Value operands are read-only
    /// String borrows or integer, `Bool` and `Char` values.
    InitInterpolatedString {
        target: LocalId,
        parts: Vec<InterpolationPart>,
    },
    /// End lexical storage for a struct with String fields, even after a move.
    EndStructLocal {
        local: LocalId,
    },
    /// End lexical storage for a String local, even after a move.
    EndStringLocal {
        local: LocalId,
    },
    /// Release an available owner while keeping its binding in lexical scope.
    DropLocal {
        value: Operand,
    },
    /// Trap with an assertion failure unless the `bool` condition holds.
    Assert {
        condition: Operand,
    },
    /// Read the byte length of an owned String or a reference to one.
    /// Validate a logical byte prefix and optionally copy it into an owned String.
    ValidateUtf8 {
        source: Operand,
        length: Operand,
        construct_string: bool,
    },
    EmptyList,
    EndListLocal {
        local: LocalId,
    },
    ListClear {
        target: LocalId,
    },
    ListPop {
        target: LocalId,
    },
    ListPush {
        target: LocalId,
        value: Operand,
    },
    ListGet {
        source: Operand,
        index: Operand,
    },
    /// Read an initialized element by value, trapping if the index is out of bounds.
    ListRead {
        source: Operand,
        index: Operand,
    },
    ListLen {
        source: Operand,
    },
    /// Read a primitive collection through a shared loan, returning membership or the first index.
    CollectionSearch {
        source: Operand,
        value: Operand,
        return_index: bool,
    },
    StringLen {
        source: Operand,
    },
    /// Test whether a byte offset is an endpoint or starts a UTF-8 scalar.
    StringIsCharBoundary {
        source: Operand,
        offset: Operand,
    },
    /// Read a byte at an unsigned offset, producing an owned Option<u8>.
    StringByteAt {
        source: Operand,
        offset: Operand,
    },
    /// Read a Unicode scalar at a byte offset, producing an owned Option<u32>.
    StringScalarAt {
        source: Operand,
        offset: Operand,
    },
    /// Decode the scalar that starts at a byte offset known to be a boundary
    /// below the byte length (checked by the loop that emits it). `width: false`
    /// produces the `Char`; `width: true` produces its UTF-8 byte width as u32.
    StringScalarRead {
        source: Operand,
        offset: Operand,
        width: bool,
    },
    /// Capture an operand at this point in evaluation order.
    Capture(Operand),
    /// Create a statically checked reference to an owner or existing reference.
    Borrow {
        loan: LoanId,
        owner: Operand,
        access: Access,
    },
    /// Create an array value. The output type is the array type.
    ArrayNew {
        init: ArrayInit,
    },
    /// Array twin of `Borrow`: a reference to one element of an array owner or
    /// array reference. The bounds check against the array length is part of
    /// this instruction and traps at run time.
    ElementAddr {
        loan: LoanId,
        base: Operand,
        index: Operand,
        access: Access,
    },
    /// Create a struct value. One consumed operand per field, in declaration
    /// order; the output type is `Type::Struct(ty)`. Source evaluation order is
    /// decided by the operands' earlier instructions, not by this order.
    StructNew {
        ty: TypeId,
        fields: Vec<Operand>,
    },
    /// Create an enum value of variant `variant` (an index into the enum's
    /// variants). One consumed operand per payload type of that variant, in
    /// declaration order, so a unit variant has none; the output type is
    /// `Type::Enum(ty)`. As for `StructNew`, source evaluation order is decided
    /// by the operands' earlier instructions.
    EnumNew {
        ty: TypeId,
        variant: u32,
        payload: Vec<Operand>,
    },
    /// Struct twin of `ElementAddr` without a bounds check: a reference to one
    /// field of a struct owner. The output is `Reference { access, field type }`.
    FieldAddr {
        loan: LoanId,
        base: Operand,
        field: u32,
        access: Access,
    },
    /// Exchange the values of two disjoint places of the same type. Both
    /// operands are `Share` references to the same aggregate type; the bytes
    /// (descriptors) are exchanged without copying heap data or releasing
    /// anything. `replace` and owning overwrite are built on it.
    SwapPlaces {
        left: Operand,
        right: Operand,
    },
    /// Replace a String field of a mutable struct local with a consumed String local.
    ReplaceStringField {
        target: LocalId,
        field: u32,
        value: Operand,
    },
    /// Enum twin of `FieldAddr`: a reference to payload field `field` of variant
    /// `variant` of an enum owner or of a reference to one. The output is
    /// `Reference { access, payload type }`. It is only meaningful on a path
    /// where the enum's tag is `variant` (the `Switch` edge for it); the
    /// validator checks indices and types, not dominance. The loan path step
    /// for it is the variant and field, and different variants of one enum
    /// place overlap because they share the payload storage.
    VariantAddr {
        loan: LoanId,
        base: Operand,
        variant: u32,
        field: u32,
        access: Access,
    },
    /// Whole-value destructuring: read one field out of a struct owner into a
    /// fresh owned value of the field's type (a primitive is copied, a nested
    /// struct or array is moved by a bitwise copy). `base` is a struct owner
    /// used with `Read`, or with `Consume` on the last extraction. An extraction
    /// of an aggregate field with a `Read` base is only valid when a later
    /// instruction of the same block consumes that base, so the whole value is
    /// always consumed exactly once and no partial move is ever observable.
    Extract {
        base: Operand,
        field: u32,
    },
    /// Read the tag of an enum as a `u32` (the variant's index). `base` is an
    /// enum owner used with `Read`, or a `Borrow`/`Share` reference to one. A
    /// pure read.
    EnumTag {
        base: Operand,
    },
    /// Enum twin of `Extract`: read payload field `field` of variant `variant`
    /// out of an enum owner into a fresh owned value of the payload type (a
    /// primitive is copied, an aggregate is moved by a bitwise copy). `base` is
    /// used with `Read`, or with `Consume` on the last extraction; an aggregate
    /// extraction with a `Read` base must be followed, in the same block, by a
    /// consuming use of the base. It is only meaningful on a path where the
    /// enum's tag is `variant` (the `Switch` edge for it); the validator checks
    /// indices and types, not dominance.
    VariantExtract {
        base: Operand,
        variant: u32,
        field: u32,
    },
    /// Read the referent. The output is read-only provenance and cannot escape
    /// as an owned value without a future explicit copy operation.
    Load {
        reference: Operand,
    },
    /// Explicit copy of a primitive value. `source` is only read (use mode
    /// `Read`); it may be an owner, a parameter or a loaded referent. The output
    /// is an ordinary owned value, so it is not read-only provenance.
    Copy {
        source: Operand,
    },
    /// Write through an exclusive share reference.
    Store {
        reference: Operand,
        value: Operand,
    },
    Unary {
        op: UnaryOp,
        operand: Operand,
    },
    /// Explicit numeric conversion. `source` is retained so validation and
    /// backends can implement the source language's width and signedness rules.
    Cast {
        value: Operand,
        source: Primitive,
        target: Primitive,
    },
    Binary {
        op: BinaryOp,
        left: Operand,
        right: Operand,
    },
    /// `initialize` distinguishes a binding's first value from reassignment.
    Assign {
        target: LocalId,
        value: Operand,
        initialize: bool,
    },
    Call {
        callee: Operand,
        arguments: Vec<Operand>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Instruction {
    pub span: Option<Span>,
    /// Required for value-producing operations; absent for assignment.
    pub output: Option<ValueId>,
    pub kind: InstructionKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edge {
    pub target: BlockId,
    pub arguments: Vec<Operand>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TerminatorKind {
    Goto(Edge),
    Branch {
        condition: Operand,
        then_edge: Edge,
        else_edge: Edge,
    },
    /// Multi-way branch on an enum tag. `tag` is a `u32` produced by `EnumTag`
    /// of an enum of type `ty`; `targets` maps distinct variant indices to
    /// edges; `default` takes every variant not listed. Every variant must be
    /// listed or a default must exist, so a `Switch` never fails at run time.
    Switch {
        tag: Operand,
        ty: TypeId,
        targets: Vec<(u32, Edge)>,
        default: Option<Edge>,
    },
    Return(Option<Operand>),
    Unreachable,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Terminator {
    pub span: Option<Span>,
    pub kind: TerminatorKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub parameters: Vec<ValueId>,
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    pub path: CanonicalFunction,
    pub span: Span,
    pub signature: Signature,
    /// Local slots initialized by the corresponding incoming parameters.
    pub parameter_locals: Vec<LocalId>,
    pub locals: Vec<Local>,
    /// Types for function-local values, including block parameters.
    pub values: Vec<Type>,
    pub blocks: Vec<Block>,
    pub entry: BlockId,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Program {
    pub functions: Vec<Function>,
    /// User-defined types, indexed by `TypeId`.
    pub types: Vec<TypeDef>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidationError {
    pub function: Option<FunctionId>,
    pub block: Option<BlockId>,
    pub message: String,
}

impl Program {
    /// Check shape, indices, edge arguments, and basic operand types. This is
    /// not a complete type, dominance, or ownership proof.
    pub fn validate(&self) -> Result<(), Vec<ValidationError>> {
        let mut errors = Vec::new();
        let mut paths = HashSet::new();
        self.validate_types(&mut errors);
        let type_count = self.types.len();
        let heap_strings = self.heap_strings();
        for (index, function) in self.functions.iter().enumerate() {
            let id = FunctionId(index as u32);
            if !paths.insert(&function.path) {
                push(&mut errors, id, None, "duplicate canonical function path");
            }
            if function.path.package.is_empty()
                || function.path.name.is_empty()
                || function.path.module.is_empty()
                || function.path.module.iter().any(String::is_empty)
            {
                push(&mut errors, id, None, "invalid canonical function path");
            }
            if function.blocks.get(function.entry.0 as usize).is_none() {
                push(&mut errors, id, None, "entry block does not exist");
            } else if !function.blocks[function.entry.0 as usize]
                .parameters
                .is_empty()
            {
                push(
                    &mut errors,
                    id,
                    Some(function.entry),
                    "entry block cannot have parameters",
                );
            }
            if self.signature_contains_borrow_option(&function.signature) {
                push(
                    &mut errors,
                    id,
                    None,
                    "borrow Option is not supported in signatures",
                );
            }
            for ty in function
                .locals
                .iter()
                .map(|local| &local.ty)
                .chain(&function.values)
            {
                if self.contains_borrow_option(ty) && !self.is_borrow_option(ty) {
                    push(
                        &mut errors,
                        id,
                        None,
                        "borrow Option cannot be nested or addressed",
                    );
                }
            }
            for parameter in &function.signature.parameters {
                validate_parameter_type(
                    type_count,
                    &parameter.ty,
                    &mut errors,
                    id,
                    "function parameter",
                );
            }
            validate_signature_value_type(
                type_count,
                &function.signature.result,
                &mut errors,
                id,
                "function result",
            );
            for local in &function.locals {
                validate_type_shape(type_count, &local.ty, &mut errors, id, "local");
            }
            for value in &function.values {
                validate_type_shape(type_count, value, &mut errors, id, "value");
            }
            if function.parameter_locals.len() != function.signature.parameters.len() {
                push(
                    &mut errors,
                    id,
                    None,
                    "parameter local count differs from signature",
                );
            }
            let mut parameter_set = HashSet::new();
            for (local, parameter) in function
                .parameter_locals
                .iter()
                .zip(&function.signature.parameters)
            {
                if !parameter_set.insert(*local) {
                    push(
                        &mut errors,
                        id,
                        None,
                        "parameter local is listed more than once",
                    );
                }
                match function.locals.get(local.0 as usize) {
                    None => push(&mut errors, id, None, "parameter local is out of range"),
                    Some(slot) if slot.ty != parameter_local_type(parameter) => push(
                        &mut errors,
                        id,
                        None,
                        "parameter local type differs from signature access mode",
                    ),
                    _ => {}
                }
            }
            let mut defined = HashSet::new();
            let mut loans = HashSet::new();
            let mut borrow_option_initializers = HashSet::new();
            for (block_index, block) in function.blocks.iter().enumerate() {
                let block_id = BlockId(block_index as u32);
                for value in &block.parameters {
                    if matches!(function.values.get(value.0 as usize), Some(Type::List(_))) {
                        push(
                            &mut errors,
                            id,
                            Some(block_id),
                            "List cannot be passed across a block edge",
                        );
                    }
                    if function
                        .values
                        .get(value.0 as usize)
                        .is_some_and(|ty| self.is_borrow_option(ty))
                    {
                        push(
                            &mut errors,
                            id,
                            Some(block_id),
                            "borrow Option cannot be passed across a block edge",
                        );
                    }
                    define_value(function, *value, &mut defined, &mut errors, id, block_id);
                }
                for (instruction_index, instruction) in block.instructions.iter().enumerate() {
                    validate_instruction(self, function, instruction, &mut errors, id, block_id);
                    // Initialization is a declaration site. A loop may execute
                    // that site again, but a second site would permit reassignment.
                    if let InstructionKind::Assign {
                        target,
                        initialize: true,
                        ..
                    } = instruction.kind
                    {
                        let is_wrapper = function
                            .locals
                            .get(target.0 as usize)
                            .is_some_and(|local| self.is_borrow_option(&local.ty));
                        if is_wrapper && !borrow_option_initializers.insert(target) {
                            push(
                                &mut errors,
                                id,
                                Some(block_id),
                                "borrow Option local has more than one initialization site",
                            );
                        }
                    }
                    validate_extract_consumption(
                        function,
                        &block.instructions[instruction_index..],
                        &mut errors,
                        id,
                        block_id,
                    );
                    if let InstructionKind::Borrow { loan, .. }
                    | InstructionKind::ElementAddr { loan, .. }
                    | InstructionKind::FieldAddr { loan, .. }
                    | InstructionKind::VariantAddr { loan, .. } = &instruction.kind
                    {
                        if !loans.insert(*loan) {
                            push(
                                &mut errors,
                                id,
                                Some(block_id),
                                "loan ID is defined more than once",
                            );
                        }
                    }
                    if let Some(value) = instruction.output {
                        define_value(function, value, &mut defined, &mut errors, id, block_id);
                    }
                }
                validate_terminator(self, function, &block.terminator, &mut errors, id, block_id);
            }
            if defined.len() != function.values.len() {
                push(&mut errors, id, None, "some value IDs have no definition");
            }
            scoped_string::validate(self, function, id, &heap_strings, &mut errors);
            validate_operand_escapes(self, function, id, &heap_strings, &mut errors);
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

impl Program {
    /// Check the compiler-known error layout consumed by the UTF-8 backend.
    pub fn utf8_outcome_error(&self, ty: &Type, success: &Type) -> Option<TypeId> {
        let Type::Enum(result) = ty else {
            return None;
        };
        let result = self.types.get(result.0 as usize)?;
        if result.entry_outcome != Some(EntryOutcome::Result) {
            return None;
        }
        let TypeDefKind::Enum { variants } = &result.kind else {
            return None;
        };
        let [ok, err] = variants.as_slice() else {
            return None;
        };
        let [Type::Struct(error)] = err.payload.as_slice() else {
            return None;
        };
        let def = self.types.get(error.0 as usize)?;
        let TypeDefKind::Struct { fields } = &def.kind else {
            return None;
        };
        let [code, offset] = fields.as_slice() else {
            return None;
        };
        let Type::Enum(option) = offset.ty else {
            return None;
        };
        let Some(ErrorAncestry::Derived(parent)) = def.error_ancestry else {
            return None;
        };
        (ok.payload.as_slice() == std::slice::from_ref(success)
            && def.path.module == ["__prelude"]
            && def.path.name == "Utf8Error"
            && code.name == "code"
            && code.ty == Type::Primitive(Primitive::U32)
            && offset.name == "offset"
            && self.types.get(parent.0 as usize)?.error_ancestry == Some(ErrorAncestry::Root)
            && self
                .types
                .get(option.0 as usize)?
                .is_scalar_option("i32?", Primitive::I32))
        .then_some(*error)
    }

    fn is_borrow_option(&self, ty: &Type) -> bool {
        matches!(ty, Type::Enum(id) if self.types.get(id.0 as usize)
            .and_then(TypeDef::borrow_option_referent).is_some())
    }

    fn contains_borrow_option(&self, ty: &Type) -> bool {
        match ty {
            Type::Array { element, .. } | Type::Reference { inner: element, .. } => {
                self.contains_borrow_option(element)
            }
            Type::Function(signature) => self.signature_contains_borrow_option(signature),
            _ => self.is_borrow_option(ty),
        }
    }

    fn signature_contains_borrow_option(&self, signature: &Signature) -> bool {
        self.contains_borrow_option(&signature.result)
            || signature
                .parameters
                .iter()
                .any(|parameter| self.contains_borrow_option(&parameter.ty))
    }

    fn valid_field_type(&self, ty: &Type) -> bool {
        field_type_is_valid(ty, self.types.len()) && !self.contains_borrow_option(ty)
    }

    fn has_error_ancestor(&self, actual: &Type, expected: &Type) -> bool {
        let (Type::Struct(mut child), Type::Struct(ancestor)) = (actual, expected) else {
            return false;
        };
        if child == *ancestor {
            return false;
        }
        // Validation also runs on IR with malformed or cyclic parent links.
        for _ in &self.types {
            let Some(ErrorAncestry::Derived(parent)) = self
                .types
                .get(child.0 as usize)
                .and_then(|ty| ty.error_ancestry)
            else {
                break;
            };
            if parent == *ancestor {
                return true;
            }
            child = parent;
        }
        false
    }

    fn validate_types(&self, errors: &mut Vec<ValidationError>) {
        let mut paths = HashSet::new();
        let root = self
            .types
            .iter()
            .position(|ty| ty.error_ancestry == Some(ErrorAncestry::Root));
        for (index, definition) in self.types.iter().enumerate() {
            let mut report = |message: String| {
                errors.push(ValidationError {
                    function: None,
                    block: None,
                    message,
                });
            };
            let path = &definition.path;
            if path.package.is_empty()
                || path.name.is_empty()
                || path.module.is_empty()
                || path.module.iter().any(String::is_empty)
            {
                report("invalid canonical type path".into());
            }
            if !paths.insert(path) {
                report(format!("duplicate canonical type path '{}'", path.name));
            }
            match definition.error_ancestry {
                Some(ErrorAncestry::Root) => {
                    if Some(index) != root
                        || path.module != ["__prelude"]
                        || path.name != "Error"
                        || !matches!(&definition.kind, TypeDefKind::Struct { fields }
                            if matches!(fields.as_slice(), [field]
                                if field.name == "code" && field.ty == Type::Primitive(Primitive::U32)))
                    {
                        report("invalid compiler-known Error root".into());
                    }
                }
                Some(ErrorAncestry::Derived(parent)) => {
                    if !root.is_some_and(|root| {
                        self.has_error_ancestor(
                            &Type::Struct(TypeId(index as u32)),
                            &Type::Struct(TypeId(root as u32)),
                        )
                    }) {
                        report(format!(
                            "error type '{}' has no valid Error ancestor",
                            path.name
                        ));
                    }
                    if !matches!(
                        (&definition.kind, self.types.get(parent.0 as usize)),
                        (TypeDefKind::Struct { fields }, Some(TypeDef {
                            kind: TypeDefKind::Struct { fields: inherited }, ..
                        })) if fields.starts_with(inherited)
                    ) {
                        report(format!(
                            "error type '{}' does not preserve its parent's field prefix",
                            path.name
                        ));
                    }
                }
                None => {}
            }
            if let Some(outcome) = definition.entry_outcome {
                let valid = match &definition.kind {
                    TypeDefKind::Enum { variants } => {
                        let names = outcome.variants();
                        variants.len() == names.len()
                            && variants
                                .iter()
                                .zip(names)
                                .all(|(variant, name)| variant.name == *name)
                            && variants[0].payload.len() == 1
                            && matches!(
                                variants[names.len() - 1].payload.as_slice(),
                                [Type::Struct(id)] if self.types.get(id.0 as usize)
                                    .is_some_and(|ty| ty.error_ancestry.is_some())
                            )
                    }
                    _ => false,
                };
                if !valid {
                    report("invalid compiler-known entry outcome shape".into());
                }
            }
            match &definition.kind {
                TypeDefKind::Struct { fields } => {
                    let mut names = HashSet::new();
                    for field in fields {
                        if !names.insert(&field.name) {
                            report(format!(
                                "struct '{}' declares field '{}' more than once",
                                path.name, field.name
                            ));
                        }
                        if !self.valid_field_type(&field.ty) {
                            report(format!(
                                "field '{}' of struct '{}' must be a non-Unit primitive, a struct, an enum or an array of such types; reference fields are not supported",
                                field.name, path.name
                            ));
                        }
                    }
                }
                TypeDefKind::Enum { variants } => {
                    if variants.is_empty() {
                        report(format!("enum '{}' has no variants", path.name));
                    }
                    let mut names = HashSet::new();
                    for variant in variants {
                        if !names.insert(&variant.name) {
                            report(format!(
                                "enum '{}' declares variant '{}' more than once",
                                path.name, variant.name
                            ));
                        }
                        let valid = if let Some(inner) = definition.borrow_option_referent() {
                            self.valid_field_type(inner)
                        } else {
                            // `List<T>?` from `pop()` carries a List payload.
                            variant.payload.iter().all(|ty| match ty {
                                Type::List(element) => {
                                    self.valid_field_type(element)
                                        || matches!(element.as_ref(), Type::List(_))
                                }
                                ty => self.valid_field_type(ty),
                            })
                        };
                        if !valid {
                            report(format!(
                                "payload of variant '{}' of enum '{}' must be non-Unit primitives, structs, enums or arrays of such types or a supported local borrow Option reference",
                                variant.name, path.name
                            ));
                        }
                    }
                }
            }
        }
        // A struct or enum that contains itself by value, directly or through
        // arrays, structs and enum payloads, has no finite size.
        for start in 0..self.types.len() {
            if self.type_reaches(start, start) {
                let what = match self.types[start].kind {
                    TypeDefKind::Struct { .. } => "struct",
                    TypeDefKind::Enum { .. } => "enum",
                };
                errors.push(ValidationError {
                    function: None,
                    block: None,
                    message: format!(
                        "{what} '{}' contains itself by value",
                        self.types[start].path.name
                    ),
                });
            }
        }
    }

    /// Whether type `from` contains type `to` by value (one or more steps).
    fn type_reaches(&self, from: usize, to: usize) -> bool {
        let mut seen = HashSet::new();
        let mut pending = vec![from];
        let mut first = true;
        while let Some(current) = pending.pop() {
            if !first && current == to {
                return true;
            }
            first = false;
            if !seen.insert(current) {
                continue;
            }
            match &self.types[current].kind {
                TypeDefKind::Struct { fields } => {
                    for field in fields {
                        collect_struct_ids(&field.ty, &mut pending, self.types.len());
                    }
                }
                TypeDefKind::Enum { variants } => {
                    for ty in variants.iter().flat_map(|variant| &variant.payload) {
                        collect_struct_ids(ty, &mut pending, self.types.len());
                    }
                }
            }
        }
        false
    }
}

fn collect_struct_ids(ty: &Type, out: &mut Vec<usize>, count: usize) {
    match ty {
        Type::Struct(id) | Type::Enum(id) if (id.0 as usize) < count => out.push(id.0 as usize),
        Type::Array { element, .. } => collect_struct_ids(element, out, count),
        _ => {}
    }
}

/// Field, payload and array-element types: non-Unit primitives, structs and enums in range, and
/// arrays of those, at any depth.
fn field_type_is_valid(ty: &Type, type_count: usize) -> bool {
    match ty {
        Type::Primitive(kind) => *kind != Primitive::Unit,
        Type::String => true,
        Type::Struct(id) | Type::Enum(id) => (id.0 as usize) < type_count,
        Type::Array { element, .. } => field_type_is_valid(element, type_count),
        _ => false,
    }
}

fn push(
    errors: &mut Vec<ValidationError>,
    function: FunctionId,
    block: Option<BlockId>,
    message: impl Into<String>,
) {
    errors.push(ValidationError {
        function: Some(function),
        block,
        message: message.into(),
    });
}

fn parameter_local_type(parameter: &ParameterType) -> Type {
    match parameter.access {
        Access::Owned => parameter.ty.clone(),
        access => Type::Reference {
            access,
            inner: Box::new(parameter.ty.clone()),
        },
    }
}

/// A parameter names its pointee type: a primitive or a fixed array of
/// primitives, passed by ownership, `borrow` or `share`.
fn validate_parameter_type(
    type_count: usize,
    ty: &Type,
    errors: &mut Vec<ValidationError>,
    id: FunctionId,
    context: &str,
) {
    if matches!(ty, Type::Reference { .. }) {
        push(
            errors,
            id,
            None,
            format!("{context} type cannot be a reference"),
        );
    }
    validate_type_shape(type_count, ty, errors, id, context);
}

fn validate_signature_value_type(
    type_count: usize,
    ty: &Type,
    errors: &mut Vec<ValidationError>,
    id: FunctionId,
    context: &str,
) {
    if matches!(ty, Type::Reference { .. }) {
        push(
            errors,
            id,
            None,
            format!("{context} type cannot be a reference"),
        );
    }
    validate_type_shape(type_count, ty, errors, id, context);
}

fn validate_type_shape(
    type_count: usize,
    ty: &Type,
    errors: &mut Vec<ValidationError>,
    id: FunctionId,
    context: &str,
) {
    match ty {
        Type::List(element) => match element.as_ref() {
            Type::Primitive(kind) if *kind != Primitive::Unit => {}
            Type::String => {}
            Type::Array { .. } | Type::Struct(_) | Type::Enum(_) | Type::List(_) => {
                validate_type_shape(type_count, element, errors, id, context)
            }
            _ => push(errors, id, None, "unsupported List element type"),
        },
        Type::Primitive(_) | Type::String => {}
        Type::Struct(type_id) | Type::Enum(type_id) => {
            if type_id.0 as usize >= type_count {
                push(
                    errors,
                    id,
                    None,
                    format!("{context} type {:?} is out of range", type_id),
                );
            }
        }
        Type::Function(signature) => {
            for parameter in &signature.parameters {
                validate_parameter_type(
                    type_count,
                    &parameter.ty,
                    errors,
                    id,
                    "function type parameter",
                );
            }
            validate_signature_value_type(
                type_count,
                &signature.result,
                errors,
                id,
                "function type result",
            );
        }
        Type::Reference { access, inner } => {
            if *access == Access::Owned {
                push(
                    errors,
                    id,
                    None,
                    format!("{context} reference cannot use Owned access"),
                );
            }
            if !matches!(
                inner.as_ref(),
                Type::Primitive(_)
                    | Type::String
                    | Type::List(_)
                    | Type::Array { .. }
                    | Type::Struct(_)
                    | Type::Enum(_)
            ) {
                push(
                    errors,
                    id,
                    None,
                    format!(
                        "{context} reference must refer to a primitive value, an array or a struct"
                    ),
                );
            }
            if matches!(
                inner.as_ref(),
                Type::List(_) | Type::Array { .. } | Type::Struct(_) | Type::Enum(_)
            ) {
                validate_type_shape(type_count, inner, errors, id, context);
            }
        }
        Type::Array { element, len: _ } => match element.as_ref() {
            Type::Primitive(p) if *p != Primitive::Unit => {}
            Type::String => {}
            Type::Array { .. } | Type::Struct(_) | Type::Enum(_) => {
                validate_type_shape(type_count, element, errors, id, context)
            }
            _ => push(
                errors,
                id,
                None,
                format!(
                    "{context} array element must be a non-Unit primitive, a struct or an array"
                ),
            ),
        },
    }
}

/// A List read accepts an owner or a read-only reference to its descriptor.
fn list_read_element(ty: &Type) -> Option<Type> {
    match ty {
        Type::List(element) => Some(element.as_ref().clone()),
        Type::Reference {
            access: Access::Borrow | Access::Share,
            inner,
        } => match inner.as_ref() {
            Type::List(element) => Some(element.as_ref().clone()),
            _ => None,
        },
        _ => None,
    }
}

fn mutable_list_element(function: &Function, target: LocalId) -> Option<Type> {
    let local = function.locals.get(target.0 as usize)?;
    match &local.ty {
        Type::List(element) if local.mutable => Some(element.as_ref().clone()),
        Type::Reference {
            access: Access::Share,
            inner,
        } if local.mutable || function.parameter_locals.contains(&target) => {
            list_read_element(inner)
        }
        _ => None,
    }
}

/// `output` is the `T?` enum whose `Some` payload is exactly `element`.
fn option_matches(program: &Program, element: Option<&Type>, output: Option<&Type>) -> bool {
    match (element, output) {
        (Some(element), Some(Type::Enum(option))) => program
            .types
            .get(option.0 as usize)
            .is_some_and(|definition| {
                definition.path.name.ends_with('?')
                    && definition.error_ancestry.is_none()
                    && definition.entry_outcome.is_none()
                    && matches!(&definition.kind, TypeDefKind::Enum { variants }
                        if matches!(&variants[..], [some, none]
                            if some.name == "Some" && some.payload == [element.clone()]
                                && none.name == "None" && none.payload.is_empty()))
            }),
        _ => false,
    }
}

fn use_mode_for_access(access: Access) -> Option<UseMode> {
    match access {
        Access::Owned => None,
        Access::Borrow => Some(UseMode::Borrow),
        Access::Share => Some(UseMode::Share),
    }
}

/// An aggregate `Extract` that only reads its base must be followed, in the
/// same block, by an instruction that consumes the base. This keeps whole-value
/// destructuring the only way an aggregate leaves a struct.
fn validate_extract_consumption(
    function: &Function,
    rest: &[Instruction],
    errors: &mut Vec<ValidationError>,
    id: FunctionId,
    block: BlockId,
) {
    let Some((base, output)) = (match rest.first() {
        Some(Instruction {
            kind:
                InstructionKind::Extract { base, .. } | InstructionKind::VariantExtract { base, .. },
            output: Some(output),
            ..
        }) => Some((base, output)),
        _ => None,
    }) else {
        return;
    };
    let aggregate = function.values.get(output.0 as usize).is_some_and(|ty| {
        matches!(
            ty,
            Type::String | Type::Array { .. } | Type::Struct(_) | Type::Enum(_)
        )
    });
    if !aggregate || base.mode == UseMode::Consume {
        return;
    }
    let consumed = rest[1..].iter().any(|later| match &later.kind {
        InstructionKind::Extract { base: other, .. }
        | InstructionKind::VariantExtract { base: other, .. } => {
            other.source == base.source && other.mode == UseMode::Consume
        }
        InstructionKind::Capture(operand) => {
            operand.source == base.source && operand.mode == UseMode::Consume
        }
        _ => false,
    });
    if !consumed {
        push(
            errors,
            id,
            Some(block),
            "aggregate field extraction must be followed by a consuming use of the whole value in the same block",
        );
    }
}

fn define_value(
    function: &Function,
    value: ValueId,
    defined: &mut HashSet<ValueId>,
    errors: &mut Vec<ValidationError>,
    id: FunctionId,
    block: BlockId,
) {
    if function.values.get(value.0 as usize).is_none() {
        push(
            errors,
            id,
            Some(block),
            format!("value {:?} is out of range", value),
        );
    } else if !defined.insert(value) {
        push(
            errors,
            id,
            Some(block),
            format!("value {:?} is defined more than once", value),
        );
    }
}

fn operand_type<'a>(
    program: &'a Program,
    function: &'a Function,
    operand: &Operand,
    errors: &mut Vec<ValidationError>,
    id: FunctionId,
    block: BlockId,
) -> Option<Type> {
    let ty = match operand.source {
        Source::Local(local) => function.locals.get(local.0 as usize).map(|l| l.ty.clone()),
        Source::Value(value) => function.values.get(value.0 as usize).cloned(),
        Source::Function(target) => program
            .functions
            .get(target.0 as usize)
            .map(|f| Type::Function(f.signature.clone())),
    };
    if ty.is_none() {
        push(
            errors,
            id,
            Some(block),
            format!("operand source {:?} is out of range", operand.source),
        );
    }
    if matches!(operand.source, Source::Function(_)) && operand.mode != UseMode::Read {
        push(
            errors,
            id,
            Some(block),
            "function reference must use Read mode",
        );
    }
    ty
}

fn output_type(function: &Function, output: Option<ValueId>) -> Option<&Type> {
    output.and_then(|id| function.values.get(id.0 as usize))
}

fn validate_instruction(
    program: &Program,
    function: &Function,
    instruction: &Instruction,
    errors: &mut Vec<ValidationError>,
    id: FunctionId,
    block: BlockId,
) {
    let out = output_type(function, instruction.output);
    match &instruction.kind {
        InstructionKind::EmptyList => {
            if !matches!(out, Some(Type::List(_))) {
                push(errors, id, Some(block), "empty List requires a List output");
            }
        }
        InstructionKind::EndListLocal { local } => {
            if instruction.output.is_some()
                || !function
                    .locals
                    .get(local.0 as usize)
                    .is_some_and(|entry| matches!(entry.ty, Type::List(_)))
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "List scope exit requires a List local and no output",
                );
            }
        }
        InstructionKind::ListClear { target } => {
            if mutable_list_element(function, *target).is_none() || instruction.output.is_some() {
                push(
                    errors,
                    id,
                    Some(block),
                    "List clear requires a mutable owner or share and no output",
                );
            }
        }
        InstructionKind::ListPop { target } => {
            if !option_matches(
                program,
                mutable_list_element(function, *target).as_ref(),
                out,
            ) {
                push(
                    errors,
                    id,
                    Some(block),
                    "List pop requires a mutable owner or share and matching Option output",
                );
            }
        }
        InstructionKind::ListPush { target, value } => {
            let actual = operand_type(program, function, value, errors, id, block);
            let receiver = mutable_list_element(function, *target);
            let owned_element = receiver
                .as_ref()
                .is_some_and(|element| !matches!(element, Type::Primitive(_)));
            let expected_mode = if owned_element {
                UseMode::Consume
            } else {
                UseMode::Read
            };
            if receiver != actual
                || receiver.is_none()
                || instruction.output.is_some()
                || value.mode != expected_mode
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "List push requires a mutable owner or share and a matching element",
                );
            }
        }
        InstructionKind::ListGet { source, index } => {
            let input = operand_type(program, function, source, errors, id, block);
            let index_type = operand_type(program, function, index, errors, id, block);
            let element = input.as_ref().and_then(list_read_element);
            let valid_output = matches!(element, Some(Type::Primitive(_)))
                && option_matches(program, element.as_ref(), out);
            if !matches!(source.source, Source::Local(_))
                || source.mode != UseMode::Read
                || index.mode != UseMode::Read
                || index_type != Some(Type::Primitive(Primitive::U32))
                || !valid_output
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "List get requires a local read, u32 index, and matching Option output",
                );
            }
        }
        InstructionKind::ListRead { source, index } => {
            let input = operand_type(program, function, source, errors, id, block);
            let index_type = operand_type(program, function, index, errors, id, block);
            let element = match input {
                Some(Type::Reference {
                    access: Access::Borrow,
                    inner,
                }) => list_read_element(&inner),
                _ => None,
            };
            if source.mode != UseMode::Read
                || index.mode != UseMode::Read
                || index_type != Some(Type::Primitive(Primitive::U32))
                || !matches!(element, Some(Type::Primitive(_)))
                || element.as_ref() != out
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "List read requires a borrowed List, u32 index, and matching element output",
                );
            }
        }
        InstructionKind::CollectionSearch {
            source,
            value,
            return_index,
        } => {
            let input = operand_type(program, function, source, errors, id, block);
            let needle = operand_type(program, function, value, errors, id, block);
            let element = match input {
                Some(Type::Reference {
                    access: Access::Borrow,
                    inner,
                }) => match *inner {
                    Type::Array { element, .. } => match *element {
                        Type::Primitive(kind) if kind != Primitive::Unit => Some(kind),
                        _ => None,
                    },
                    Type::List(element) => match *element {
                        Type::Primitive(kind) if kind != Primitive::Unit => Some(kind),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            };
            let valid_output = if *return_index {
                option_matches(program, Some(&Type::Primitive(Primitive::U32)), out)
            } else {
                out == Some(&Type::Primitive(Primitive::Bool))
            };
            if source.mode != UseMode::Read
                || value.mode != UseMode::Read
                || element.is_none()
                || element.map(Type::Primitive) != needle
                || !valid_output
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "collection search requires a borrowed primitive collection, matching scalar value, and the corresponding bool or u32? output",
                );
            }
        }
        InstructionKind::ListLen { source } => {
            let input = operand_type(program, function, source, errors, id, block);
            if input.as_ref().and_then(list_read_element).is_none()
                || (!matches!(source.source, Source::Local(_))
                    && !matches!(input, Some(Type::Reference { .. })))
                || source.mode != UseMode::Read
                || out != Some(&Type::Primitive(Primitive::U32))
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "List length requires a local or reference read and u32 output",
                );
            }
        }
        InstructionKind::ValidateUtf8 {
            source,
            length,
            construct_string,
        } => {
            let input = operand_type(program, function, source, errors, id, block);
            let len = operand_type(program, function, length, errors, id, block);
            if !matches!(input, Some(Type::Reference { access: Access::Borrow, inner })
                if matches!(inner.as_ref(), Type::Array { element, .. } if **element == Type::Primitive(Primitive::U8)))
                || source.mode != UseMode::Read
                || length.mode != UseMode::Read
                || len != Some(Type::Primitive(Primitive::I32))
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "UTF-8 validation requires a borrowed byte array and i32 length",
                );
            }
            let success = if *construct_string {
                Type::String
            } else {
                Type::Primitive(Primitive::I32)
            };
            let valid_result = out
                .and_then(|ty| program.utf8_outcome_error(ty, &success))
                .is_some();
            if !valid_result {
                push(
                    errors,
                    id,
                    Some(block),
                    "invalid result type for UTF-8 operation",
                );
            }
        }
        InstructionKind::InitInterpolatedString { target, parts } => {
            let valid_local = function
                .locals
                .get(target.0 as usize)
                .is_some_and(|local| local.ty == Type::String)
                && !function.parameter_locals.contains(target);
            if !valid_local || instruction.output.is_some() {
                push(
                    errors,
                    id,
                    Some(block),
                    "string interpolation requires a new String local and no output",
                );
            }
            for part in parts {
                let InterpolationPart::Value(source) = part else {
                    continue;
                };
                let input = operand_type(program, function, source, errors, id, block);
                let formattable = match &input {
                    Some(Type::Reference {
                        access: Access::Borrow,
                        inner,
                    }) => **inner == Type::String,
                    Some(Type::Primitive(kind)) => {
                        !matches!(kind, Primitive::Unit | Primitive::F32 | Primitive::F64)
                    }
                    _ => false,
                };
                if !formattable || source.mode != UseMode::Read {
                    push(
                        errors,
                        id,
                        Some(block),
                        "string interpolation requires read-only String borrows or integer, bool and char values",
                    );
                }
            }
        }
        InstructionKind::InitConcatString { target, strings } => {
            let valid_local = function
                .locals
                .get(target.0 as usize)
                .is_some_and(|local| local.ty == Type::String)
                && !function.parameter_locals.contains(target);
            if !valid_local || instruction.output.is_some() {
                push(
                    errors,
                    id,
                    Some(block),
                    "concat requires a new String local and no output",
                );
            }
            for source in strings {
                let input = operand_type(program, function, source, errors, id, block);
                if !matches!(input, Some(Type::Reference { access: Access::Borrow, inner }) if *inner == Type::String)
                    || source.mode != UseMode::Read
                {
                    push(
                        errors,
                        id,
                        Some(block),
                        "concat requires read-only String borrows",
                    );
                }
            }
        }
        InstructionKind::Assert { condition } => {
            let ty = operand_type(program, function, condition, errors, id, block);
            if instruction.output.is_some()
                || condition.mode == UseMode::Consume
                || ty != Some(Type::Primitive(Primitive::Bool))
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "assert requires a non-consumed bool condition and no output",
                );
            }
        }
        InstructionKind::DropLocal { value } => {
            let ty = operand_type(program, function, value, errors, id, block);
            if instruction.output.is_some()
                || value.mode != UseMode::Consume
                || !matches!(value.source, Source::Local(_))
                || !matches!(ty, Some(Type::String | Type::List(_)))
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "drop requires a consumed String or primitive List local and no output",
                );
            }
        }
        InstructionKind::EndStructLocal { local } => {
            if instruction.output.is_some()
                || !function
                    .locals
                    .get(local.0 as usize)
                    .is_some_and(|local| scoped_string::owns_string_aggregate(program, &local.ty))
            {
                let message = function.locals.get(local.0 as usize).map_or(
                    "struct scope exit requires a String-owning struct local and no output",
                    |binding| match &binding.ty {
                        Type::Enum(_) => {
                            "enum scope exit requires a String-owning enum local and no output"
                        }
                        _ => {
                            "struct scope exit requires a String-owning struct local and no output"
                        }
                    },
                );
                push(errors, id, Some(block), message);
            }
        }
        InstructionKind::EndStringLocal { local } => {
            if instruction.output.is_some()
                || !function
                    .locals
                    .get(local.0 as usize)
                    .is_some_and(|local| local.ty == Type::String)
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "String scope exit requires a String local and no output",
                );
            }
        }
        InstructionKind::Constant(value) => {
            if out.is_none() {
                push(errors, id, Some(block), "constant requires an output value");
            }
            let okay = matches!(
                (value, out),
                (
                    Constant::Integer(_),
                    Some(Type::Primitive(
                        Primitive::I8
                            | Primitive::I16
                            | Primitive::I32
                            | Primitive::I64
                            | Primitive::U8
                            | Primitive::U16
                            | Primitive::U32
                            | Primitive::U64
                            | Primitive::Char,
                    )),
                ) | (
                    Constant::Float(_),
                    Some(Type::Primitive(Primitive::F32 | Primitive::F64))
                ) | (Constant::Bool(_), Some(Type::Primitive(Primitive::Bool)))
                    | (Constant::Unit, Some(Type::Primitive(Primitive::Unit)))
                    | (Constant::String(_), Some(Type::String))
            );
            let valid_char = match (value, out) {
                (Constant::Integer(text), Some(Type::Primitive(Primitive::Char))) => {
                    text.parse::<u32>().ok().and_then(char::from_u32).is_some()
                }
                _ => true,
            };
            if out.is_some() && (!okay || !valid_char) {
                push(
                    errors,
                    id,
                    Some(block),
                    "constant output type is incompatible",
                );
            }
        }
        InstructionKind::Capture(operand) => {
            let input = operand_type(program, function, operand, errors, id, block);
            if input
                .as_ref()
                .is_some_and(|ty| program.is_borrow_option(ty))
                && operand.mode != UseMode::Consume
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "borrow Option capture must consume its operand",
                );
            }
            if out.is_none() {
                push(errors, id, Some(block), "capture requires an output value");
            }
            if input
                .as_ref()
                .zip(out)
                .is_some_and(|(input, output)| input != output)
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "capture output type differs from operand type",
                );
            }
        }
        InstructionKind::StringLen { source }
        | InstructionKind::StringIsCharBoundary { source, .. }
        | InstructionKind::StringByteAt { source, .. }
        | InstructionKind::StringScalarAt { source, .. }
        | InstructionKind::StringScalarRead { source, .. } => {
            let input = operand_type(program, function, source, errors, id, block);
            if !input.as_ref().is_some_and(|ty| {
                matches!(ty, Type::String)
                    || matches!(ty, Type::Reference { inner, .. } if **inner == Type::String)
            }) || source.mode != UseMode::Read
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "String operation must read a String or String reference",
                );
            }
            if let InstructionKind::StringIsCharBoundary { offset, .. }
            | InstructionKind::StringByteAt { offset, .. }
            | InstructionKind::StringScalarAt { offset, .. }
            | InstructionKind::StringScalarRead { offset, .. } = &instruction.kind
            {
                if operand_type(program, function, offset, errors, id, block)
                    != Some(Type::Primitive(Primitive::U32))
                    || offset.mode != UseMode::Read
                {
                    push(errors, id, Some(block), "String offset must be read as u32");
                }
            }
            let valid_result = match &instruction.kind {
                kind @ (InstructionKind::StringByteAt { .. }
                | InstructionKind::StringScalarAt { .. }) => {
                    let (name, payload) = if matches!(kind, InstructionKind::StringByteAt { .. }) {
                        ("u8?", Primitive::U8)
                    } else {
                        ("u32?", Primitive::U32)
                    };
                    matches!(out, Some(Type::Enum(id))
                        if program.types.get(id.0 as usize).is_some_and(|ty| ty.is_scalar_option(name, payload)))
                }
                InstructionKind::StringIsCharBoundary { .. } => {
                    out == Some(&Type::Primitive(Primitive::Bool))
                }
                InstructionKind::StringScalarRead { width, .. } => {
                    out == Some(&Type::Primitive(if *width {
                        Primitive::U32
                    } else {
                        Primitive::Char
                    }))
                }
                _ => out == Some(&Type::Primitive(Primitive::U32)),
            };
            if !valid_result {
                push(
                    errors,
                    id,
                    Some(block),
                    "String operation has the wrong output type",
                );
            }
        }
        InstructionKind::Copy { source } => {
            let input = operand_type(program, function, source, errors, id, block);
            if out.is_none() {
                push(errors, id, Some(block), "copy requires an output value");
            }
            if source.mode != UseMode::Read {
                push(errors, id, Some(block), "copy must only read its source");
            }
            match &input {
                Some(Type::Primitive(Primitive::Unit)) | None => {
                    if input.is_some() {
                        push(
                            errors,
                            id,
                            Some(block),
                            "copy is available only for primitive values",
                        );
                    }
                }
                Some(Type::Primitive(_)) => {
                    if out.is_some_and(|output| Some(output) != input.as_ref()) {
                        push(
                            errors,
                            id,
                            Some(block),
                            "copy output type differs from source type",
                        );
                    }
                }
                Some(_) => push(
                    errors,
                    id,
                    Some(block),
                    "copy is available only for primitive values",
                ),
            }
        }
        InstructionKind::Borrow { owner, access, .. } => {
            let actual = operand_type(program, function, owner, errors, id, block);
            if instruction.output.is_none() {
                push(
                    errors,
                    id,
                    Some(block),
                    "borrow requires an output reference",
                );
            }
            let expected_mode = use_mode_for_access(*access);
            if expected_mode.is_none() || owner.mode != expected_mode.unwrap() {
                push(
                    errors,
                    id,
                    Some(block),
                    "borrow operand mode does not match requested access",
                );
            }
            let borrowed_type = actual.and_then(|actual| match actual {
                Type::Reference {
                    access: owner_access,
                    inner,
                } => {
                    let permitted = match access {
                        Access::Owned => false,
                        Access::Borrow => {
                            matches!(owner_access, Access::Borrow | Access::Share)
                        }
                        Access::Share => owner_access == Access::Share,
                    };
                    if !permitted {
                        push(
                            errors,
                            id,
                            Some(block),
                            "borrow cannot strengthen reference access",
                        );
                    }
                    Some(*inner)
                }
                Type::List(_)
                    if matches!(access, Access::Borrow | Access::Share)
                        && matches!(owner.source, Source::Local(_)) =>
                {
                    Some(actual)
                }
                Type::Primitive(_)
                | Type::String
                | Type::Array { .. }
                | Type::Struct(_)
                | Type::Enum(_)
                    if *access != Access::Owned =>
                {
                    Some(actual)
                }
                _ => {
                    push(
                        errors,
                        id,
                        Some(block),
                        "borrow source must be a primitive, array or struct owner or a reference",
                    );
                    None
                }
            });
            if let (Some(inner), Some(output)) = (borrowed_type, out) {
                let expected = Type::Reference {
                    access: *access,
                    inner: Box::new(inner),
                };
                if output != &expected {
                    push(
                        errors,
                        id,
                        Some(block),
                        "borrow output type is incompatible",
                    );
                }
            }
        }
        InstructionKind::ArrayNew { init } => {
            let operand_types = match init {
                ArrayInit::Elements(elements) => elements
                    .iter()
                    .map(|operand| {
                        let actual = operand_type(program, function, operand, errors, id, block);
                        if operand.mode != UseMode::Consume {
                            push(
                                errors,
                                id,
                                Some(block),
                                "array element operand must be consumed",
                            );
                        }
                        actual
                    })
                    .collect::<Vec<_>>(),
                ArrayInit::Zeroed => Vec::new(),
            };
            match out {
                None => push(
                    errors,
                    id,
                    Some(block),
                    "array creation requires an output value",
                ),
                Some(Type::Array { element, len }) => match init {
                    ArrayInit::Elements(elements) => {
                        if elements.len() != *len as usize {
                            push(
                                errors,
                                id,
                                Some(block),
                                "array literal length differs from output array length",
                            );
                        }
                        if operand_types
                            .iter()
                            .flatten()
                            .any(|actual| actual != element.as_ref())
                        {
                            push(
                                errors,
                                id,
                                Some(block),
                                "array element type differs from output array element type",
                            );
                        }
                    }
                    ArrayInit::Zeroed => {}
                },
                Some(_) => push(
                    errors,
                    id,
                    Some(block),
                    "array creation output must have an array type",
                ),
            }
        }
        InstructionKind::ElementAddr {
            base,
            index,
            access,
            ..
        } => {
            let actual = operand_type(program, function, base, errors, id, block);
            let index_type = operand_type(program, function, index, errors, id, block);
            if instruction.output.is_none() {
                push(
                    errors,
                    id,
                    Some(block),
                    "element address requires an output reference",
                );
            }
            let expected_mode = use_mode_for_access(*access);
            if expected_mode.is_none() || base.mode != expected_mode.unwrap() {
                push(
                    errors,
                    id,
                    Some(block),
                    "element address base mode does not match requested access",
                );
            }
            if index.mode != UseMode::Read {
                push(
                    errors,
                    id,
                    Some(block),
                    "element address index must use Read mode",
                );
            }
            if index_type.is_some_and(|ty| !is_integer(&ty)) {
                push(
                    errors,
                    id,
                    Some(block),
                    "element address index must be an integer",
                );
            }
            let element = actual.and_then(|actual| match actual {
                Type::Array { element, .. } | Type::List(element) if *access != Access::Owned => {
                    Some(*element)
                }
                Type::Reference {
                    access: owner_access,
                    inner,
                } => {
                    let permitted = match access {
                        Access::Owned => false,
                        Access::Borrow => {
                            matches!(owner_access, Access::Borrow | Access::Share)
                        }
                        Access::Share => owner_access == Access::Share,
                    };
                    if !permitted {
                        push(
                            errors,
                            id,
                            Some(block),
                            "element address cannot strengthen reference access",
                        );
                    }
                    match *inner {
                        Type::Array { element, .. } | Type::List(element) => Some(*element),
                        _ => {
                            push(
                                errors,
                                id,
                                Some(block),
                                "element address base must be an array owner or array reference",
                            );
                            None
                        }
                    }
                }
                _ => {
                    push(
                        errors,
                        id,
                        Some(block),
                        "element address base must be an array owner or array reference",
                    );
                    None
                }
            });
            if let (Some(element), Some(output)) = (element, out) {
                let expected = Type::Reference {
                    access: *access,
                    inner: Box::new(element),
                };
                if output != &expected {
                    push(
                        errors,
                        id,
                        Some(block),
                        "element address output type is incompatible",
                    );
                }
            }
        }
        InstructionKind::StructNew { ty, fields } => {
            let operand_types = fields
                .iter()
                .map(|operand| {
                    let actual = operand_type(program, function, operand, errors, id, block);
                    if operand.mode != UseMode::Consume {
                        push(
                            errors,
                            id,
                            Some(block),
                            "struct field operand must be consumed",
                        );
                    }
                    actual
                })
                .collect::<Vec<_>>();
            if out.is_none() {
                push(
                    errors,
                    id,
                    Some(block),
                    "struct creation requires an output value",
                );
            }
            if out.is_some_and(|output| output != &Type::Struct(*ty)) {
                push(
                    errors,
                    id,
                    Some(block),
                    "struct creation output must have the created struct type",
                );
            }
            match program.types.get(ty.0 as usize) {
                None => push(
                    errors,
                    id,
                    Some(block),
                    format!("struct type {:?} is out of range", ty),
                ),
                Some(TypeDef {
                    kind: TypeDefKind::Enum { .. },
                    ..
                }) => push(
                    errors,
                    id,
                    Some(block),
                    format!("struct creation names enum type {:?}", ty),
                ),
                Some(TypeDef {
                    kind: TypeDefKind::Struct { fields: declared },
                    ..
                }) => {
                    if declared.len() != fields.len() {
                        push(
                            errors,
                            id,
                            Some(block),
                            "struct creation operand count differs from the field count",
                        );
                    }
                    if operand_types
                        .iter()
                        .zip(declared)
                        .any(|(actual, field)| actual.as_ref().is_some_and(|a| a != &field.ty))
                    {
                        push(
                            errors,
                            id,
                            Some(block),
                            "struct field operand type differs from the declared field type",
                        );
                    }
                }
            }
        }
        InstructionKind::EnumNew {
            ty,
            variant,
            payload,
        } => {
            let operand_types = payload
                .iter()
                .map(|operand| {
                    let actual = operand_type(program, function, operand, errors, id, block);
                    if operand.mode != UseMode::Consume {
                        push(
                            errors,
                            id,
                            Some(block),
                            "enum payload operand must be consumed",
                        );
                    }
                    actual
                })
                .collect::<Vec<_>>();
            if out.is_none() {
                push(
                    errors,
                    id,
                    Some(block),
                    "enum creation requires an output value",
                );
            }
            if out.is_some_and(|output| output != &Type::Enum(*ty)) {
                push(
                    errors,
                    id,
                    Some(block),
                    "enum creation output must have the created enum type",
                );
            }
            match program.types.get(ty.0 as usize) {
                None => push(
                    errors,
                    id,
                    Some(block),
                    format!("enum type {:?} is out of range", ty),
                ),
                Some(TypeDef {
                    kind: TypeDefKind::Struct { .. },
                    ..
                }) => push(
                    errors,
                    id,
                    Some(block),
                    format!("enum creation names struct type {:?}", ty),
                ),
                Some(TypeDef {
                    kind: TypeDefKind::Enum { variants },
                    ..
                }) => match variants.get(*variant as usize) {
                    None => push(
                        errors,
                        id,
                        Some(block),
                        format!("variant index {variant} is out of range"),
                    ),
                    Some(declared) => {
                        if declared.payload.len() != payload.len() {
                            push(
                                errors,
                                id,
                                Some(block),
                                "enum creation operand count differs from the variant's payload",
                            );
                        }
                        if operand_types
                            .iter()
                            .zip(&declared.payload)
                            .any(|(actual, ty)| actual.as_ref().is_some_and(|a| a != ty))
                        {
                            push(
                                errors,
                                id,
                                Some(block),
                                "enum payload operand type differs from the declared payload type",
                            );
                        }
                    }
                },
            }
        }
        InstructionKind::FieldAddr {
            base,
            field,
            access,
            ..
        } => {
            let actual = operand_type(program, function, base, errors, id, block);
            if instruction.output.is_none() {
                push(
                    errors,
                    id,
                    Some(block),
                    "field address requires an output reference",
                );
            }
            let expected_mode = use_mode_for_access(*access);
            if expected_mode.is_none() || base.mode != expected_mode.unwrap() {
                push(
                    errors,
                    id,
                    Some(block),
                    "field address base mode does not match requested access",
                );
            }
            // A struct owner, or a reference to a struct (a `borrow`/`share`
            // parameter or binding) whose access is at least the requested one.
            let struct_id = match actual {
                Some(Type::Struct(type_id)) if *access != Access::Owned => Some(type_id),
                Some(Type::Reference {
                    access: owner_access,
                    inner,
                }) if matches!(inner.as_ref(), Type::Struct(_)) => {
                    let permitted = match access {
                        Access::Owned => false,
                        Access::Borrow => matches!(owner_access, Access::Borrow | Access::Share),
                        Access::Share => owner_access == Access::Share,
                    };
                    if !permitted {
                        push(
                            errors,
                            id,
                            Some(block),
                            "field address cannot strengthen reference access",
                        );
                    }
                    match *inner {
                        Type::Struct(type_id) => Some(type_id),
                        _ => None,
                    }
                }
                Some(_) => {
                    push(
                        errors,
                        id,
                        Some(block),
                        "field address base must be a struct owner or struct reference",
                    );
                    None
                }
                None => None,
            };
            let field_type =
                struct_id.and_then(|type_id| match program.types.get(type_id.0 as usize) {
                    Some(TypeDef {
                        kind: TypeDefKind::Struct { fields },
                        ..
                    }) => match fields.get(*field as usize) {
                        Some(declared) => Some(declared.ty.clone()),
                        None => {
                            push(
                                errors,
                                id,
                                Some(block),
                                format!("field index {field} is out of range"),
                            );
                            None
                        }
                    },
                    Some(TypeDef {
                        kind: TypeDefKind::Enum { .. },
                        ..
                    }) => {
                        push(
                            errors,
                            id,
                            Some(block),
                            format!("struct type {:?} names an enum", type_id),
                        );
                        None
                    }
                    None => {
                        push(
                            errors,
                            id,
                            Some(block),
                            format!("struct type {:?} is out of range", type_id),
                        );
                        None
                    }
                });
            if let (Some(field_type), Some(output)) = (field_type, out) {
                let expected = Type::Reference {
                    access: *access,
                    inner: Box::new(field_type),
                };
                if output != &expected {
                    push(
                        errors,
                        id,
                        Some(block),
                        "field address output type is incompatible",
                    );
                }
            }
        }
        InstructionKind::VariantAddr {
            base,
            variant,
            field,
            access,
            ..
        } => {
            let actual = operand_type(program, function, base, errors, id, block);
            if instruction.output.is_none() {
                push(
                    errors,
                    id,
                    Some(block),
                    "variant address requires an output reference",
                );
            }
            let expected_mode = use_mode_for_access(*access);
            if expected_mode.is_none() || base.mode != expected_mode.unwrap() {
                push(
                    errors,
                    id,
                    Some(block),
                    "variant address base mode does not match requested access",
                );
            }
            let enum_id = match actual {
                Some(Type::Enum(type_id)) if *access != Access::Owned => Some(type_id),
                Some(Type::Reference {
                    access: owner_access,
                    inner,
                }) if matches!(inner.as_ref(), Type::Enum(_)) => {
                    let permitted = match access {
                        Access::Owned => false,
                        Access::Borrow => matches!(owner_access, Access::Borrow | Access::Share),
                        Access::Share => owner_access == Access::Share,
                    };
                    if !permitted {
                        push(
                            errors,
                            id,
                            Some(block),
                            "variant address cannot strengthen reference access",
                        );
                    }
                    match *inner {
                        Type::Enum(type_id) => Some(type_id),
                        _ => None,
                    }
                }
                Some(_) => {
                    push(
                        errors,
                        id,
                        Some(block),
                        "variant address base must be an enum owner or enum reference",
                    );
                    None
                }
                None => None,
            };
            let payload_type =
                enum_id.and_then(|type_id| match program.types.get(type_id.0 as usize) {
                    Some(TypeDef {
                        kind: TypeDefKind::Enum { variants },
                        ..
                    }) => match variants.get(*variant as usize) {
                        None => {
                            push(
                                errors,
                                id,
                                Some(block),
                                format!("variant index {variant} is out of range"),
                            );
                            None
                        }
                        Some(declared) => match declared.payload.get(*field as usize) {
                            None => {
                                push(
                                    errors,
                                    id,
                                    Some(block),
                                    format!("payload index {field} is out of range"),
                                );
                                None
                            }
                            Some(ty) => Some(ty.clone()),
                        },
                    },
                    _ => {
                        push(
                            errors,
                            id,
                            Some(block),
                            format!("enum type {:?} is out of range or names a struct", type_id),
                        );
                        None
                    }
                });
            // `string ! E` entry-style results keep requiring a consuming match;
            // other enums may bind a String payload in place as a read-only
            // reference (in-place `match` of an element place, E1a).
            if payload_type == Some(Type::String)
                && enum_id
                    .and_then(|type_id| program.types.get(type_id.0 as usize))
                    .is_some_and(|definition| {
                        definition.entry_outcome == Some(EntryOutcome::Result)
                    })
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "String enum payloads require a consuming match",
                );
            }
            if let (Some(payload_type), Some(output)) = (payload_type, out) {
                let expected = Type::Reference {
                    access: *access,
                    inner: Box::new(payload_type),
                };
                if output != &expected {
                    push(
                        errors,
                        id,
                        Some(block),
                        "variant address output type is incompatible",
                    );
                }
            }
        }
        InstructionKind::Extract { base, field } => {
            let actual = operand_type(program, function, base, errors, id, block);
            if base.mode == UseMode::Borrow || base.mode == UseMode::Share {
                push(
                    errors,
                    id,
                    Some(block),
                    "field extraction base must be read or consumed",
                );
            }
            let field_type = match actual {
                Some(Type::Struct(type_id)) => match program.types.get(type_id.0 as usize) {
                    Some(TypeDef {
                        kind: TypeDefKind::Struct { fields },
                        ..
                    }) => match fields.get(*field as usize) {
                        Some(declared) => Some(declared.ty.clone()),
                        None => {
                            push(
                                errors,
                                id,
                                Some(block),
                                format!("field index {field} is out of range"),
                            );
                            None
                        }
                    },
                    Some(TypeDef {
                        kind: TypeDefKind::Enum { .. },
                        ..
                    }) => {
                        push(
                            errors,
                            id,
                            Some(block),
                            format!("struct type {:?} names an enum", type_id),
                        );
                        None
                    }
                    None => {
                        push(
                            errors,
                            id,
                            Some(block),
                            format!("struct type {:?} is out of range", type_id),
                        );
                        None
                    }
                },
                Some(_) => {
                    push(
                        errors,
                        id,
                        Some(block),
                        "field extraction base must be a struct owner",
                    );
                    None
                }
                None => None,
            };
            match (out, field_type) {
                (None, _) => push(
                    errors,
                    id,
                    Some(block),
                    "field extraction requires an output value",
                ),
                (Some(output), Some(expected)) if output != &expected => push(
                    errors,
                    id,
                    Some(block),
                    "field extraction output differs from the field type",
                ),
                _ => {}
            }
        }
        InstructionKind::EnumTag { base } => {
            let actual = operand_type(program, function, base, errors, id, block);
            let enum_type = match (&actual, base.mode) {
                (Some(Type::Enum(type_id)), UseMode::Read) => Some(*type_id),
                (Some(Type::Reference { access, inner }), mode)
                    if matches!(inner.as_ref(), Type::Enum(_))
                        && (use_mode_for_access(*access) == Some(mode)
                            || mode == UseMode::Borrow) =>
                {
                    match inner.as_ref() {
                        Type::Enum(type_id) => Some(*type_id),
                        _ => None,
                    }
                }
                (None, _) => None,
                _ => {
                    push(
                        errors,
                        id,
                        Some(block),
                        "enum tag base must be an enum owner read, or a reference to an enum",
                    );
                    None
                }
            };
            if let Some(type_id) = enum_type {
                if !matches!(
                    program.types.get(type_id.0 as usize),
                    Some(TypeDef {
                        kind: TypeDefKind::Enum { .. },
                        ..
                    })
                ) {
                    push(
                        errors,
                        id,
                        Some(block),
                        format!("enum tag type {:?} does not name an enum", type_id),
                    );
                }
            }
            if out != Some(&Type::Primitive(Primitive::U32)) {
                push(errors, id, Some(block), "enum tag output must be u32");
            }
        }
        InstructionKind::VariantExtract {
            base,
            variant,
            field,
        } => {
            let actual = operand_type(program, function, base, errors, id, block);
            if base.mode == UseMode::Borrow || base.mode == UseMode::Share {
                push(
                    errors,
                    id,
                    Some(block),
                    "variant extraction base must be read or consumed",
                );
            }
            let payload_type = match actual {
                Some(Type::Enum(type_id)) => match program.types.get(type_id.0 as usize) {
                    Some(TypeDef {
                        kind: TypeDefKind::Enum { variants },
                        ..
                    }) => match variants.get(*variant as usize) {
                        None => {
                            push(
                                errors,
                                id,
                                Some(block),
                                format!("variant index {variant} is out of range"),
                            );
                            None
                        }
                        Some(declared) => match declared.payload.get(*field as usize) {
                            None => {
                                push(
                                    errors,
                                    id,
                                    Some(block),
                                    format!("payload index {field} is out of range"),
                                );
                                None
                            }
                            Some(ty) => Some(ty.clone()),
                        },
                    },
                    _ => {
                        push(
                            errors,
                            id,
                            Some(block),
                            format!("enum type {:?} is out of range or names a struct", type_id),
                        );
                        None
                    }
                },
                Some(_) => {
                    push(
                        errors,
                        id,
                        Some(block),
                        "variant extraction base must be an enum owner",
                    );
                    None
                }
                None => None,
            };
            if matches!(payload_type, Some(Type::Reference { .. })) && base.mode != UseMode::Consume
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "extracting a borrow Option payload must consume the wrapper",
                );
            }
            if payload_type == Some(Type::String) && base.mode != UseMode::Consume {
                push(
                    errors,
                    id,
                    Some(block),
                    "String enum payloads require a consuming match",
                );
            }
            match (out, payload_type) {
                (None, _) => push(
                    errors,
                    id,
                    Some(block),
                    "variant extraction requires an output value",
                ),
                (Some(output), Some(expected)) if output != &expected => push(
                    errors,
                    id,
                    Some(block),
                    "variant extraction output differs from the payload type",
                ),
                _ => {}
            }
        }
        InstructionKind::Load { reference } => {
            let actual = operand_type(program, function, reference, errors, id, block);
            if instruction.output.is_none() {
                push(errors, id, Some(block), "load requires an output value");
            }
            match actual {
                Some(Type::Reference { access, inner }) => {
                    let expected_mode = use_mode_for_access(access);
                    if expected_mode.is_none() || reference.mode != expected_mode.unwrap() {
                        push(
                            errors,
                            id,
                            Some(block),
                            "load operand mode does not match reference access",
                        );
                    }
                    if matches!(inner.as_ref(), Type::List(_)) {
                        push(
                            errors,
                            id,
                            Some(block),
                            "whole Lists cannot be loaded through a borrow",
                        );
                    }
                    if matches!(inner.as_ref(), Type::Array { .. }) {
                        push(
                            errors,
                            id,
                            Some(block),
                            "load of a whole array is not supported; read elements instead",
                        );
                    }
                    if matches!(inner.as_ref(), Type::Struct(_)) {
                        push(
                            errors,
                            id,
                            Some(block),
                            "load of a whole struct is not supported; read fields instead",
                        );
                    }
                    if matches!(inner.as_ref(), Type::Enum(_)) {
                        push(
                            errors,
                            id,
                            Some(block),
                            "load of a whole enum is not supported",
                        );
                    }
                    if out.is_some_and(|output| output != inner.as_ref()) {
                        push(
                            errors,
                            id,
                            Some(block),
                            "load output type differs from referent",
                        );
                    }
                }
                Some(_) => push(errors, id, Some(block), "load source is not a reference"),
                None => {}
            }
        }
        InstructionKind::SwapPlaces { left, right } => {
            if instruction.output.is_some() {
                push(
                    errors,
                    id,
                    Some(block),
                    "swap cannot define an output value",
                );
            }
            let left_ty = operand_type(program, function, left, errors, id, block);
            let right_ty = operand_type(program, function, right, errors, id, block);
            match (left_ty, right_ty) {
                (
                    Some(Type::Reference {
                        access: Access::Share,
                        inner: left_inner,
                    }),
                    Some(Type::Reference {
                        access: Access::Share,
                        inner: right_inner,
                    }),
                ) => {
                    if left_inner != right_inner {
                        push(errors, id, Some(block), "swap operands differ in type");
                    }
                    if left.mode != UseMode::Share || right.mode != UseMode::Share {
                        push(errors, id, Some(block), "swap requires Share operand mode");
                    }
                }
                (None, _) | (_, None) => {}
                _ => push(
                    errors,
                    id,
                    Some(block),
                    "swap requires two exclusive Share references",
                ),
            }
        }
        InstructionKind::ReplaceStringField {
            target,
            field,
            value,
        } => {
            let actual = operand_type(program, function, value, errors, id, block);
            let destination = function.locals.get(target.0 as usize).is_some_and(|local| {
                let (ty, allowed) = match &local.ty {
                    Type::Struct(ty) => (
                        *ty,
                        local.mutable && !function.parameter_locals.contains(target),
                    ),
                    Type::Reference {
                        access: Access::Share,
                        inner,
                    } if function.parameter_locals.contains(target) => {
                        let Type::Struct(ty) = inner.as_ref() else {
                            return false;
                        };
                        let Some(position) = function
                            .parameter_locals
                            .iter()
                            .position(|parameter| parameter == target)
                        else {
                            return false;
                        };
                        (*ty, function.signature.parameters[position].access == Access::Share)
                    }
                    _ => return false,
                };
                allowed
                    && program.types.get(ty.0 as usize).is_some_and(|ty| {
                        matches!(&ty.kind, TypeDefKind::Struct { fields }
                            if fields.get(*field as usize).is_some_and(|field| field.ty == Type::String))
                    })
            });
            if instruction.output.is_some()
                || !destination
                || actual != Some(Type::String)
                || value.mode != UseMode::Consume
                || !matches!(value.source, Source::Local(_))
            {
                push(errors, id, Some(block),
                    "String field replacement requires a mutable local or shared struct parameter and a consumed String local");
            }
        }
        InstructionKind::Store { reference, value } => {
            if instruction.output.is_some() {
                push(
                    errors,
                    id,
                    Some(block),
                    "store cannot define an output value",
                );
            }
            let actual_reference = operand_type(program, function, reference, errors, id, block);
            let actual_value = operand_type(program, function, value, errors, id, block);
            match actual_reference {
                Some(Type::Reference {
                    access: Access::Share,
                    inner,
                }) => {
                    if matches!(inner.as_ref(), Type::List(_))
                        && scoped_string::list_share_destination(function, reference, &inner)
                            .is_none()
                    {
                        push(
                            errors,
                            id,
                            Some(block),
                            "whole List replacement requires a mutable share local or direct share parameter",
                        );
                    }
                    if reference.mode != UseMode::Share {
                        push(errors, id, Some(block), "store requires Share operand mode");
                    }
                    if actual_value.as_ref().is_some_and(|ty| ty != inner.as_ref()) {
                        push(
                            errors,
                            id,
                            Some(block),
                            "store value type differs from referent",
                        );
                    }
                    if value.mode != UseMode::Consume {
                        push(errors, id, Some(block), "store value must be consumed");
                    }
                }
                Some(Type::Reference { .. }) => push(
                    errors,
                    id,
                    Some(block),
                    "store requires an exclusive Share reference",
                ),
                Some(_) => push(errors, id, Some(block), "store target is not a reference"),
                None => {}
            }
        }
        InstructionKind::Unary { op, operand } => {
            let input = operand_type(program, function, operand, errors, id, block);
            if out.is_none() {
                push(
                    errors,
                    id,
                    Some(block),
                    "unary instruction requires an output value",
                );
            }
            if let (Some(input), Some(output)) = (input, out) {
                let okay = match op {
                    UnaryOp::Not => input == Type::Primitive(Primitive::Bool) && output == &input,
                    UnaryOp::Plus | UnaryOp::Negate => is_numeric(&input) && output == &input,
                };
                if !okay {
                    push(
                        errors,
                        id,
                        Some(block),
                        "unary operand/output types are incompatible",
                    );
                }
            }
        }
        InstructionKind::Cast {
            value,
            source,
            target,
        } => {
            let input = operand_type(program, function, value, errors, id, block);
            let expected = Type::Primitive(*target);
            let numeric = |primitive: Primitive| {
                matches!(
                    primitive,
                    Primitive::I8
                        | Primitive::I16
                        | Primitive::I32
                        | Primitive::I64
                        | Primitive::U8
                        | Primitive::U16
                        | Primitive::U32
                        | Primitive::U64
                        | Primitive::F32
                        | Primitive::F64
                )
            };
            if instruction.output.is_none()
                || !numeric(*source)
                || !numeric(*target)
                || input != Some(Type::Primitive(*source))
                || out != Some(&expected)
                || value.mode != UseMode::Read
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "numeric cast source, target, or operand type is invalid",
                );
            }
        }
        InstructionKind::Binary { op, left, right } => {
            if matches!(op, BinaryOp::And | BinaryOp::Or) {
                push(
                    errors,
                    id,
                    Some(block),
                    "logical and/or must be represented with control flow to preserve short-circuit evaluation",
                );
            }
            let lhs = operand_type(program, function, left, errors, id, block);
            let rhs = operand_type(program, function, right, errors, id, block);
            if out.is_none() {
                push(
                    errors,
                    id,
                    Some(block),
                    "binary instruction requires an output value",
                );
            }
            if let (Some(lhs), Some(rhs), Some(output)) = (lhs, rhs, out) {
                let both = lhs == rhs;
                let bool_ty = Type::Primitive(Primitive::Bool);
                let okay = match op {
                    BinaryOp::Add | BinaryOp::Subtract | BinaryOp::Multiply | BinaryOp::Divide => {
                        both && is_numeric(&lhs) && output == &lhs
                    }
                    BinaryOp::WrappingAdd
                    | BinaryOp::WrappingMultiply
                    | BinaryOp::WrappingSubtract
                    | BinaryOp::SaturatingAdd
                    | BinaryOp::SaturatingSubtract
                    | BinaryOp::SaturatingMultiply
                    | BinaryOp::BitwiseAnd
                    | BinaryOp::BitwiseXor
                    | BinaryOp::BitwiseOr => both && is_integer(&lhs) && output == &lhs,
                    BinaryOp::ShiftLeft
                    | BinaryOp::ShiftRight
                    | BinaryOp::WrappingShiftLeft
                    | BinaryOp::WrappingShiftRight => {
                        is_integer(&lhs) && rhs == Type::Primitive(Primitive::U32) && output == &lhs
                    }
                    BinaryOp::CheckedShiftLeft | BinaryOp::CheckedShiftRight => {
                        is_integer(&lhs)
                            && rhs == Type::Primitive(Primitive::U32)
                            && is_checked_option(program, &lhs, output)
                    }
                    BinaryOp::CheckedAdd
                    | BinaryOp::CheckedSubtract
                    | BinaryOp::CheckedMultiply
                    | BinaryOp::CheckedDivide
                    | BinaryOp::CheckedRemainder => {
                        both && is_integer(&lhs) && is_checked_option(program, &lhs, output)
                    }
                    BinaryOp::Remainder => both && is_integer(&lhs) && output == &lhs,
                    BinaryOp::Less
                    | BinaryOp::LessEqual
                    | BinaryOp::Greater
                    | BinaryOp::GreaterEqual => both && is_numeric(&lhs) && output == &bool_ty,
                    BinaryOp::Equal | BinaryOp::NotEqual => {
                        both && (is_numeric(&lhs)
                            || lhs == bool_ty
                            || lhs == Type::Primitive(Primitive::Char))
                            && output == &bool_ty
                    }
                    BinaryOp::And | BinaryOp::Or => both && lhs == bool_ty && output == &bool_ty,
                };
                if !okay {
                    push(
                        errors,
                        id,
                        Some(block),
                        "binary operand/output types are incompatible",
                    );
                }
            }
        }
        InstructionKind::Assign {
            target,
            value,
            initialize,
        } => {
            if instruction.output.is_some() {
                push(
                    errors,
                    id,
                    Some(block),
                    "assignment cannot define an output value",
                );
            }
            let actual = operand_type(program, function, value, errors, id, block);
            if actual
                .as_ref()
                .is_some_and(|ty| program.is_borrow_option(ty))
                && (!initialize || value.mode != UseMode::Consume)
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "borrow Option assignment requires a consuming initialization",
                );
            }
            if matches!(actual, Some(Type::List(_)))
                && (value.mode != UseMode::Consume
                    || !initialize
                        && function
                            .locals
                            .get(target.0 as usize)
                            .is_some_and(|local| !local.mutable))
            {
                push(
                    errors,
                    id,
                    Some(block),
                    "List assignment requires a consuming move and a mutable target for replacement",
                );
            }
            match function.locals.get(target.0 as usize) {
                None => push(
                    errors,
                    id,
                    Some(block),
                    format!("assignment target {:?} is out of range", target),
                ),
                Some(local) if actual.as_ref().is_some_and(|ty| ty != &local.ty) => push(
                    errors,
                    id,
                    Some(block),
                    "assignment value type differs from local type",
                ),
                _ => {}
            }
        }
        InstructionKind::Call { callee, arguments } => {
            let callee_type = operand_type(program, function, callee, errors, id, block);
            let argument_types = arguments
                .iter()
                .map(|arg| operand_type(program, function, arg, errors, id, block))
                .collect::<Vec<_>>();
            if out.is_none() {
                push(
                    errors,
                    id,
                    Some(block),
                    "call requires an output value, including Unit calls",
                );
            }
            match callee_type {
                Some(Type::Function(signature)) => {
                    if matches!(signature.result.as_ref(), Type::List(_))
                        && !matches!(callee.source, Source::Function(_))
                    {
                        push(
                            errors,
                            id,
                            Some(block),
                            "List results require a direct internal call",
                        );
                    }

                    if signature.parameters.len() != arguments.len() {
                        push(
                            errors,
                            id,
                            Some(block),
                            "call argument count differs from signature",
                        );
                    }
                    for ((arg, actual), parameter) in arguments
                        .iter()
                        .zip(argument_types)
                        .zip(&signature.parameters)
                    {
                        if matches!(parameter.ty, Type::List(_))
                            && !matches!(callee.source, Source::Function(_))
                        {
                            push(
                                errors,
                                id,
                                Some(block),
                                "List arguments require a direct internal call",
                            );
                        }
                        if matches!(parameter.ty, Type::List(_))
                            && parameter.access == Access::Owned
                            && !matches!(arg.source, Source::Local(_))
                        {
                            push(
                                errors,
                                id,
                                Some(block),
                                "owned List arguments require a named whole local",
                            );
                        }
                        // Internal direct calls pass the original reference address.
                        let pointee_matches = |inner: &Type| {
                            inner == &parameter.ty
                                || matches!(callee.source, Source::Function(_))
                                    && program.has_error_ancestor(inner, &parameter.ty)
                        };
                        let type_matches = actual.as_ref().is_some_and(|actual| {
                            match (parameter.access, actual) {
                                (Access::Owned, actual) => actual == &parameter.ty,
                                (Access::Borrow, Type::Reference { access, inner }) => {
                                    matches!(access, Access::Borrow | Access::Share)
                                        && pointee_matches(inner)
                                }
                                (
                                    Access::Share,
                                    Type::Reference {
                                        access: Access::Share,
                                        inner,
                                    },
                                ) => pointee_matches(inner),
                                _ => false,
                            }
                        });
                        if !type_matches {
                            push(
                                errors,
                                id,
                                Some(block),
                                "call argument type or reference access differs from parameter",
                            );
                        }
                        let expected_mode = match parameter.access {
                            Access::Owned => UseMode::Consume,
                            Access::Borrow => UseMode::Borrow,
                            Access::Share => UseMode::Share,
                        };
                        if arg.mode != expected_mode {
                            push(
                                errors,
                                id,
                                Some(block),
                                "call argument use mode differs from parameter access",
                            );
                        }
                    }
                    if out.is_some_and(|ty| ty != signature.result.as_ref()) {
                        push(
                            errors,
                            id,
                            Some(block),
                            "call result type differs from signature",
                        );
                    }
                }
                Some(_) => push(errors, id, Some(block), "call target is not a function"),
                None => {}
            }
        }
    }
}

fn validate_operand_escapes(
    program: &Program,
    function: &Function,
    id: FunctionId,
    heap_strings: &[HeapStrings],
    errors: &mut Vec<ValidationError>,
) {
    let mut read_only = vec![false; function.values.len()];
    for block in &function.blocks {
        for instruction in &block.instructions {
            if matches!(&instruction.kind, InstructionKind::Load { .. }) {
                if let Some(output) = instruction.output {
                    if let Some(slot) = read_only.get_mut(output.0 as usize) {
                        *slot = true;
                    }
                }
            }
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for block in &function.blocks {
            for instruction in &block.instructions {
                if let InstructionKind::Capture(operand) = &instruction.kind {
                    if operand_is_read_only(operand, &read_only) {
                        if let Some(output) = instruction.output {
                            if let Some(slot) = read_only.get_mut(output.0 as usize) {
                                if !*slot {
                                    *slot = true;
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
            for edge in outgoing_edges(&block.terminator.kind) {
                let Some(target) = function.blocks.get(edge.target.0 as usize) else {
                    continue;
                };
                for (argument, parameter) in edge.arguments.iter().zip(&target.parameters) {
                    if operand_is_read_only(argument, &read_only) {
                        if let Some(slot) = read_only.get_mut(parameter.0 as usize) {
                            if !*slot {
                                *slot = true;
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
    }

    let shares = scoped_string::share_borrows(function);
    for (index, block) in function.blocks.iter().enumerate() {
        let block_id = Some(BlockId(index as u32));
        let list_return = scoped_string::return_capture(block).filter(|(_, source)| {
            matches!(function.signature.result.as_ref(), Type::List(_))
                && function
                    .locals
                    .get(source.0 as usize)
                    .is_some_and(|local| &local.ty == function.signature.result.as_ref())
        });
        if matches!(function.signature.result.as_ref(), Type::List(_))
            && matches!(&block.terminator.kind, TerminatorKind::Return(_))
            && list_return.is_none()
        {
            push(
                errors,
                id,
                block_id,
                "List return requires a named whole local",
            );
        }
        for (position, instruction) in block.instructions.iter().enumerate() {
            if let InstructionKind::Capture(_) = &instruction.kind {
                if matches!(
                    output_type(function, instruction.output),
                    Some(Type::List(_))
                ) && !list_return.is_some_and(|(returned, _)| returned == position)
                    && !instruction.output.is_some_and(|output| {
                        // A List moved into an outer List element.
                        block.instructions[position + 1..].iter().any(|candidate| {
                            matches!(&candidate.kind, InstructionKind::ListPush { value, .. }
                                if value.source == Source::Value(output)
                                    && value.mode == UseMode::Consume)
                        })
                    })
                {
                    push(
                        errors,
                        id,
                        block_id,
                        "List moves currently require a new local binding or a direct return",
                    );
                }
            }

            if matches!(
                instruction.kind,
                InstructionKind::ValidateUtf8 {
                    construct_string: true,
                    ..
                }
            ) && !instruction
                .output
                .is_some_and(|value| heap_strings[id.0 as usize].approved_ok.contains(&value))
            {
                push(errors, id, Some(BlockId(index as u32)),
                    "UTF-8 String result must be returned directly or immediately matched with explicit Ok(value) and Err arms");
            }
            if let InstructionKind::Call { callee, arguments } = &instruction.kind {
                if let Source::Function(target) = callee.source {
                    let Some(facts) = heap_strings.get(target.0 as usize) else {
                        continue;
                    };
                    let result = program.functions[target.0 as usize]
                        .signature
                        .result
                        .as_ref();
                    if matches!(result, Type::List(_))
                        && scoped_string::call_binding(
                            program,
                            function,
                            &block.instructions[position..],
                            result,
                        )
                        .is_none()
                    {
                        push(
                            errors,
                            id,
                            block_id,
                            "List call result must be assigned directly to a whole List local, mutable share local, or direct share parameter",
                        );
                    }
                    if facts.returns_heap
                        && scoped_string::call_binding(
                            program,
                            function,
                            &block.instructions[position..],
                            result,
                        )
                        .is_none()
                        && !scoped_string::owned_aggregate_call_argument(
                            program, block, position, result,
                        )
                    {
                        let message = if matches!(result, Type::String) {
                            "heap String call result must be assigned directly to a whole String local"
                        } else {
                            "String-owning aggregate call result must be assigned directly to a whole local"
                        };
                        push(errors, id, block_id, message);
                    }
                    if facts.returns_heap_ok
                        && scoped_string::immediate_result_match(program, function, block, position)
                            .is_none()
                    {
                        push(errors, id, block_id,
                            "heap `string ! E` requires an immediate consuming match with explicit Ok(value) and Err arms");
                    }
                    for parameter in &facts.writes_heap {
                        if arguments
                            .get(*parameter)
                            .and_then(|arg| {
                                scoped_string::direct_share_owner(function, &shares, arg)
                            })
                            .is_none()
                        {
                            push(errors, id, block_id,
                                "heap String replacement requires a direct share of a whole mutable caller local");
                        }
                    }
                }
            }
        }
    }

    let heap_locals = &heap_strings[id.0 as usize].locals;
    let mut report = |block: BlockId, operand: &Operand, escape: bool, captures: bool| {
        if matches!(operand.source, Source::Local(local) if heap_locals.contains(&local))
            && (escape || captures || !matches!(operand.mode, UseMode::Read | UseMode::Borrow))
        {
            push(
                errors,
                id,
                Some(block),
                if matches!(operand.source, Source::Local(local) if matches!(function.locals[local.0 as usize].ty, Type::Struct(_)))
                {
                    "a struct owning a heap String can only move directly into a new local"
                } else if matches!(operand.source, Source::Local(local) if matches!(function.locals[local.0 as usize].ty, Type::Enum(_)))
                {
                    "an enum owning a heap String can only move to an owned destination"
                } else {
                    "heap String requires a whole String destination for moves and a checked loan for reference access"
                },
            );
        }
        if operand_is_read_only(operand, &read_only) && (escape || operand.mode != UseMode::Read) {
            push(
                errors,
                id,
                Some(block),
                "loaded reference value is read-only and cannot be consumed or escape its reference",
            );
        }
    };

    let mut borrowed_payload_extractions: Vec<BlockId> = Vec::new();
    for (index, block) in function.blocks.iter().enumerate() {
        let block_id = BlockId(index as u32);
        let return_capture = scoped_string::return_capture(block);
        let tuple_extractions =
            scoped_string::tuple_destructure_extractions(program, function, block);
        for (position, instruction) in block.instructions.iter().enumerate() {
            match &instruction.kind {
                InstructionKind::Capture(value) => {
                    let returns_owned_tuple = scoped_string::owns_string_aggregate(
                        program,
                        function.signature.result.as_ref(),
                    );
                    let feeds_owned_enum_payload = instruction.output.is_some_and(|output| {
                        block.instructions[position + 1..].iter().enumerate().any(|(offset, candidate)| {
                            let InstructionKind::EnumNew { ty, variant, payload } = &candidate.kind else {
                                return false;
                            };
                            (scoped_string::enum_binding(
                                function,
                                &block.instructions[position + 1 + offset..],
                            )
                            .is_some()
                                || matches!(block.terminator.kind,
                                    TerminatorKind::Return(Some(Operand {
                                        source: Source::Value(returned),
                                        mode: UseMode::Consume,
                                        ..
                                    })) if candidate.output == Some(returned)))
                                && payload.iter().enumerate().any(|(field, operand)| {
                                    operand.source == Source::Value(output)
                                        && operand.mode == UseMode::Consume
                                        && program.types.get(ty.0 as usize).is_some_and(|definition|
                                            matches!(&definition.kind, TypeDefKind::Enum { variants }
                                                if variants.get(*variant as usize).is_some_and(|item|
                                                    item.payload.get(field)
                                                        .is_some_and(|payload_ty| scoped_string::owns_string_storage(program, payload_ty)))))
                                })
                        })
                    });
                    let feeds_owned_call_argument = instruction.output.is_some_and(|output| {
                        let Source::Local(source) = value.source else {
                            return false;
                        };
                        let Some(source_ty) = function
                            .locals
                            .get(source.0 as usize)
                            .map(|local| &local.ty)
                        else {
                            return false;
                        };
                        block.instructions[position + 1..].iter().any(|candidate| {
                            let InstructionKind::Call {
                                callee:
                                    Operand {
                                        source: Source::Function(callee),
                                        ..
                                    },
                                arguments,
                            } = &candidate.kind
                            else {
                                return false;
                            };
                            let Some(target) = program.functions.get(callee.0 as usize) else {
                                return false;
                            };
                            arguments.iter().zip(&target.signature.parameters).any(
                                |(argument, parameter)| {
                                    argument.source == Source::Value(output)
                                        && argument.mode == UseMode::Consume
                                        && parameter.access == Access::Owned
                                        && parameter.ty == *source_ty
                                        && scoped_string::owns_string_aggregate(program, source_ty)
                                },
                            )
                        })
                    });
                    let feeds_owned_array_element = instruction.output.is_some_and(|output| {
                        let Source::Local(source) = value.source else {
                            return false;
                        };
                        let Some(source_ty) = function
                            .locals
                            .get(source.0 as usize)
                            .map(|local| &local.ty)
                        else {
                            return false;
                        };
                        block.instructions[position + 1..].iter().enumerate().any(
                            |(offset, candidate)| {
                                let InstructionKind::ArrayNew {
                                    init: ArrayInit::Elements(elements),
                                } = &candidate.kind
                                else {
                                    return false;
                                };
                                let destination = scoped_string::array_binding(
                                    function,
                                    &block.instructions[position + 1 + offset..],
                                )
                                .is_some()
                                    || matches!(&block.terminator.kind,
                                    TerminatorKind::Return(Some(Operand {
                                        source: Source::Value(returned),
                                        mode: UseMode::Consume,
                                        ..
                                    })) if candidate.output == Some(*returned));
                                destination
                                    && candidate
                                        .output
                                        .and_then(|id| function.values.get(id.0 as usize))
                                        .is_some_and(|ty| {
                                            matches!(ty, Type::Array { element, .. }
                                        if **element == *source_ty
                                            && scoped_string::owns_string_storage(program, element))
                                        })
                                    && elements.iter().any(|element| {
                                        element.source == Source::Value(output)
                                            && element.mode == UseMode::Consume
                                    })
                            },
                        )
                    });
                    let feeds_owned_list_push = instruction.output.is_some_and(|output| {
                        let Source::Local(source) = value.source else {
                            return false;
                        };
                        let Some(source_ty) = function
                            .locals
                            .get(source.0 as usize)
                            .map(|local| &local.ty)
                        else {
                            return false;
                        };
                        scoped_string::owns_string_storage(program, source_ty)
                            && block.instructions[position + 1..].iter().any(|candidate| {
                                matches!(&candidate.kind, InstructionKind::ListPush { target, value: pushed }
                                    if pushed.source == Source::Value(output)
                                        && pushed.mode == UseMode::Consume
                                        && function.locals.get(target.0 as usize).is_some_and(|list| {
                                            let list = match &list.ty {
                                                Type::Reference { inner, .. } => inner.as_ref(),
                                                other => other,
                                            };
                                            matches!(list, Type::List(element) if **element == *source_ty)
                                        }))
                            })
                    });
                    if !feeds_owned_enum_payload
                        && !feeds_owned_call_argument
                        && !feeds_owned_array_element
                        && !feeds_owned_list_push
                        && (!return_capture.is_some_and(|(returned, source)| {
                            returned == position && heap_locals.contains(&source)
                        }) || (*function.signature.result != Type::String
                            && !returns_owned_tuple))
                    {
                        report(block_id, value, false, true);
                    }
                }
                InstructionKind::Borrow {
                    owner,
                    access: Access::Share,
                    ..
                } if matches!(owner.source, Source::Local(local) if heap_locals.contains(&local)) =>
                    {}
                InstructionKind::Borrow { owner: value, .. }
                | InstructionKind::Load { reference: value } => {
                    report(block_id, value, false, false)
                }
                InstructionKind::ElementAddr {
                    base,
                    index,
                    access,
                    ..
                } => {
                    // A shared projection of a heap owner is a checked loan
                    // like a borrow; the loan checker orders it.
                    report(block_id, &projection_base(base, *access), false, false);
                    report(block_id, index, false, false);
                }
                InstructionKind::FieldAddr { base, access, .. }
                | InstructionKind::VariantAddr { base, access, .. } => {
                    report(block_id, &projection_base(base, *access), false, false)
                }
                InstructionKind::EnumTag { base } => report(block_id, base, false, false),
                InstructionKind::VariantExtract { base, variant, .. } => {
                    // A non-local base is a temporary. Extracting an owned
                    // String payload is only sound when that temporary owns
                    // its storage: not when it is loaded through a reference
                    // or read out of a field or array element.
                    if let Source::Value(base_value) = base.source {
                        let payload_owns_heap = function
                            .values
                            .get(base_value.0 as usize)
                            .is_some_and(|ty| {
                                scoped_string::enum_variant_owns_string_storage(
                                    program, ty, *variant,
                                )
                            });
                        if payload_owns_heap {
                            let defining = block.instructions[..position]
                                .iter()
                                .enumerate()
                                .find(|(_, candidate)| candidate.output == Some(base_value));
                            let owned_temporary = match defining {
                                Some((index, candidate)) => match &candidate.kind {
                                    InstructionKind::Load { .. } => false,
                                    InstructionKind::Extract { .. } => {
                                        tuple_extractions.contains_key(&index)
                                    }
                                    _ => true,
                                },
                                // Defined in another block: only block parameters
                                // and values the loan analysis marks are possible.
                                None => true,
                            };
                            if !owned_temporary || operand_is_read_only(base, &read_only) {
                                borrowed_payload_extractions.push(block_id);
                            }
                        }
                    }
                    let variant_owns_heap_string = match (&base.source, &instruction.kind) {
                        (Source::Local(local), InstructionKind::VariantExtract { variant, .. }) => {
                            function
                                .locals
                                .get(local.0 as usize)
                                .is_some_and(|binding| {
                                    scoped_string::enum_variant_owns_string_storage(
                                        program,
                                        &binding.ty,
                                        *variant,
                                    )
                                })
                        }
                        _ => false,
                    };
                    let extracted_owned_payload = match (base.source, &instruction.kind) {
                        (
                            Source::Local(local),
                            InstructionKind::VariantExtract {
                                variant: variant_index,
                                ..
                            },
                        ) => {
                            let enum_id =
                                function.locals.get(local.0 as usize).and_then(|binding| {
                                    if let Type::Enum(id) = &binding.ty {
                                        Some(*id)
                                    } else {
                                        None
                                    }
                                });
                            enum_id.is_some_and(|enum_id| program.types
                                .get(enum_id.0 as usize).is_some_and(|definition| {
                            matches!(&definition.kind, TypeDefKind::Enum { variants }
                                if variants.get(*variant_index as usize).is_some_and(|declared_variant| {
                                    declared_variant.payload.iter().enumerate().any(|(field, payload_ty)| {
                                        if !scoped_string::owns_string_storage(program, payload_ty) {
                                            return false;
                                        }
                                        block.instructions[..position].iter().enumerate().any(|(prior_position, prior)| {
                                            let InstructionKind::VariantExtract {
                                                base: prior_base,
                                                variant: prior_variant,
                                                field: prior_field,
                                            } = &prior.kind else {
                                                return false;
                                            };
                                            prior_base.source == Source::Local(local)
                                                && *prior_variant == *variant_index
                                                && *prior_field as usize == field
                                                && prior.output.is_some_and(|output| {
                                                    // Only statements after the prior extraction can consume it.
                                                    block.instructions[prior_position + 1..].iter().any(|next| matches!(
                                                        &next.kind,
                                                        InstructionKind::Assign {
                                                            value,
                                                            initialize: true,
                                                            ..
                                                        } if value.source == Source::Value(output)
                                                            && value.mode == UseMode::Consume
                                                    ))
                                                })
                                        })
                                    })
                                }))
                                }))
                        }
                        _ => false,
                    };
                    let final_extract_consumes_owner = base.mode == UseMode::Consume
                        || (matches!(base.source, Source::Local(local)
                        if block.instructions[position + 1..].iter().any(|later| {
                            matches!(&later.kind,
                                InstructionKind::VariantExtract { base: later_base, .. }
                                    if later_base.source == Source::Local(local)
                                        && later_base.mode == UseMode::Consume)
                        })));
                    // A non-owning variant contains no heap descriptor to
                    // transfer, even when its enum's other variants own one.
                    // Matching that branch therefore retires the enum shell
                    // without requiring a String destination.
                    let transferred = !variant_owns_heap_string
                        || extracted_owned_payload
                        || (final_extract_consumes_owner
                        && instruction.output.is_some_and(|output| {
                            function.values.get(output.0 as usize)
                                .is_some_and(|ty| scoped_string::owns_string_storage(program, ty))
                                && block.instructions[position + 1..].iter()
                                    .find(|next| !matches!(next.kind,
                                        InstructionKind::EndStringLocal { .. }
                                            | InstructionKind::EndListLocal { .. }
                                            | InstructionKind::EndStructLocal { .. }))
                                    .is_some_and(|next| matches!(&next.kind,
                                        InstructionKind::Assign { value, initialize: true, .. }
                                            if value.source == Source::Value(instruction.output.unwrap())
                                                && value.mode == UseMode::Consume))
                        }));
                    if !transferred {
                        report(block_id, base, false, false);
                    }
                }
                InstructionKind::Extract { base, .. } => {
                    if !tuple_extractions.contains_key(&position) {
                        report(block_id, base, true, false);
                    }
                }
                InstructionKind::StructNew { ty, fields } => {
                    let struct_fields = program.types.get(ty.0 as usize).and_then(|definition| {
                        match &definition.kind {
                            TypeDefKind::Struct { fields } => Some(fields),
                            TypeDefKind::Enum { .. } => None,
                        }
                    });
                    // Tuples and admitted nominal owners may hold owners moved in
                    // from named locals (nested structs, arrays of owners).
                    let enclosing_owner = scoped_string::is_string_owner_transport(
                        &program.types,
                        &Type::Struct(*ty),
                    ) || program
                        .types
                        .get(ty.0 as usize)
                        .is_some_and(|definition| definition.path.module.as_slice() == ["\0tuple"]);
                    for (index, field) in fields.iter().enumerate() {
                        let direct_string_move = field.mode == UseMode::Consume
                            && matches!(field.source, Source::Local(local)
                                if function.locals.get(local.0 as usize)
                                    .is_some_and(|local| local.ty == Type::String));
                        let nested_tuple_move = field.mode == UseMode::Consume
                            && struct_fields
                                .and_then(|fields| fields.get(index))
                                .is_some_and(|definition| {
                                    let mut element = &definition.ty;
                                    while let Type::Array { element: inner, .. } = element {
                                        element = inner;
                                    }
                                    let is_array = element != &definition.ty;
                                    matches!(element, Type::Struct(nested)
                                        if ((!is_array
                                            && scoped_string::tuple_owns_string(program, nested.0))
                                            || (enclosing_owner
                                                && !(is_array && program.types.get(nested.0 as usize).is_some_and(|d| d.path.module.as_slice() == ["\0tuple"]))
                                                && scoped_string::is_string_owner_transport(
                                                    &program.types,
                                                    element,
                                                )))
                                            && matches!(field.source, Source::Local(local)
                                                if function.locals.get(local.0 as usize)
                                                    .is_some_and(|local| local.ty == definition.ty)))
                                });
                        if !direct_string_move && !nested_tuple_move {
                            report(block_id, field, true, false);
                        }
                    }
                }
                InstructionKind::EnumNew { ty, payload, .. } => {
                    let is_heap_result_enum =
                        program.types.get(ty.0 as usize).is_some_and(|definition| {
                            definition.entry_outcome == Some(EntryOutcome::Result)
                        });
                    let owned_enum_destination =
                        scoped_string::enum_binding(function, &block.instructions[position..])
                            .is_some()
                            || instruction.output.is_some_and(|output| {
                                matches!(&block.terminator.kind,
                                TerminatorKind::Return(Some(Operand {
                                    source: Source::Value(returned),
                                    mode: UseMode::Consume,
                                    ..
                                })) if *returned == output)
                            });
                    if !instruction.output.is_some_and(|value| {
                        heap_strings[id.0 as usize].approved_ok.contains(&value)
                    }) {
                        for operand in payload {
                            let transferred_owned_payload = !is_heap_result_enum
                                && owned_enum_destination
                                && operand.mode == UseMode::Consume
                                && matches!(operand.source, Source::Local(local)
                                    if function.locals.get(local.0 as usize).is_some_and(|binding|
                                        binding.ty == Type::String
                                            || scoped_string::owns_string_aggregate(program, &binding.ty)));
                            if !transferred_owned_payload {
                                report(block_id, operand, true, false);
                            }
                        }
                    }
                }
                InstructionKind::ArrayNew { init } => {
                    if let ArrayInit::Elements(elements) = init {
                        let destination =
                            scoped_string::array_binding(function, &block.instructions[position..])
                                .is_some()
                                || instruction.output.is_some_and(|output| {
                                    matches!(&block.terminator.kind,
                                    TerminatorKind::Return(Some(Operand {
                                        source: Source::Value(returned),
                                        mode: UseMode::Consume,
                                        ..
                                    })) if *returned == output)
                                });
                        let element_ty = instruction
                            .output
                            .and_then(|output| function.values.get(output.0 as usize))
                            .and_then(|ty| match ty {
                                Type::Array { element, .. } => Some(element.as_ref()),
                                _ => None,
                            });
                        for element in elements {
                            let moved_owner = destination
                                && element.mode == UseMode::Consume
                                && element_ty.is_some_and(|ty| {
                                    scoped_string::owns_string_storage(program, ty)
                                        && matches!(element.source, Source::Local(local)
                                            if function.locals.get(local.0 as usize)
                                                .is_some_and(|binding| binding.ty == *ty))
                                });
                            if !moved_owner {
                                report(block_id, element, true, false);
                            }
                        }
                    }
                }
                InstructionKind::SwapPlaces { left, right } => {
                    report(block_id, left, false, false);
                    report(block_id, right, false, false);
                }
                InstructionKind::Store { reference, value } => {
                    report(block_id, reference, false, false);
                    if scoped_string::string_share_parameter(function, reference).is_none() {
                        report(block_id, value, true, false);
                    }
                }
                InstructionKind::ListGet {
                    source,
                    index: offset,
                }
                | InstructionKind::ListRead {
                    source,
                    index: offset,
                }
                | InstructionKind::CollectionSearch {
                    source,
                    value: offset,
                    ..
                }
                | InstructionKind::ValidateUtf8 {
                    source,
                    length: offset,
                    ..
                }
                | InstructionKind::StringIsCharBoundary { source, offset }
                | InstructionKind::StringByteAt { source, offset }
                | InstructionKind::StringScalarAt { source, offset }
                | InstructionKind::StringScalarRead { source, offset, .. } => {
                    report(block_id, source, false, false);
                    report(block_id, offset, false, false);
                }
                InstructionKind::ListClear { .. } | InstructionKind::ListPop { .. } => {}
                InstructionKind::ListPush { target, value } => {
                    // An owner element moves into the list: a consumed local of
                    // the element type (or a captured one, checked above).
                    let moved_owner = value.mode == UseMode::Consume
                        && matches!(value.source, Source::Local(local)
                        if function.locals.get(local.0 as usize).is_some_and(|binding|
                            scoped_string::owns_string_storage(program, &binding.ty)
                                && function.locals.get(target.0 as usize).is_some_and(|list| {
                                    let list = match &list.ty {
                                        Type::Reference { inner, .. } => inner.as_ref(),
                                        other => other,
                                    };
                                    matches!(list, Type::List(element) if **element == binding.ty)
                                })));
                    if !moved_owner {
                        report(block_id, value, false, false)
                    }
                }
                InstructionKind::ListLen { source }
                | InstructionKind::Copy { source }
                | InstructionKind::StringLen { source } => {
                    report(block_id, source, false, false);
                }
                InstructionKind::Unary { operand, .. } => report(block_id, operand, false, false),
                InstructionKind::Cast { value, .. } => report(block_id, value, false, false),
                InstructionKind::Binary { left, right, .. } => {
                    report(block_id, left, false, false);
                    report(block_id, right, false, false);
                }
                InstructionKind::Assign {
                    target,
                    value,
                    initialize,
                } => {
                    if scoped_string::local_move_source(function, *target, value, *initialize)
                        .or_else(|| {
                            scoped_string::struct_move_source(function, *target, value, *initialize)
                        })
                        .or_else(|| {
                            scoped_string::array_move_source(function, *target, value, *initialize)
                        })
                        .is_none()
                    {
                        report(block_id, value, true, false);
                    }
                }
                InstructionKind::InitConcatString { strings, .. } => {
                    for source in strings {
                        report(block_id, source, false, false);
                    }
                }
                InstructionKind::InitInterpolatedString { parts, .. } => {
                    for part in parts {
                        if let InterpolationPart::Value(source) = part {
                            report(block_id, source, false, false);
                        }
                    }
                }
                InstructionKind::Call { callee, arguments } => {
                    report(block_id, callee, true, false);
                    for (index, argument) in arguments.iter().enumerate() {
                        if scoped_string::owned_call_transfer(program, callee, index, argument)
                            .is_none()
                        {
                            report(block_id, argument, true, false);
                        }
                    }
                }
                InstructionKind::EmptyList
                | InstructionKind::DropLocal { .. }
                | InstructionKind::Assert { .. }
                | InstructionKind::EndListLocal { .. }
                | InstructionKind::Constant(_)
                | InstructionKind::EndStructLocal { .. }
                | InstructionKind::ReplaceStringField { .. }
                | InstructionKind::EndStringLocal { .. } => {}
            }
        }
        match &block.terminator.kind {
            TerminatorKind::Goto(edge) => {
                for argument in &edge.arguments {
                    report(block_id, argument, false, true);
                }
            }
            TerminatorKind::Branch {
                condition,
                then_edge,
                else_edge,
            } => {
                report(block_id, condition, false, false);
                for edge in [then_edge, else_edge] {
                    for argument in &edge.arguments {
                        report(block_id, argument, false, true);
                    }
                }
            }
            TerminatorKind::Switch {
                tag,
                targets,
                default,
                ..
            } => {
                report(block_id, tag, false, false);
                for edge in targets.iter().map(|(_, edge)| edge).chain(default) {
                    for argument in &edge.arguments {
                        report(block_id, argument, false, true);
                    }
                }
            }
            TerminatorKind::Return(Some(value)) => {
                let tuple_move = scoped_string::is_string_owner_transport(
                    &program.types,
                    function.signature.result.as_ref(),
                ) && matches!(value.source, Source::Local(_))
                    && value.mode == UseMode::Consume;
                if !tuple_move {
                    report(block_id, value, true, false);
                }
            }
            TerminatorKind::Return(None) | TerminatorKind::Unreachable => {}
        }
    }
    for block in borrowed_payload_extractions {
        push(
            errors,
            id,
            Some(block),
            "a heap String payload cannot be extracted from borrowed, field or array-element storage",
        );
    }
}

fn operand_is_read_only(operand: &Operand, read_only: &[bool]) -> bool {
    matches!(operand.source, Source::Value(value) if read_only.get(value.0 as usize) == Some(&true))
}

fn outgoing_edges(terminator: &TerminatorKind) -> Vec<&Edge> {
    match terminator {
        TerminatorKind::Goto(edge) => vec![edge],
        TerminatorKind::Branch {
            then_edge,
            else_edge,
            ..
        } => vec![then_edge, else_edge],
        TerminatorKind::Switch {
            targets, default, ..
        } => targets
            .iter()
            .map(|(_, edge)| edge)
            .chain(default.iter())
            .collect(),
        TerminatorKind::Return(_) | TerminatorKind::Unreachable => Vec::new(),
    }
}

fn validate_edge(
    program: &Program,
    function: &Function,
    edge: &Edge,
    errors: &mut Vec<ValidationError>,
    id: FunctionId,
    block: BlockId,
) {
    let target = function.blocks.get(edge.target.0 as usize);
    if target.is_none() {
        push(
            errors,
            id,
            Some(block),
            format!("edge target {:?} is out of range", edge.target),
        );
    }
    if let Some(target) = target {
        if target.parameters.len() != edge.arguments.len() {
            push(
                errors,
                id,
                Some(block),
                "edge argument count differs from target block parameters",
            );
        }
        for (arg, parameter) in edge.arguments.iter().zip(&target.parameters) {
            let actual = operand_type(program, function, arg, errors, id, block);
            if let (Some(actual), Some(expected)) =
                (actual, function.values.get(parameter.0 as usize))
            {
                if &actual != expected {
                    push(
                        errors,
                        id,
                        Some(block),
                        "edge argument type differs from target block parameter",
                    );
                }
            }
        }
        for arg in edge.arguments.iter().skip(target.parameters.len()) {
            operand_type(program, function, arg, errors, id, block);
        }
    } else {
        for arg in &edge.arguments {
            operand_type(program, function, arg, errors, id, block);
        }
    }
}

fn validate_terminator(
    program: &Program,
    function: &Function,
    terminator: &Terminator,
    errors: &mut Vec<ValidationError>,
    id: FunctionId,
    block: BlockId,
) {
    match &terminator.kind {
        TerminatorKind::Goto(edge) => validate_edge(program, function, edge, errors, id, block),
        TerminatorKind::Branch {
            condition,
            then_edge,
            else_edge,
        } => {
            let ty = operand_type(program, function, condition, errors, id, block);
            if ty.is_some_and(|ty| ty != Type::Primitive(Primitive::Bool)) {
                push(errors, id, Some(block), "branch condition must be Bool");
            }
            validate_edge(program, function, then_edge, errors, id, block);
            validate_edge(program, function, else_edge, errors, id, block);
        }
        TerminatorKind::Switch {
            tag,
            ty,
            targets,
            default,
        } => {
            let actual = operand_type(program, function, tag, errors, id, block);
            if actual.is_some_and(|actual| actual != Type::Primitive(Primitive::U32)) {
                push(errors, id, Some(block), "switch tag must be u32");
            }
            let variants = match program.types.get(ty.0 as usize) {
                Some(TypeDef {
                    kind: TypeDefKind::Enum { variants },
                    ..
                }) => Some(variants.len()),
                _ => {
                    push(
                        errors,
                        id,
                        Some(block),
                        format!("switch type {:?} is out of range or names a struct", ty),
                    );
                    None
                }
            };
            let mut seen = HashSet::new();
            for (variant, edge) in targets {
                if !seen.insert(*variant) {
                    push(
                        errors,
                        id,
                        Some(block),
                        format!("switch lists variant {variant} more than once"),
                    );
                }
                if variants.is_some_and(|count| *variant as usize >= count) {
                    push(
                        errors,
                        id,
                        Some(block),
                        format!("switch variant {variant} is out of range"),
                    );
                }
                validate_edge(program, function, edge, errors, id, block);
            }
            if let Some(count) = variants {
                if default.is_none() && (0..count as u32).any(|variant| !seen.contains(&variant)) {
                    push(
                        errors,
                        id,
                        Some(block),
                        "switch must list every variant or have a default",
                    );
                }
            }
            if let Some(edge) = default {
                validate_edge(program, function, edge, errors, id, block);
            }
        }
        TerminatorKind::Return(value) => {
            let actual = value
                .as_ref()
                .map(|value| operand_type(program, function, value, errors, id, block));
            let expected = function.signature.result.as_ref();
            match actual {
                None if expected != &Type::Primitive(Primitive::Unit) => {
                    push(errors, id, Some(block), "non-Unit return requires a value")
                }
                Some(Some(actual)) if &actual != expected => push(
                    errors,
                    id,
                    Some(block),
                    "return value type differs from function result",
                ),
                _ => {}
            }
        }
        TerminatorKind::Unreachable => {}
    }
}

fn is_numeric(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Primitive(
            Primitive::I8
                | Primitive::I16
                | Primitive::I32
                | Primitive::I64
                | Primitive::U8
                | Primitive::U16
                | Primitive::U32
                | Primitive::U64
                | Primitive::F32
                | Primitive::F64
        )
    )
}
/// Whether `output` is the scalar option type `T?` of the integer type `lhs`.
fn is_checked_option(program: &Program, lhs: &Type, output: &Type) -> bool {
    let (Type::Primitive(payload), Type::Enum(id)) = (lhs, output) else {
        return false;
    };
    let name = format!("{}?", primitive_name(*payload));
    program
        .types
        .get(id.0 as usize)
        .is_some_and(|ty| ty.is_scalar_option(&name, *payload))
}

fn primitive_name(primitive: Primitive) -> &'static str {
    match primitive {
        Primitive::I8 => "i8",
        Primitive::I16 => "i16",
        Primitive::I32 => "i32",
        Primitive::I64 => "i64",
        Primitive::U8 => "u8",
        Primitive::U16 => "u16",
        Primitive::U32 => "u32",
        Primitive::U64 => "u64",
        _ => "?",
    }
}

fn is_integer(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Primitive(
            Primitive::I8
                | Primitive::I16
                | Primitive::I32
                | Primitive::I64
                | Primitive::U8
                | Primitive::U16
                | Primitive::U32
                | Primitive::U64
        )
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_program_is_structurally_valid() {
        assert_eq!(Program::default().validate(), Ok(()));
    }

    #[test]
    fn canonical_paths_keep_module_boundaries() {
        let a = CanonicalFunction {
            package: "demo".into(),
            module: vec!["math".into(), "vector".into()],
            name: "length".into(),
        };
        let b = CanonicalFunction {
            package: "demo".into(),
            module: vec!["math_vector".into()],
            name: "length".into(),
        };
        assert_ne!(a, b);
    }
}
