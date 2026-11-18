//! Data-only typed control-flow IR. Construction and semantic proof belong to
//! analysis passes; `validate` performs structural and selected type checks.
use memobits_diagnostics::Span;
use std::collections::HashSet;

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
    Attempt,
}

impl EntryOutcome {
    pub fn variants(self) -> &'static [&'static str] {
        match self {
            Self::Result => &["Ok", "Err"],
            Self::Attempt => &["Done", "Skipped", "Failed"],
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
    fn borrow_option_referent(&self) -> Option<&Type> {
        if !self.path.name.starts_with("Option<borrow ")
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
            }] if some.name == "Some" && none.name == "None" && none.payload.is_empty() => {
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Local {
    pub name: String,
    pub ty: Type,
    pub mutable: bool,
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
    /// Read the byte length of an owned String or a reference to one.
    StringLen {
        source: Operand,
    },
    /// Test whether a byte offset is an endpoint or starts a UTF-8 scalar.
    StringIsCharBoundary {
        source: Operand,
        offset: Operand,
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
            validate_read_only_loaded_values(function, id, &mut errors);
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

impl Program {
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
                            && (outcome != EntryOutcome::Attempt || variants[1].payload.is_empty())
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
                            variant.payload.iter().all(|ty| self.valid_field_type(ty))
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
                Type::Array { .. } | Type::Struct(_) | Type::Enum(_)
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
                            | Primitive::U64,
                    )),
                ) | (
                    Constant::Float(_),
                    Some(Type::Primitive(Primitive::F32 | Primitive::F64))
                ) | (Constant::Bool(_), Some(Type::Primitive(Primitive::Bool)))
                    | (Constant::Unit, Some(Type::Primitive(Primitive::Unit)))
                    | (Constant::String(_), Some(Type::String))
            );
            if out.is_some() && !okay {
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
        | InstructionKind::StringIsCharBoundary { source, .. } => {
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
            let result =
                if let InstructionKind::StringIsCharBoundary { offset, .. } = &instruction.kind {
                    if operand_type(program, function, offset, errors, id, block)
                        != Some(Type::Primitive(Primitive::U32))
                        || offset.mode != UseMode::Read
                    {
                        push(
                            errors,
                            id,
                            Some(block),
                            "String boundary offset must be read as u32",
                        );
                    }
                    Primitive::Bool
                } else {
                    Primitive::U32
                };
            if out != Some(&Type::Primitive(result)) {
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
                Type::Array { element, .. } if *access != Access::Owned => Some(*element),
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
                        Type::Array { element, .. } => Some(*element),
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
                    BinaryOp::Remainder => both && is_integer(&lhs) && output == &lhs,
                    BinaryOp::Less
                    | BinaryOp::LessEqual
                    | BinaryOp::Greater
                    | BinaryOp::GreaterEqual => both && is_numeric(&lhs) && output == &bool_ty,
                    BinaryOp::Equal | BinaryOp::NotEqual => {
                        both && (is_numeric(&lhs) || lhs == bool_ty) && output == &bool_ty
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

fn validate_read_only_loaded_values(
    function: &Function,
    id: FunctionId,
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

    let mut report = |block: BlockId, operand: &Operand, escape: bool| {
        if operand_is_read_only(operand, &read_only) && (escape || operand.mode != UseMode::Read) {
            push(
                errors,
                id,
                Some(block),
                "loaded reference value is read-only and cannot be consumed or escape its reference",
            );
        }
    };

    for (index, block) in function.blocks.iter().enumerate() {
        let block_id = BlockId(index as u32);
        for instruction in &block.instructions {
            match &instruction.kind {
                InstructionKind::Capture(value)
                | InstructionKind::Borrow { owner: value, .. }
                | InstructionKind::Load { reference: value } => report(block_id, value, false),
                InstructionKind::ElementAddr { base, index, .. } => {
                    report(block_id, base, false);
                    report(block_id, index, false);
                }
                InstructionKind::FieldAddr { base, .. }
                | InstructionKind::VariantAddr { base, .. }
                | InstructionKind::Extract { base, .. }
                | InstructionKind::EnumTag { base }
                | InstructionKind::VariantExtract { base, .. } => report(block_id, base, false),
                InstructionKind::StructNew { fields, .. } => {
                    for field in fields {
                        report(block_id, field, true);
                    }
                }
                InstructionKind::EnumNew { payload, .. } => {
                    for operand in payload {
                        report(block_id, operand, true);
                    }
                }
                InstructionKind::ArrayNew { init } => {
                    if let ArrayInit::Elements(elements) = init {
                        for element in elements {
                            report(block_id, element, true);
                        }
                    }
                }
                InstructionKind::Store { reference, value } => {
                    report(block_id, reference, false);
                    report(block_id, value, true);
                }
                InstructionKind::StringIsCharBoundary { source, offset } => {
                    report(block_id, source, false);
                    report(block_id, offset, false);
                }
                InstructionKind::Copy { source } | InstructionKind::StringLen { source } => {
                    report(block_id, source, false);
                }
                InstructionKind::Unary { operand, .. } => report(block_id, operand, false),
                InstructionKind::Binary { left, right, .. } => {
                    report(block_id, left, false);
                    report(block_id, right, false);
                }
                InstructionKind::Assign { value, .. } => report(block_id, value, true),
                InstructionKind::Call { callee, arguments } => {
                    report(block_id, callee, true);
                    for argument in arguments {
                        report(block_id, argument, true);
                    }
                }
                InstructionKind::Constant(_) => {}
            }
        }
        match &block.terminator.kind {
            TerminatorKind::Goto(edge) => {
                for argument in &edge.arguments {
                    report(block_id, argument, false);
                }
            }
            TerminatorKind::Branch {
                condition,
                then_edge,
                else_edge,
            } => {
                report(block_id, condition, false);
                for edge in [then_edge, else_edge] {
                    for argument in &edge.arguments {
                        report(block_id, argument, false);
                    }
                }
            }
            TerminatorKind::Switch {
                tag,
                targets,
                default,
                ..
            } => {
                report(block_id, tag, false);
                for edge in targets.iter().map(|(_, edge)| edge).chain(default) {
                    for argument in &edge.arguments {
                        report(block_id, argument, false);
                    }
                }
            }
            TerminatorKind::Return(Some(value)) => report(block_id, value, true),
            TerminatorKind::Return(None) | TerminatorKind::Unreachable => {}
        }
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
