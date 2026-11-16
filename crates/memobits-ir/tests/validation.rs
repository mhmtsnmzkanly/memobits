use memobits_diagnostics::{SourceId, Span};
use memobits_ir::*;

fn span() -> Span {
    Span {
        source: SourceId(0),
        start: 0,
        end: 1,
    }
}
fn i32_ty() -> Type {
    Type::Primitive(Primitive::I32)
}
fn bool_ty() -> Type {
    Type::Primitive(Primitive::Bool)
}
fn operand(source: Source, mode: UseMode) -> Operand {
    Operand {
        source,
        mode,
        span: Some(span()),
    }
}
fn function() -> Function {
    Function {
        path: CanonicalFunction {
            package: "test".into(),
            module: vec!["main".into()],
            name: "main".into(),
        },
        span: span(),
        signature: Signature {
            parameters: vec![],
            result: Box::new(i32_ty()),
        },
        parameter_locals: vec![],
        locals: vec![],
        values: vec![i32_ty()],
        blocks: vec![Block {
            parameters: vec![],
            instructions: vec![Instruction {
                span: Some(span()),
                output: Some(ValueId(0)),
                kind: InstructionKind::Constant(Constant::Integer("42".into())),
            }],
            terminator: Terminator {
                span: Some(span()),
                kind: TerminatorKind::Return(Some(operand(
                    Source::Value(ValueId(0)),
                    UseMode::Consume,
                ))),
            },
        }],
        entry: BlockId(0),
    }
}

#[test]
fn accepts_well_formed_function_and_join() {
    let mut f = function();
    f.values.push(bool_ty());
    f.values.push(i32_ty());
    f.blocks[0].instructions.push(Instruction {
        span: Some(span()),
        output: Some(ValueId(1)),
        kind: InstructionKind::Constant(Constant::Bool(true)),
    });
    f.blocks[0].terminator.kind = TerminatorKind::Branch {
        condition: operand(Source::Value(ValueId(1)), UseMode::Read),
        then_edge: Edge {
            target: BlockId(1),
            arguments: vec![operand(Source::Value(ValueId(0)), UseMode::Consume)],
        },
        else_edge: Edge {
            target: BlockId(1),
            arguments: vec![operand(Source::Value(ValueId(0)), UseMode::Consume)],
        },
    };
    f.blocks.push(Block {
        parameters: vec![ValueId(2)],
        instructions: vec![],
        terminator: Terminator {
            span: None,
            kind: TerminatorKind::Return(Some(operand(
                Source::Value(ValueId(2)),
                UseMode::Consume,
            ))),
        },
    });
    assert_eq!(Program { functions: vec![f] }.validate(), Ok(()));
}

#[test]
fn rejects_eager_logical_binary_operations() {
    let mut f = function();
    f.values.extend([bool_ty(), bool_ty()]);
    f.blocks[0].instructions = vec![
        Instruction {
            span: Some(span()),
            output: Some(ValueId(1)),
            kind: InstructionKind::Constant(Constant::Bool(true)),
        },
        Instruction {
            span: Some(span()),
            output: Some(ValueId(2)),
            kind: InstructionKind::Binary {
                op: BinaryOp::And,
                left: operand(Source::Value(ValueId(1)), UseMode::Read),
                right: operand(Source::Value(ValueId(1)), UseMode::Read),
            },
        },
    ];
    f.blocks[0].terminator.kind =
        TerminatorKind::Return(Some(operand(Source::Value(ValueId(0)), UseMode::Consume)));

    let errors = Program { functions: vec![f] }.validate().unwrap_err();
    assert!(errors
        .iter()
        .any(|error| { error.message.contains("short-circuit evaluation") }));
}

#[test]
fn rejects_entry_block_parameters() {
    let mut f = function();
    f.values.push(bool_ty());
    f.blocks[0].parameters.push(ValueId(1));

    let errors = Program { functions: vec![f] }.validate().unwrap_err();
    assert!(errors
        .iter()
        .any(|error| error.message.contains("entry block cannot have parameters")));
}

#[test]
fn validates_reference_parameters_and_loads() {
    let mut f = function();
    f.signature.parameters = vec![ParameterType {
        access: Access::Borrow,
        ty: i32_ty(),
    }];
    f.signature.result = Box::new(Type::Primitive(Primitive::Unit));
    f.parameter_locals = vec![LocalId(0)];
    f.locals = vec![Local {
        name: "value".into(),
        ty: Type::Reference {
            access: Access::Borrow,
            inner: Box::new(i32_ty()),
        },
        mutable: false,
        span: span(),
    }];
    f.values = vec![i32_ty()];
    f.blocks[0].instructions = vec![Instruction {
        span: Some(span()),
        output: Some(ValueId(0)),
        kind: InstructionKind::Load {
            reference: operand(Source::Local(LocalId(0)), UseMode::Borrow),
        },
    }];
    f.blocks[0].terminator.kind = TerminatorKind::Return(None);

    assert_eq!(Program { functions: vec![f] }.validate(), Ok(()));
}

#[test]
fn validates_exclusive_reference_stores() {
    let mut f = function();
    f.signature.parameters = vec![ParameterType {
        access: Access::Share,
        ty: i32_ty(),
    }];
    f.signature.result = Box::new(Type::Primitive(Primitive::Unit));
    f.parameter_locals = vec![LocalId(0)];
    f.locals = vec![Local {
        name: "value".into(),
        ty: Type::Reference {
            access: Access::Share,
            inner: Box::new(i32_ty()),
        },
        mutable: false,
        span: span(),
    }];
    f.values = vec![i32_ty()];
    f.blocks[0].instructions = vec![
        Instruction {
            span: Some(span()),
            output: Some(ValueId(0)),
            kind: InstructionKind::Constant(Constant::Integer("9".into())),
        },
        Instruction {
            span: Some(span()),
            output: None,
            kind: InstructionKind::Store {
                reference: operand(Source::Local(LocalId(0)), UseMode::Share),
                value: operand(Source::Value(ValueId(0)), UseMode::Consume),
            },
        },
    ];
    f.blocks[0].terminator.kind = TerminatorKind::Return(None);

    assert_eq!(Program { functions: vec![f] }.validate(), Ok(()));
}

#[test]
fn loaded_reference_values_cannot_be_consumed_as_owned() {
    let mut f = function();
    f.signature.parameters = vec![ParameterType {
        access: Access::Borrow,
        ty: i32_ty(),
    }];
    f.parameter_locals = vec![LocalId(0)];
    f.locals = vec![Local {
        name: "value".into(),
        ty: Type::Reference {
            access: Access::Borrow,
            inner: Box::new(i32_ty()),
        },
        mutable: false,
        span: span(),
    }];
    f.values = vec![i32_ty()];
    f.blocks[0].instructions = vec![Instruction {
        span: Some(span()),
        output: Some(ValueId(0)),
        kind: InstructionKind::Load {
            reference: operand(Source::Local(LocalId(0)), UseMode::Borrow),
        },
    }];
    f.blocks[0].terminator.kind =
        TerminatorKind::Return(Some(operand(Source::Value(ValueId(0)), UseMode::Consume)));

    let errors = Program { functions: vec![f] }.validate().unwrap_err();
    assert!(errors
        .iter()
        .any(|error| error.message.contains("read-only and cannot be consumed")));
}

#[test]
fn read_only_load_provenance_survives_capture_and_block_arguments() {
    let mut f = function();
    f.signature.parameters = vec![ParameterType {
        access: Access::Borrow,
        ty: i32_ty(),
    }];
    f.parameter_locals = vec![LocalId(0)];
    f.locals = vec![Local {
        name: "value".into(),
        ty: Type::Reference {
            access: Access::Borrow,
            inner: Box::new(i32_ty()),
        },
        mutable: false,
        span: span(),
    }];
    f.values = vec![i32_ty(), i32_ty(), i32_ty()];
    f.blocks = vec![
        Block {
            parameters: vec![],
            instructions: vec![
                Instruction {
                    span: Some(span()),
                    output: Some(ValueId(0)),
                    kind: InstructionKind::Load {
                        reference: operand(Source::Local(LocalId(0)), UseMode::Borrow),
                    },
                },
                Instruction {
                    span: Some(span()),
                    output: Some(ValueId(1)),
                    kind: InstructionKind::Capture(operand(
                        Source::Value(ValueId(0)),
                        UseMode::Read,
                    )),
                },
            ],
            terminator: Terminator {
                span: None,
                kind: TerminatorKind::Goto(Edge {
                    target: BlockId(1),
                    arguments: vec![operand(Source::Value(ValueId(1)), UseMode::Read)],
                }),
            },
        },
        Block {
            parameters: vec![ValueId(2)],
            instructions: vec![],
            terminator: Terminator {
                span: None,
                kind: TerminatorKind::Return(Some(operand(
                    Source::Value(ValueId(2)),
                    UseMode::Consume,
                ))),
            },
        },
    ];

    let errors = Program { functions: vec![f] }.validate().unwrap_err();
    assert!(errors
        .iter()
        .any(|error| error.message.contains("read-only and cannot be consumed")));
}

#[test]
fn reference_types_reject_owned_access_and_reference_results() {
    let mut f = function();
    f.locals.push(Local {
        name: "invalid".into(),
        ty: Type::Reference {
            access: Access::Owned,
            inner: Box::new(i32_ty()),
        },
        mutable: false,
        span: span(),
    });
    f.signature.result = Box::new(Type::Reference {
        access: Access::Borrow,
        inner: Box::new(i32_ty()),
    });

    let errors = Program { functions: vec![f] }.validate().unwrap_err();
    assert!(errors
        .iter()
        .any(|error| error.message.contains("reference cannot use Owned access")));
    assert!(errors.iter().any(|error| error
        .message
        .contains("function result type cannot be a reference")));
}

#[test]
fn calls_require_reference_arguments_for_borrow_and_share_parameters() {
    let mut callee = function();
    callee.path.name = "callee".into();
    callee.signature.parameters = vec![ParameterType {
        access: Access::Borrow,
        ty: i32_ty(),
    }];
    callee.signature.result = Box::new(Type::Primitive(Primitive::Unit));
    callee.parameter_locals = vec![LocalId(0)];
    callee.locals = vec![Local {
        name: "value".into(),
        ty: Type::Reference {
            access: Access::Borrow,
            inner: Box::new(i32_ty()),
        },
        mutable: false,
        span: span(),
    }];
    callee.values.clear();
    callee.blocks[0].instructions.clear();
    callee.blocks[0].terminator.kind = TerminatorKind::Return(None);

    let mut caller = function();
    caller.path.name = "caller".into();
    caller.signature.result = Box::new(Type::Primitive(Primitive::Unit));
    caller.locals = vec![Local {
        name: "shared".into(),
        ty: Type::Reference {
            access: Access::Share,
            inner: Box::new(i32_ty()),
        },
        mutable: true,
        span: span(),
    }];
    caller.values = vec![Type::Primitive(Primitive::Unit)];
    caller.blocks[0].instructions = vec![Instruction {
        span: Some(span()),
        output: Some(ValueId(0)),
        kind: InstructionKind::Call {
            callee: operand(Source::Function(FunctionId(0)), UseMode::Read),
            arguments: vec![operand(Source::Local(LocalId(0)), UseMode::Borrow)],
        },
    }];
    caller.blocks[0].terminator.kind = TerminatorKind::Return(None);

    assert_eq!(
        Program {
            functions: vec![callee.clone(), caller.clone()]
        }
        .validate(),
        Ok(())
    );

    callee.signature.parameters[0].access = Access::Owned;
    callee.locals[0].ty = i32_ty();
    let errors = Program {
        functions: vec![callee, caller],
    }
    .validate()
    .unwrap_err();
    assert!(errors.iter().any(|error| error
        .message
        .contains("call argument type or reference access")));
}

#[test]
fn detects_missing_targets_and_bad_return_type() {
    let mut f = function();
    f.blocks[0].terminator.kind = TerminatorKind::Goto(Edge {
        target: BlockId(9),
        arguments: vec![],
    });
    f.entry = BlockId(8);
    let errors = Program { functions: vec![f] }.validate().unwrap_err();
    assert!(errors.iter().any(|e| e.message.contains("entry block")));
    assert!(errors.iter().any(|e| e.message.contains("edge target")));

    let mut f = function();
    f.values[0] = bool_ty();
    f.blocks[0].instructions[0].kind = InstructionKind::Constant(Constant::Bool(true));
    let errors = Program { functions: vec![f] }.validate().unwrap_err();
    assert!(errors
        .iter()
        .any(|e| e.message.contains("return value type")));
}

#[test]
fn detects_duplicate_values_and_invalid_operand_ids() {
    let mut f = function();
    let duplicate = f.blocks[0].instructions[0].clone();
    f.blocks[0].instructions.push(duplicate);
    f.blocks[0].terminator.kind =
        TerminatorKind::Return(Some(operand(Source::Local(LocalId(4)), UseMode::Consume)));
    let errors = Program { functions: vec![f] }.validate().unwrap_err();
    assert!(errors
        .iter()
        .any(|e| e.message.contains("defined more than once")));
    assert!(errors.iter().any(|e| e.message.contains("out of range")));
}

#[test]
fn checks_call_signature_and_use_modes() {
    let mut caller = function();
    caller.values.push(i32_ty());
    caller.blocks[0].instructions.push(Instruction {
        span: Some(span()),
        output: Some(ValueId(1)),
        kind: InstructionKind::Call {
            callee: operand(Source::Function(FunctionId(1)), UseMode::Read),
            arguments: vec![operand(Source::Value(ValueId(0)), UseMode::Read)],
        },
    });
    let mut callee = function();
    callee.path.name = "take".into();
    callee.signature.parameters.push(ParameterType {
        access: Access::Owned,
        ty: i32_ty(),
    });
    callee.locals.push(Local {
        name: "x".into(),
        ty: i32_ty(),
        mutable: false,
        span: span(),
    });
    callee.parameter_locals.push(LocalId(0));
    let errors = Program {
        functions: vec![caller, callee],
    }
    .validate()
    .unwrap_err();
    assert!(errors.iter().any(|e| e.message.contains("use mode")));
}

fn array_ty(len: u32) -> Type {
    Type::Array {
        element: Box::new(i32_ty()),
        len,
    }
}

fn instruction(output: Option<u32>, kind: InstructionKind) -> Instruction {
    Instruction {
        span: Some(span()),
        output: output.map(ValueId),
        kind,
    }
}

/// `a := [c, c]; return a[index] + 0` with the pieces individually adjustable.
/// Values: 0 const 42, 1 index, 2 array, 3 reference, 4 loaded, 5 const 0, 6 sum.
fn array_function(index_ty: Type) -> Function {
    let mut f = function();
    f.locals = vec![Local {
        name: "a".into(),
        ty: array_ty(2),
        mutable: false,
        span: span(),
    }];
    f.values = vec![
        i32_ty(),
        index_ty,
        array_ty(2),
        Type::Reference {
            access: Access::Borrow,
            inner: Box::new(i32_ty()),
        },
        i32_ty(),
        i32_ty(),
        i32_ty(),
    ];
    let value = |id: u32, mode| operand(Source::Value(ValueId(id)), mode);
    f.blocks[0].instructions = vec![
        instruction(
            Some(0),
            InstructionKind::Constant(Constant::Integer("42".into())),
        ),
        instruction(
            Some(1),
            InstructionKind::Constant(Constant::Integer("1".into())),
        ),
        instruction(
            Some(2),
            InstructionKind::ArrayNew {
                init: ArrayInit::Elements(vec![
                    value(0, UseMode::Consume),
                    value(0, UseMode::Consume),
                ]),
            },
        ),
        instruction(
            None,
            InstructionKind::Assign {
                target: LocalId(0),
                value: value(2, UseMode::Consume),
                initialize: true,
            },
        ),
        instruction(
            Some(3),
            InstructionKind::ElementAddr {
                loan: LoanId(0),
                base: operand(Source::Local(LocalId(0)), UseMode::Borrow),
                index: value(1, UseMode::Read),
                access: Access::Borrow,
            },
        ),
        instruction(
            Some(4),
            InstructionKind::Load {
                reference: value(3, UseMode::Borrow),
            },
        ),
        instruction(
            Some(5),
            InstructionKind::Constant(Constant::Integer("0".into())),
        ),
        instruction(
            Some(6),
            InstructionKind::Binary {
                op: BinaryOp::Add,
                left: value(4, UseMode::Read),
                right: value(5, UseMode::Read),
            },
        ),
    ];
    f.blocks[0].terminator.kind = TerminatorKind::Return(Some(value(6, UseMode::Consume)));
    f
}

fn messages(f: Function) -> Vec<String> {
    Program { functions: vec![f] }
        .validate()
        .err()
        .unwrap_or_default()
        .into_iter()
        .map(|error| error.message)
        .collect()
}

#[test]
fn accepts_array_new_and_element_address() {
    let f = array_function(i32_ty());
    assert_eq!(Program { functions: vec![f] }.validate(), Ok(()));
    // Any integer width is a valid index; Zeroed needs no operands.
    for index in [Primitive::U8, Primitive::I64, Primitive::U64] {
        let f = array_function(Type::Primitive(index));
        assert_eq!(
            Program { functions: vec![f] }.validate(),
            Ok(()),
            "{index:?}"
        );
    }
    let mut f = array_function(i32_ty());
    f.blocks[0].instructions[2].kind = InstructionKind::ArrayNew {
        init: ArrayInit::Zeroed,
    };
    assert_eq!(Program { functions: vec![f] }.validate(), Ok(()));
}

#[test]
fn rejects_array_literal_with_wrong_length_or_element_type() {
    let mut f = array_function(i32_ty());
    f.values[2] = array_ty(3);
    f.locals[0].ty = array_ty(3);
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("array literal length differs")));

    let mut f = array_function(i32_ty());
    f.values[0] = Type::Primitive(Primitive::I64);
    f.blocks[0].instructions[0].kind = InstructionKind::Constant(Constant::Integer("42".into()));
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("array element type differs")));

    let mut f = array_function(i32_ty());
    f.values[2] = i32_ty();
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("output must have an array type")));

    let mut f = array_function(i32_ty());
    if let InstructionKind::ArrayNew {
        init: ArrayInit::Elements(elements),
    } = &mut f.blocks[0].instructions[2].kind
    {
        elements[0].mode = UseMode::Read;
    }
    assert!(messages(f).iter().any(|m| m.contains("must be consumed")));
}

#[test]
fn rejects_bad_element_address_operands() {
    let f = array_function(Type::Primitive(Primitive::F64));
    let mut f = f;
    f.blocks[0].instructions[1].kind = InstructionKind::Constant(Constant::Float("1.0".into()));
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("index must be an integer")));

    let f = array_function(Type::Primitive(Primitive::Bool));
    let mut f = f;
    f.blocks[0].instructions[1].kind = InstructionKind::Constant(Constant::Bool(true));
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("index must be an integer")));

    let mut f = array_function(i32_ty());
    if let InstructionKind::ElementAddr { index, .. } = &mut f.blocks[0].instructions[4].kind {
        index.mode = UseMode::Consume;
    }
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("index must use Read mode")));

    let mut f = array_function(i32_ty());
    if let InstructionKind::ElementAddr { base, .. } = &mut f.blocks[0].instructions[4].kind {
        base.mode = UseMode::Read;
    }
    assert!(messages(f).iter().any(|m| m.contains("base mode")));

    let mut f = array_function(i32_ty());
    if let InstructionKind::ElementAddr { base, .. } = &mut f.blocks[0].instructions[4].kind {
        base.source = Source::Value(ValueId(0));
        base.mode = UseMode::Borrow;
    }
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("base must be an array")));

    let mut f = array_function(i32_ty());
    f.values[3] = Type::Reference {
        access: Access::Borrow,
        inner: Box::new(Type::Primitive(Primitive::I64)),
    };
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("output type is incompatible")));
}

#[test]
fn element_addresses_share_loan_ids_with_borrows() {
    let mut f = array_function(i32_ty());
    f.values.push(Type::Reference {
        access: Access::Borrow,
        inner: Box::new(array_ty(2)),
    });
    f.blocks[0].instructions.insert(
        5,
        instruction(
            Some(7),
            InstructionKind::Borrow {
                loan: LoanId(0),
                owner: operand(Source::Local(LocalId(0)), UseMode::Borrow),
                access: Access::Borrow,
            },
        ),
    );
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("loan ID is defined more than once")));
}

#[test]
fn rejects_malformed_array_types() {
    // Nested arrays of primitives are valid element shapes.
    let mut f = array_function(i32_ty());
    f.locals[0].ty = Type::Array {
        element: Box::new(array_ty(1)),
        len: 2,
    };
    assert!(!messages(f).iter().any(|m| m.contains("array element")));

    let mut f = array_function(i32_ty());
    f.locals[0].ty = Type::Array {
        element: Box::new(Type::Primitive(Primitive::Unit)),
        len: 2,
    };
    assert!(messages(f).iter().any(|m| m.contains("non-Unit primitive")));

    // Deep element shapes are validated recursively.
    let mut f = array_function(i32_ty());
    f.locals[0].ty = Type::Array {
        element: Box::new(Type::Array {
            element: Box::new(Type::Reference {
                access: Access::Borrow,
                inner: Box::new(i32_ty()),
            }),
            len: 1,
        }),
        len: 2,
    };
    assert!(messages(f).iter().any(|m| m.contains("non-Unit primitive")));

    // Array results and array block parameters are valid signature/join types.
    let mut f = array_function(i32_ty());
    f.signature.result = Box::new(array_ty(2));
    assert!(!messages(f).iter().any(|m| m.contains("cannot be an array")));

    let mut f = array_function(i32_ty());
    f.values.push(array_ty(2));
    f.blocks.push(Block {
        parameters: vec![ValueId(7)],
        instructions: vec![],
        terminator: Terminator {
            span: None,
            kind: TerminatorKind::Unreachable,
        },
    });
    assert!(!messages(f)
        .iter()
        .any(|m| m.contains("array-typed block parameters")));

    // A reference may refer to a primitive or an array, never to a reference.
    let mut f = array_function(i32_ty());
    f.values[3] = Type::Reference {
        access: Access::Borrow,
        inner: Box::new(Type::Reference {
            access: Access::Borrow,
            inner: Box::new(array_ty(2)),
        }),
    };
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("reference must refer to a primitive value or an array")));
}

#[test]
fn array_element_loads_are_read_only() {
    let mut f = array_function(i32_ty());
    f.blocks[0].terminator.kind =
        TerminatorKind::Return(Some(operand(Source::Value(ValueId(4)), UseMode::Consume)));
    assert!(messages(f).iter().any(|m| m.contains("read-only")));
}

/// `fn reader(a: <access> Array<i32, 2>) -> i32 { a[0] + 0 }` built by hand.
/// Values: 0 index, 1 element reference, 2 loaded, 3 const 0, 4 sum.
fn array_reference_function(access: Access) -> Function {
    let mut f = function();
    f.signature.parameters = vec![ParameterType {
        access,
        ty: array_ty(2),
    }];
    f.parameter_locals = vec![LocalId(0)];
    f.locals = vec![Local {
        name: "a".into(),
        ty: Type::Reference {
            access,
            inner: Box::new(array_ty(2)),
        },
        mutable: false,
        span: span(),
    }];
    f.values = vec![
        Type::Primitive(Primitive::U32),
        Type::Reference {
            access: Access::Borrow,
            inner: Box::new(i32_ty()),
        },
        i32_ty(),
        i32_ty(),
        i32_ty(),
    ];
    let value = |id: u32, mode| operand(Source::Value(ValueId(id)), mode);
    f.blocks[0].instructions = vec![
        instruction(
            Some(0),
            InstructionKind::Constant(Constant::Integer("0".into())),
        ),
        instruction(
            Some(1),
            InstructionKind::ElementAddr {
                loan: LoanId(0),
                base: operand(Source::Local(LocalId(0)), UseMode::Borrow),
                index: value(0, UseMode::Read),
                access: Access::Borrow,
            },
        ),
        instruction(
            Some(2),
            InstructionKind::Load {
                reference: value(1, UseMode::Borrow),
            },
        ),
        instruction(
            Some(3),
            InstructionKind::Constant(Constant::Integer("0".into())),
        ),
        instruction(
            Some(4),
            InstructionKind::Binary {
                op: BinaryOp::Add,
                left: value(2, UseMode::Read),
                right: value(3, UseMode::Read),
            },
        ),
    ];
    f.blocks[0].terminator.kind = TerminatorKind::Return(Some(value(4, UseMode::Consume)));
    f
}

#[test]
fn accepts_array_parameters_and_references_to_arrays() {
    for access in [Access::Owned, Access::Borrow, Access::Share] {
        let mut f = array_reference_function(access);
        if access == Access::Owned {
            // An owned array parameter is an array local, indexed in place.
            f.locals[0].ty = array_ty(2);
        }
        assert!(messages(f).is_empty(), "{access:?}");
    }
}

#[test]
fn array_parameter_locals_follow_the_signature_access_mode() {
    let mut f = array_reference_function(Access::Borrow);
    f.locals[0].ty = array_ty(2);
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("parameter local type differs")));
    let mut f = array_reference_function(Access::Borrow);
    f.signature.parameters[0].ty = array_ty(3);
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("parameter local type differs")));
    // A parameter names its pointee; a reference-typed parameter stays invalid.
    let mut f = array_reference_function(Access::Borrow);
    f.signature.parameters[0].ty = Type::Reference {
        access: Access::Borrow,
        inner: Box::new(array_ty(2)),
    };
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("cannot be a reference")));
}

#[test]
fn element_addresses_through_references_respect_access() {
    // A borrow reference cannot produce a Share element address.
    let mut f = array_reference_function(Access::Borrow);
    if let InstructionKind::ElementAddr { base, access, .. } = &mut f.blocks[0].instructions[1].kind
    {
        base.mode = UseMode::Share;
        *access = Access::Share;
    }
    f.values[1] = Type::Reference {
        access: Access::Share,
        inner: Box::new(i32_ty()),
    };
    assert!(messages(f).iter().any(|m| m.contains("strengthen")));
    // A reference to a primitive is not an array base.
    let mut f = array_reference_function(Access::Borrow);
    f.signature.parameters[0].ty = i32_ty();
    f.locals[0].ty = Type::Reference {
        access: Access::Borrow,
        inner: Box::new(i32_ty()),
    };
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("base must be an array owner or array reference")));
}

#[test]
fn borrowing_an_array_owner_produces_an_array_reference() {
    // a := [c, c]; r := borrow a  (value 7)
    let mut f = array_function(i32_ty());
    f.values.push(Type::Reference {
        access: Access::Borrow,
        inner: Box::new(array_ty(2)),
    });
    f.blocks[0].instructions.insert(
        5,
        instruction(
            Some(7),
            InstructionKind::Borrow {
                loan: LoanId(1),
                owner: operand(Source::Local(LocalId(0)), UseMode::Borrow),
                access: Access::Borrow,
            },
        ),
    );
    assert!(messages(f.clone()).is_empty(), "{:?}", messages(f.clone()));
    f.values[7] = Type::Reference {
        access: Access::Borrow,
        inner: Box::new(array_ty(3)),
    };
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("borrow output type is incompatible")));
}

#[test]
fn array_results_nested_element_addresses_and_whole_array_loads() {
    // An array-typed function result is valid; the returned value must match it.
    let mut f = array_function(i32_ty());
    f.signature.result = Box::new(array_ty(2));
    f.blocks[0].terminator.kind =
        TerminatorKind::Return(Some(operand(Source::Value(ValueId(2)), UseMode::Consume)));
    assert!(messages(f).is_empty());
    let mut f = array_function(i32_ty());
    f.signature.result = Box::new(array_ty(3));
    f.blocks[0].terminator.kind =
        TerminatorKind::Return(Some(operand(Source::Value(ValueId(2)), UseMode::Consume)));
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("return value type differs")));

    // Addressing a row of a nested array yields a reference to the row.
    let nested = Type::Array {
        element: Box::new(array_ty(2)),
        len: 2,
    };
    let mut f = array_function(i32_ty());
    f.locals[0].ty = nested;
    f.values[3] = Type::Reference {
        access: Access::Borrow,
        inner: Box::new(array_ty(2)),
    };
    let found = messages(f);
    assert!(
        !found.iter().any(|m| m.contains("element address")),
        "{found:?}"
    );

    // A whole-array load through such a reference is not an operation.
    let mut f = array_function(i32_ty());
    f.values[3] = Type::Reference {
        access: Access::Borrow,
        inner: Box::new(array_ty(2)),
    };
    f.values[4] = array_ty(2);
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("load of a whole array")));
}
