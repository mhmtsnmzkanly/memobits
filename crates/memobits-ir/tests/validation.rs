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
    assert_eq!(
        Program {
            functions: vec![f],
            ..Program::default()
        }
        .validate(),
        Ok(())
    );
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

    let errors = Program {
        functions: vec![f],
        ..Program::default()
    }
    .validate()
    .unwrap_err();
    assert!(errors
        .iter()
        .any(|error| { error.message.contains("short-circuit evaluation") }));
}

#[test]
fn rejects_entry_block_parameters() {
    let mut f = function();
    f.values.push(bool_ty());
    f.blocks[0].parameters.push(ValueId(1));

    let errors = Program {
        functions: vec![f],
        ..Program::default()
    }
    .validate()
    .unwrap_err();
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

    assert_eq!(
        Program {
            functions: vec![f],
            ..Program::default()
        }
        .validate(),
        Ok(())
    );
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

    assert_eq!(
        Program {
            functions: vec![f],
            ..Program::default()
        }
        .validate(),
        Ok(())
    );
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

    let errors = Program {
        functions: vec![f],
        ..Program::default()
    }
    .validate()
    .unwrap_err();
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

    let errors = Program {
        functions: vec![f],
        ..Program::default()
    }
    .validate()
    .unwrap_err();
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

    let errors = Program {
        functions: vec![f],
        ..Program::default()
    }
    .validate()
    .unwrap_err();
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
            functions: vec![callee.clone(), caller.clone()],
            ..Program::default()
        }
        .validate(),
        Ok(())
    );

    callee.signature.parameters[0].access = Access::Owned;
    callee.locals[0].ty = i32_ty();
    let errors = Program {
        functions: vec![callee, caller],
        ..Program::default()
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
    let errors = Program {
        functions: vec![f],
        ..Program::default()
    }
    .validate()
    .unwrap_err();
    assert!(errors.iter().any(|e| e.message.contains("entry block")));
    assert!(errors.iter().any(|e| e.message.contains("edge target")));

    let mut f = function();
    f.values[0] = bool_ty();
    f.blocks[0].instructions[0].kind = InstructionKind::Constant(Constant::Bool(true));
    let errors = Program {
        functions: vec![f],
        ..Program::default()
    }
    .validate()
    .unwrap_err();
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
    let errors = Program {
        functions: vec![f],
        ..Program::default()
    }
    .validate()
    .unwrap_err();
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
        ..Program::default()
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
    Program {
        functions: vec![f],
        ..Program::default()
    }
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
    assert_eq!(
        Program {
            functions: vec![f],
            ..Program::default()
        }
        .validate(),
        Ok(())
    );
    // Any integer width is a valid index; Zeroed needs no operands.
    for index in [Primitive::U8, Primitive::I64, Primitive::U64] {
        let f = array_function(Type::Primitive(index));
        assert_eq!(
            Program {
                functions: vec![f],
                ..Program::default()
            }
            .validate(),
            Ok(()),
            "{index:?}"
        );
    }
    let mut f = array_function(i32_ty());
    f.blocks[0].instructions[2].kind = InstructionKind::ArrayNew {
        init: ArrayInit::Zeroed,
    };
    assert_eq!(
        Program {
            functions: vec![f],
            ..Program::default()
        }
        .validate(),
        Ok(())
    );
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
        .any(|m| m.contains("reference must refer to a primitive value, an array or a struct")));
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

fn copy_function(source_ty: Type, output_ty: Type, mode: UseMode) -> Function {
    let mut f = function();
    f.signature.parameters = vec![ParameterType {
        access: Access::Borrow,
        ty: source_ty.clone(),
    }];
    f.signature.result = Box::new(output_ty.clone());
    f.parameter_locals = vec![LocalId(0)];
    f.locals = vec![Local {
        name: "value".into(),
        ty: Type::Reference {
            access: Access::Borrow,
            inner: Box::new(source_ty),
        },
        mutable: false,
        span: span(),
    }];
    f.values = vec![i32_ty(), output_ty];
    f.blocks[0].instructions = vec![
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
            kind: InstructionKind::Copy {
                source: operand(Source::Value(ValueId(0)), mode),
            },
        },
    ];
    f.blocks[0].terminator.kind =
        TerminatorKind::Return(Some(operand(Source::Value(ValueId(1)), UseMode::Consume)));
    f
}

#[test]
fn copy_turns_a_loaded_read_only_value_into_an_owned_value() {
    let f = copy_function(i32_ty(), i32_ty(), UseMode::Read);
    Program {
        functions: vec![f],
        ..Program::default()
    }
    .validate()
    .unwrap();
}

#[test]
fn copy_requires_a_primitive_read_source_with_matching_output() {
    let messages = |f: Function| -> Vec<String> {
        Program {
            functions: vec![f],
            ..Program::default()
        }
        .validate()
        .unwrap_err()
        .into_iter()
        .map(|error| error.message)
        .collect()
    };
    assert!(
        messages(copy_function(i32_ty(), i32_ty(), UseMode::Consume))
            .iter()
            .any(|m| m.contains("only read its source"))
    );
    let mut f = copy_function(i32_ty(), bool_ty(), UseMode::Read);
    f.values[0] = i32_ty();
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("copy output type differs")));
    let mut f = copy_function(i32_ty(), i32_ty(), UseMode::Read);
    f.values[0] = Type::Array {
        element: Box::new(i32_ty()),
        len: 2,
    };
    f.values[1] = f.values[0].clone();
    assert!(messages(f)
        .iter()
        .any(|m| m.contains("copy is available only for primitive values")));
}

// ---- user-defined struct types ----

fn struct_def(name: &str, fields: Vec<(&str, Type)>) -> TypeDef {
    TypeDef {
        path: CanonicalType {
            package: "test".into(),
            module: vec!["main".into()],
            name: name.into(),
        },
        span: span(),
        kind: TypeDefKind::Struct {
            fields: fields
                .into_iter()
                .map(|(name, ty)| FieldDef {
                    name: name.into(),
                    ty,
                })
                .collect(),
        },
    }
}
fn ins(output: Option<u32>, kind: InstructionKind) -> Instruction {
    Instruction {
        span: Some(span()),
        output: output.map(ValueId),
        kind,
    }
}
fn val(id: u32, mode: UseMode) -> Operand {
    operand(Source::Value(ValueId(id)), mode)
}
fn loc(id: u32, mode: UseMode) -> Operand {
    operand(Source::Local(LocalId(id)), mode)
}

/// `type P { x: i32, y: i32 }` and a function building one, binding it to the
/// local `p`, then reading field `y` through a field address and a load.
fn struct_program() -> Program {
    let mut f = function();
    f.signature.result = Box::new(Type::Primitive(Primitive::Unit));
    f.locals = vec![Local {
        name: "p".into(),
        ty: Type::Struct(TypeId(0)),
        mutable: false,
        span: span(),
    }];
    f.values = vec![
        i32_ty(),
        i32_ty(),
        Type::Struct(TypeId(0)),
        Type::Reference {
            access: Access::Borrow,
            inner: Box::new(i32_ty()),
        },
        i32_ty(),
    ];
    f.blocks[0].instructions = vec![
        ins(
            Some(0),
            InstructionKind::Constant(Constant::Integer("1".into())),
        ),
        ins(
            Some(1),
            InstructionKind::Constant(Constant::Integer("2".into())),
        ),
        ins(
            Some(2),
            InstructionKind::StructNew {
                ty: TypeId(0),
                fields: vec![val(0, UseMode::Consume), val(1, UseMode::Consume)],
            },
        ),
        ins(
            None,
            InstructionKind::Assign {
                target: LocalId(0),
                value: val(2, UseMode::Consume),
                initialize: true,
            },
        ),
        ins(
            Some(3),
            InstructionKind::FieldAddr {
                loan: LoanId(0),
                base: loc(0, UseMode::Borrow),
                field: 1,
                access: Access::Borrow,
            },
        ),
        ins(
            Some(4),
            InstructionKind::Load {
                reference: val(3, UseMode::Borrow),
            },
        ),
    ];
    f.blocks[0].terminator.kind = TerminatorKind::Return(None);
    Program {
        functions: vec![f],
        types: vec![struct_def("P", vec![("x", i32_ty()), ("y", i32_ty())])],
    }
}
fn struct_errors(edit: impl FnOnce(&mut Program)) -> Vec<String> {
    let mut program = struct_program();
    edit(&mut program);
    program
        .validate()
        .unwrap_err()
        .into_iter()
        .map(|e| e.message)
        .collect()
}
fn has(errors: &[String], needle: &str) -> bool {
    errors.iter().any(|e| e.contains(needle))
}

#[test]
fn accepts_struct_creation_field_address_and_load() {
    assert_eq!(struct_program().validate(), Ok(()));
}

#[test]
fn rejects_out_of_range_struct_type_ids() {
    let errors = struct_errors(|p| {
        p.functions[0].locals[0].ty = Type::Struct(TypeId(7));
    });
    assert!(has(&errors, "out of range"), "{errors:?}");
    let errors = struct_errors(|p| {
        p.functions[0].blocks[0].instructions[2].kind = InstructionKind::StructNew {
            ty: TypeId(7),
            fields: vec![val(0, UseMode::Consume), val(1, UseMode::Consume)],
        };
    });
    assert!(has(&errors, "out of range"), "{errors:?}");
}

#[test]
fn rejects_invalid_struct_creation() {
    let errors = struct_errors(|p| {
        p.functions[0].blocks[0].instructions[2].kind = InstructionKind::StructNew {
            ty: TypeId(0),
            fields: vec![val(0, UseMode::Consume)],
        };
    });
    assert!(has(&errors, "operand count"), "{errors:?}");
    let errors = struct_errors(|p| {
        p.functions[0].values[1] = Type::Primitive(Primitive::Bool);
        p.functions[0].blocks[0].instructions[1].kind =
            InstructionKind::Constant(Constant::Bool(true));
    });
    assert!(
        has(&errors, "differs from the declared field type"),
        "{errors:?}"
    );
    let errors = struct_errors(|p| {
        if let InstructionKind::StructNew { fields, .. } =
            &mut p.functions[0].blocks[0].instructions[2].kind
        {
            fields[0].mode = UseMode::Read;
        }
    });
    assert!(has(&errors, "must be consumed"), "{errors:?}");
    let errors = struct_errors(|p| {
        p.functions[0].values[2] = i32_ty();
    });
    assert!(has(&errors, "created struct type"), "{errors:?}");
}

#[test]
fn rejects_invalid_field_addresses() {
    let errors = struct_errors(|p| {
        if let InstructionKind::FieldAddr { field, .. } =
            &mut p.functions[0].blocks[0].instructions[4].kind
        {
            *field = 2;
        }
    });
    assert!(has(&errors, "field index 2 is out of range"), "{errors:?}");
    let errors = struct_errors(|p| {
        p.functions[0].values[3] = Type::Reference {
            access: Access::Borrow,
            inner: Box::new(Type::Primitive(Primitive::Bool)),
        };
    });
    assert!(has(&errors, "output type is incompatible"), "{errors:?}");
    let errors = struct_errors(|p| {
        if let InstructionKind::FieldAddr { base, .. } =
            &mut p.functions[0].blocks[0].instructions[4].kind
        {
            base.mode = UseMode::Share;
        }
    });
    assert!(has(&errors, "base mode"), "{errors:?}");
    let errors = struct_errors(|p| {
        if let InstructionKind::FieldAddr { base, .. } =
            &mut p.functions[0].blocks[0].instructions[4].kind
        {
            *base = val(0, UseMode::Borrow);
        }
    });
    assert!(has(&errors, "must be a struct owner"), "{errors:?}");
    let errors = struct_errors(|p| {
        if let InstructionKind::FieldAddr { loan, .. } =
            &mut p.functions[0].blocks[0].instructions[4].kind
        {
            *loan = LoanId(0);
        }
        // A second field address reusing loan 0.
        let duplicate = p.functions[0].blocks[0].instructions[4].clone();
        p.functions[0].values.push(Type::Reference {
            access: Access::Borrow,
            inner: Box::new(i32_ty()),
        });
        let mut duplicate = duplicate;
        duplicate.output = Some(ValueId(5));
        p.functions[0].blocks[0].instructions.push(duplicate);
    });
    assert!(
        has(&errors, "loan ID is defined more than once"),
        "{errors:?}"
    );
}

#[test]
fn rejects_unsupported_struct_shapes() {
    // A whole-struct load is never valid, and a reference never refers to a reference.
    let errors = struct_errors(|p| {
        let f = &mut p.functions[0];
        f.values[3] = Type::Reference {
            access: Access::Borrow,
            inner: Box::new(Type::Struct(TypeId(0))),
        };
    });
    assert!(has(&errors, "output type is incompatible"), "{errors:?}");
    let errors = struct_errors(|p| {
        let f = &mut p.functions[0];
        f.values[3] = Type::Reference {
            access: Access::Borrow,
            inner: Box::new(Type::Reference {
                access: Access::Borrow,
                inner: Box::new(Type::Struct(TypeId(0))),
            }),
        };
    });
    assert!(has(&errors, "must refer to"), "{errors:?}");
}

#[test]
fn accepts_struct_signatures_references_and_block_parameters() {
    let struct_ty = Type::Struct(TypeId(0));
    let mut program = struct_program();
    {
        let f = &mut program.functions[0];
        // fn f(a: P, b: borrow P, c: share P) -> P
        for (access, local_ty) in [
            (Access::Owned, struct_ty.clone()),
            (
                Access::Borrow,
                Type::Reference {
                    access: Access::Borrow,
                    inner: Box::new(struct_ty.clone()),
                },
            ),
            (
                Access::Share,
                Type::Reference {
                    access: Access::Share,
                    inner: Box::new(struct_ty.clone()),
                },
            ),
        ] {
            f.signature.parameters.push(ParameterType {
                access,
                ty: struct_ty.clone(),
            });
            f.locals.push(Local {
                name: "q".into(),
                ty: local_ty,
                mutable: false,
                span: span(),
            });
            f.parameter_locals.push(LocalId(f.locals.len() as u32 - 1));
        }
        *f.signature.result = struct_ty.clone();
        f.blocks[0].terminator.kind = TerminatorKind::Unreachable;
        // A struct-typed block parameter.
        f.values.push(struct_ty.clone());
        f.blocks.push(Block {
            parameters: vec![ValueId(5)],
            instructions: vec![],
            terminator: Terminator {
                span: None,
                kind: TerminatorKind::Unreachable,
            },
        });
        // A field address through a share reference parameter, at Share access.
        f.values.push(Type::Reference {
            access: Access::Share,
            inner: Box::new(i32_ty()),
        });
        f.blocks[0].instructions.push(ins(
            Some(6),
            InstructionKind::FieldAddr {
                loan: LoanId(1),
                base: loc(3, UseMode::Share),
                field: 0,
                access: Access::Share,
            },
        ));
    }
    assert_eq!(program.validate(), Ok(()));
    // A borrow reference cannot be strengthened into a share field address.
    let mut weaker = program.clone();
    if let InstructionKind::FieldAddr { base, .. } =
        &mut weaker.functions[0].blocks[0].instructions[6].kind
    {
        *base = loc(2, UseMode::Share);
    }
    let errors: Vec<_> = weaker
        .validate()
        .unwrap_err()
        .into_iter()
        .map(|e| e.message)
        .collect();
    assert!(
        has(&errors, "cannot strengthen reference access"),
        "{errors:?}"
    );
}

#[test]
fn rejects_invalid_struct_definitions() {
    // Recursive and nested aggregate fields cannot be represented.
    let errors = struct_errors(|p| {
        p.types
            .push(struct_def("Node", vec![("next", Type::Struct(TypeId(1)))]));
    });
    assert!(has(&errors, "must be a non-Unit primitive"), "{errors:?}");
    let errors = struct_errors(|p| {
        p.types[0] = struct_def(
            "P",
            vec![
                ("x", i32_ty()),
                (
                    "y",
                    Type::Array {
                        element: Box::new(i32_ty()),
                        len: 2,
                    },
                ),
            ],
        );
    });
    assert!(has(&errors, "must be a non-Unit primitive"), "{errors:?}");
    let errors = struct_errors(|p| {
        p.types[0] = struct_def("P", vec![("x", i32_ty()), ("x", i32_ty())]);
    });
    assert!(has(&errors, "more than once"), "{errors:?}");
    let errors = struct_errors(|p| {
        p.types.push(p.types[0].clone());
    });
    assert!(has(&errors, "duplicate canonical type path"), "{errors:?}");
    let errors = struct_errors(|p| {
        p.types[0].path.name = String::new();
    });
    assert!(has(&errors, "invalid canonical type path"), "{errors:?}");
    let errors = struct_errors(|p| {
        p.types[0] = struct_def("P", vec![("x", Type::Primitive(Primitive::Unit))]);
    });
    assert!(has(&errors, "must be a non-Unit primitive"), "{errors:?}");
}

#[test]
fn nominal_struct_types_with_equal_fields_are_distinct() {
    // Assigning a `Q` value to a local of type `P` is a type mismatch.
    let errors = struct_errors(|p| {
        p.types
            .push(struct_def("Q", vec![("x", i32_ty()), ("y", i32_ty())]));
        p.functions[0].values[2] = Type::Struct(TypeId(1));
        p.functions[0].blocks[0].instructions[2].kind = InstructionKind::StructNew {
            ty: TypeId(1),
            fields: vec![val(0, UseMode::Consume), val(1, UseMode::Consume)],
        };
    });
    assert!(
        has(&errors, "assignment value type differs from local type"),
        "{errors:?}"
    );
}
