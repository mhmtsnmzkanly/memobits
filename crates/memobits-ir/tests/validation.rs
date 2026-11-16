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
