use memobits_diagnostics::{SourceId, Span};
use memobits_ir::*;
use memobits_ownership::check_loans;

fn span(at: usize) -> Span {
    Span {
        source: SourceId(4),
        start: at,
        end: at + 1,
    }
}
fn i32_ty() -> Type {
    Type::Primitive(Primitive::I32)
}
fn reference(access: Access) -> Type {
    Type::Reference {
        access,
        inner: Box::new(i32_ty()),
    }
}
fn operand(source: Source, mode: UseMode, at: usize) -> Operand {
    Operand {
        source,
        mode,
        span: Some(span(at)),
    }
}
fn local(id: u32, mode: UseMode, at: usize) -> Operand {
    operand(Source::Local(LocalId(id)), mode, at)
}
fn value(id: u32, mode: UseMode, at: usize) -> Operand {
    operand(Source::Value(ValueId(id)), mode, at)
}
fn ins(at: usize, output: Option<u32>, kind: InstructionKind) -> Instruction {
    Instruction {
        span: Some(span(at)),
        output: output.map(ValueId),
        kind,
    }
}
fn block(parameters: &[u32], instructions: Vec<Instruction>, kind: TerminatorKind) -> Block {
    Block {
        parameters: parameters.iter().copied().map(ValueId).collect(),
        instructions,
        terminator: Terminator { span: None, kind },
    }
}
fn edge(target: u32, arguments: Vec<Operand>) -> Edge {
    Edge {
        target: BlockId(target),
        arguments,
    }
}
fn function(
    name: &str,
    parameters: Vec<ParameterType>,
    locals: Vec<Local>,
    values: Vec<Type>,
    blocks: Vec<Block>,
) -> Function {
    let parameter_locals = (0..parameters.len()).map(|i| LocalId(i as u32)).collect();
    Function {
        path: CanonicalFunction {
            package: "test".into(),
            module: vec!["main".into()],
            name: name.into(),
        },
        span: span(0),
        signature: Signature {
            parameters,
            result: Box::new(Type::Primitive(Primitive::Unit)),
        },
        parameter_locals,
        locals,
        values,
        blocks,
        entry: BlockId(0),
    }
}
fn local_slot(name: &str, ty: Type, mutable: bool) -> Local {
    Local {
        name: name.into(),
        ty,
        mutable,
        kind: memobits_ir::LocalKind::Ordinary,
        span: span(1),
    }
}
fn codes(functions: Vec<Function>) -> Vec<String> {
    check_loans(&Program {
        functions,
        ..Program::default()
    })
    .iter()
    .map(|d| d.code.to_string())
    .collect()
}
fn owned_i32(name: &str, mutable: bool) -> (ParameterType, Local) {
    (
        ParameterType {
            access: Access::Owned,
            ty: i32_ty(),
        },
        local_slot(name, i32_ty(), mutable),
    )
}

#[test]
fn handle_capture_requires_relocation() {
    for access in [Access::Borrow, Access::Share] {
        for mode in [
            UseMode::Read,
            UseMode::Borrow,
            UseMode::Share,
            UseMode::Consume,
        ] {
            let (param, owner) = owned_i32("owner", true);
            let f = function(
                "transport",
                vec![param],
                vec![owner],
                vec![reference(access), reference(access)],
                vec![block(
                    &[],
                    vec![
                        ins(
                            10,
                            Some(0),
                            InstructionKind::Borrow {
                                loan: LoanId(0),
                                owner: local(
                                    0,
                                    if access == Access::Share {
                                        UseMode::Share
                                    } else {
                                        UseMode::Borrow
                                    },
                                    10,
                                ),
                                access,
                            },
                        ),
                        ins(11, Some(1), InstructionKind::Capture(value(0, mode, 11))),
                    ],
                    TerminatorKind::Return(None),
                )],
            );
            let program = Program {
                functions: vec![f],
                ..Program::default()
            };
            program.validate().unwrap();
            let diagnostics = memobits_ownership::check_ownership(&program);
            assert_eq!(
                diagnostics.is_empty(),
                mode == UseMode::Consume,
                "{access:?} {mode:?}: {diagnostics:?}"
            );
        }
    }
}

#[test]
fn edge_consumption_conflicts_with_live_read_only_loan() {
    let (param, owner) = owned_i32("owner", true);
    let f = function(
        "edge_move",
        vec![param],
        vec![owner],
        vec![reference(Access::Borrow), i32_ty(), i32_ty()],
        vec![
            block(
                &[],
                vec![ins(
                    20,
                    Some(0),
                    InstructionKind::Borrow {
                        loan: LoanId(0),
                        owner: local(0, UseMode::Borrow, 20),
                        access: Access::Borrow,
                    },
                )],
                TerminatorKind::Goto(edge(1, vec![local(0, UseMode::Consume, 21)])),
            ),
            block(
                &[1],
                vec![ins(
                    22,
                    Some(2),
                    InstructionKind::Load {
                        reference: value(0, UseMode::Borrow, 22),
                    },
                )],
                TerminatorKind::Return(None),
            ),
        ],
    );
    assert!(codes(vec![f]).iter().any(|code| code == "BE005"));
}

#[test]
fn parent_relocation_conflicts_with_live_descendant() {
    let (param, owner) = owned_i32("owner", true);
    let f = function(
        "frozen_parent",
        vec![param],
        vec![owner],
        vec![
            reference(Access::Share),
            reference(Access::Borrow),
            reference(Access::Share),
            i32_ty(),
        ],
        vec![block(
            &[],
            vec![
                ins(
                    30,
                    Some(0),
                    InstructionKind::Borrow {
                        loan: LoanId(0),
                        owner: local(0, UseMode::Share, 30),
                        access: Access::Share,
                    },
                ),
                ins(
                    31,
                    Some(1),
                    InstructionKind::Borrow {
                        loan: LoanId(1),
                        owner: value(0, UseMode::Borrow, 31),
                        access: Access::Borrow,
                    },
                ),
                ins(
                    32,
                    Some(2),
                    InstructionKind::Capture(value(0, UseMode::Consume, 32)),
                ),
                ins(
                    33,
                    Some(3),
                    InstructionKind::Load {
                        reference: value(1, UseMode::Borrow, 33),
                    },
                ),
            ],
            TerminatorKind::Return(None),
        )],
    );
    assert!(codes(vec![f]).iter().any(|code| code == "BE005"));
}

#[test]
fn local_handle_binding_controls_target_mutation() {
    for mutable in [false, true] {
        let (param, owner) = owned_i32("owner", true);
        let f = function(
            "local_write",
            vec![param],
            vec![
                owner,
                local_slot("handle", reference(Access::Share), mutable),
            ],
            vec![reference(Access::Share), i32_ty()],
            vec![block(
                &[],
                vec![
                    ins(
                        40,
                        Some(0),
                        InstructionKind::Borrow {
                            loan: LoanId(0),
                            owner: local(0, UseMode::Share, 40),
                            access: Access::Share,
                        },
                    ),
                    ins(
                        41,
                        None,
                        InstructionKind::Assign {
                            target: LocalId(1),
                            value: value(0, UseMode::Consume, 41),
                            initialize: true,
                        },
                    ),
                    ins(
                        42,
                        Some(1),
                        InstructionKind::Constant(Constant::Integer("7".into())),
                    ),
                    ins(
                        43,
                        None,
                        InstructionKind::Store {
                            reference: local(1, UseMode::Share, 43),
                            value: value(1, UseMode::Consume, 43),
                        },
                    ),
                ],
                TerminatorKind::Return(None),
            )],
        );
        let diagnostics = codes(vec![f]);
        assert_eq!(diagnostics.is_empty(), mutable, "{diagnostics:?}");
    }
}

#[test]
fn edge_handle_transport_requires_consume() {
    for mode in [UseMode::Share, UseMode::Consume] {
        let (param, owner) = owned_i32("owner", true);
        let f = function(
            "edge_handle",
            vec![param],
            vec![owner],
            vec![reference(Access::Share), reference(Access::Share)],
            vec![
                block(
                    &[],
                    vec![ins(
                        50,
                        Some(0),
                        InstructionKind::Borrow {
                            loan: LoanId(0),
                            owner: local(0, UseMode::Share, 50),
                            access: Access::Share,
                        },
                    )],
                    TerminatorKind::Goto(edge(1, vec![value(0, mode, 51)])),
                ),
                block(&[1], vec![], TerminatorKind::Return(None)),
            ],
        );
        let diagnostics = codes(vec![f]);
        assert_eq!(
            diagnostics.is_empty(),
            mode == UseMode::Consume,
            "{diagnostics:?}"
        );
    }
}

#[test]
fn local_binding_controls_share_reborrow_but_parameters_allow_it() {
    for access in [Access::Borrow, Access::Share] {
        for mutable in [false, true] {
            let (param, owner) = owned_i32("owner", true);
            let f = function(
                "local_reborrow",
                vec![param],
                vec![
                    owner,
                    local_slot("handle", reference(Access::Share), mutable),
                ],
                vec![reference(Access::Share), reference(access)],
                vec![block(
                    &[],
                    vec![
                        ins(
                            60,
                            Some(0),
                            InstructionKind::Borrow {
                                loan: LoanId(0),
                                owner: local(0, UseMode::Share, 60),
                                access: Access::Share,
                            },
                        ),
                        ins(
                            61,
                            None,
                            InstructionKind::Assign {
                                target: LocalId(1),
                                value: value(0, UseMode::Consume, 61),
                                initialize: true,
                            },
                        ),
                        ins(
                            62,
                            Some(1),
                            InstructionKind::Borrow {
                                loan: LoanId(1),
                                owner: local(
                                    1,
                                    if access == Access::Share {
                                        UseMode::Share
                                    } else {
                                        UseMode::Borrow
                                    },
                                    62,
                                ),
                                access,
                            },
                        ),
                    ],
                    TerminatorKind::Return(None),
                )],
            );
            let diagnostics = codes(vec![f]);
            assert_eq!(
                diagnostics.is_empty(),
                mutable || access == Access::Borrow,
                "{access:?} {mutable}: {diagnostics:?}"
            );
        }
        let f = function(
            "parameter_reborrow",
            vec![ParameterType {
                access: Access::Share,
                ty: i32_ty(),
            }],
            vec![local_slot("parameter", reference(Access::Share), false)],
            vec![reference(access)],
            vec![block(
                &[],
                vec![ins(
                    63,
                    Some(0),
                    InstructionKind::Borrow {
                        loan: LoanId(0),
                        owner: local(
                            0,
                            if access == Access::Share {
                                UseMode::Share
                            } else {
                                UseMode::Borrow
                            },
                            63,
                        ),
                        access,
                    },
                )],
                TerminatorKind::Return(None),
            )],
        );
        assert!(codes(vec![f]).is_empty());
    }
}
