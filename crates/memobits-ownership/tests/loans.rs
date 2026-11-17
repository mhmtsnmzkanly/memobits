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
fn bool_ty() -> Type {
    Type::Primitive(Primitive::Bool)
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
fn live_borrow_blocks_owner_write_until_last_use() {
    let (param, owner) = owned_i32("owner", true);
    let f = function(
        "live",
        vec![param],
        vec![owner],
        vec![reference(Access::Borrow), i32_ty(), i32_ty()],
        vec![block(
            &[],
            vec![
                ins(
                    10,
                    Some(0),
                    InstructionKind::Borrow {
                        loan: LoanId(0),
                        owner: local(0, UseMode::Borrow, 10),
                        access: Access::Borrow,
                    },
                ),
                ins(
                    11,
                    Some(1),
                    InstructionKind::Constant(Constant::Integer("2".into())),
                ),
                ins(
                    12,
                    None,
                    InstructionKind::Assign {
                        target: LocalId(0),
                        value: value(1, UseMode::Consume, 12),
                        initialize: false,
                    },
                ),
                ins(
                    13,
                    Some(2),
                    InstructionKind::Load {
                        reference: value(0, UseMode::Borrow, 13),
                    },
                ),
            ],
            TerminatorKind::Return(None),
        )],
    );
    let diagnostics = check_loans(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert!(
        diagnostics
            .iter()
            .any(|d| d.code.to_string() == "BE005" && d.span.unwrap().start == 12),
        "{diagnostics:?}"
    );

    let (param, owner) = owned_i32("owner", true);
    let f = function(
        "ended",
        vec![param],
        vec![owner],
        vec![reference(Access::Borrow), i32_ty(), i32_ty()],
        vec![block(
            &[],
            vec![
                ins(
                    20,
                    Some(0),
                    InstructionKind::Borrow {
                        loan: LoanId(0),
                        owner: local(0, UseMode::Borrow, 20),
                        access: Access::Borrow,
                    },
                ),
                ins(
                    21,
                    Some(1),
                    InstructionKind::Load {
                        reference: value(0, UseMode::Borrow, 21),
                    },
                ),
                ins(
                    22,
                    Some(2),
                    InstructionKind::Constant(Constant::Integer("2".into())),
                ),
                ins(
                    23,
                    None,
                    InstructionKind::Assign {
                        target: LocalId(0),
                        value: value(2, UseMode::Consume, 23),
                        initialize: false,
                    },
                ),
            ],
            TerminatorKind::Return(None),
        )],
    );
    assert!(codes(vec![f]).is_empty());
}

#[test]
fn forwarded_reborrow_keeps_ancestor_live() {
    let (param, owner) = owned_i32("owner", true);
    let f = function(
        "reborrow",
        vec![param],
        vec![owner],
        vec![
            reference(Access::Borrow),
            reference(Access::Borrow),
            reference(Access::Borrow),
            i32_ty(),
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
                        owner: local(0, UseMode::Borrow, 30),
                        access: Access::Borrow,
                    },
                ),
                ins(
                    31,
                    Some(1),
                    InstructionKind::Capture(value(0, UseMode::Borrow, 31)),
                ),
                ins(
                    32,
                    Some(2),
                    InstructionKind::Borrow {
                        loan: LoanId(1),
                        owner: value(1, UseMode::Borrow, 32),
                        access: Access::Borrow,
                    },
                ),
                ins(
                    33,
                    Some(3),
                    InstructionKind::Constant(Constant::Integer("2".into())),
                ),
                ins(
                    34,
                    None,
                    InstructionKind::Assign {
                        target: LocalId(0),
                        value: value(3, UseMode::Consume, 34),
                        initialize: false,
                    },
                ),
                ins(
                    35,
                    Some(4),
                    InstructionKind::Load {
                        reference: value(2, UseMode::Borrow, 35),
                    },
                ),
            ],
            TerminatorKind::Return(None),
        )],
    );
    let diagnostics = check_loans(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert!(
        diagnostics
            .iter()
            .any(|d| d.code.to_string() == "BE005" && d.span.unwrap().start == 34),
        "{diagnostics:?}"
    );
}

#[test]
fn branch_join_unions_possible_owner_origins() {
    let (x, x_local) = owned_i32("x", true);
    let (y, y_local) = owned_i32("y", true);
    let cond = ParameterType {
        access: Access::Owned,
        ty: bool_ty(),
    };
    let f = function(
        "branch",
        vec![x, y, cond],
        vec![x_local, y_local, local_slot("condition", bool_ty(), false)],
        vec![
            reference(Access::Borrow),
            reference(Access::Borrow),
            reference(Access::Borrow),
            i32_ty(),
            i32_ty(),
        ],
        vec![
            block(
                &[],
                vec![],
                TerminatorKind::Branch {
                    condition: local(2, UseMode::Read, 40),
                    then_edge: edge(1, vec![]),
                    else_edge: edge(2, vec![]),
                },
            ),
            block(
                &[],
                vec![ins(
                    41,
                    Some(0),
                    InstructionKind::Borrow {
                        loan: LoanId(0),
                        owner: local(0, UseMode::Borrow, 41),
                        access: Access::Borrow,
                    },
                )],
                TerminatorKind::Goto(edge(3, vec![value(0, UseMode::Borrow, 42)])),
            ),
            block(
                &[],
                vec![ins(
                    43,
                    Some(1),
                    InstructionKind::Borrow {
                        loan: LoanId(1),
                        owner: local(1, UseMode::Borrow, 43),
                        access: Access::Borrow,
                    },
                )],
                TerminatorKind::Goto(edge(3, vec![value(1, UseMode::Borrow, 44)])),
            ),
            block(
                &[2],
                vec![
                    ins(
                        45,
                        Some(3),
                        InstructionKind::Constant(Constant::Integer("5".into())),
                    ),
                    ins(
                        46,
                        None,
                        InstructionKind::Assign {
                            target: LocalId(0),
                            value: value(3, UseMode::Consume, 46),
                            initialize: false,
                        },
                    ),
                    ins(
                        47,
                        Some(4),
                        InstructionKind::Load {
                            reference: value(2, UseMode::Borrow, 47),
                        },
                    ),
                ],
                TerminatorKind::Return(None),
            ),
        ],
    );
    let diagnostics = check_loans(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert!(
        diagnostics
            .iter()
            .any(|d| d.code.to_string() == "BE005" && d.span.unwrap().start == 46),
        "{diagnostics:?}"
    );
}

#[test]
fn share_store_is_allowed_through_its_handle_but_not_with_competing_borrow() {
    let (param, owner) = owned_i32("owner", true);
    let f = function(
        "store",
        vec![param.clone()],
        vec![owner.clone()],
        vec![reference(Access::Share), i32_ty()],
        vec![block(
            &[],
            vec![
                ins(
                    50,
                    Some(0),
                    InstructionKind::Borrow {
                        loan: LoanId(0),
                        owner: local(0, UseMode::Share, 50),
                        access: Access::Share,
                    },
                ),
                ins(
                    51,
                    Some(1),
                    InstructionKind::Constant(Constant::Integer("5".into())),
                ),
                ins(
                    52,
                    None,
                    InstructionKind::Store {
                        reference: value(0, UseMode::Share, 52),
                        value: value(1, UseMode::Consume, 52),
                    },
                ),
            ],
            TerminatorKind::Return(None),
        )],
    );
    assert!(codes(vec![f]).is_empty());

    let f = function(
        "conflict",
        vec![param],
        vec![owner],
        vec![
            reference(Access::Share),
            reference(Access::Borrow),
            i32_ty(),
            i32_ty(),
        ],
        vec![block(
            &[],
            vec![
                ins(
                    53,
                    Some(0),
                    InstructionKind::Borrow {
                        loan: LoanId(0),
                        owner: local(0, UseMode::Share, 53),
                        access: Access::Share,
                    },
                ),
                ins(
                    54,
                    Some(1),
                    InstructionKind::Borrow {
                        loan: LoanId(1),
                        owner: local(0, UseMode::Borrow, 54),
                        access: Access::Borrow,
                    },
                ),
                ins(
                    55,
                    Some(2),
                    InstructionKind::Constant(Constant::Integer("6".into())),
                ),
                ins(
                    56,
                    None,
                    InstructionKind::Store {
                        reference: value(0, UseMode::Share, 56),
                        value: value(2, UseMode::Consume, 56),
                    },
                ),
                ins(
                    57,
                    Some(3),
                    InstructionKind::Load {
                        reference: value(1, UseMode::Borrow, 57),
                    },
                ),
            ],
            TerminatorKind::Return(None),
        )],
    );
    assert!(codes(vec![f]).contains(&"BE005".into()));
}

#[test]
fn borrowed_call_argument_ends_at_call_and_share_requires_mutable_owner() {
    let borrow_callee = function(
        "read",
        vec![ParameterType {
            access: Access::Borrow,
            ty: i32_ty(),
        }],
        vec![local_slot("value", reference(Access::Borrow), false)],
        vec![i32_ty()],
        vec![block(
            &[],
            vec![ins(
                60,
                Some(0),
                InstructionKind::Load {
                    reference: local(0, UseMode::Borrow, 60),
                },
            )],
            TerminatorKind::Return(None),
        )],
    );
    let (param, owner) = owned_i32("owner", true);
    let caller = function(
        "caller",
        vec![param],
        vec![owner],
        vec![
            reference(Access::Borrow),
            Type::Primitive(Primitive::Unit),
            i32_ty(),
        ],
        vec![block(
            &[],
            vec![
                ins(
                    61,
                    Some(0),
                    InstructionKind::Borrow {
                        loan: LoanId(0),
                        owner: local(0, UseMode::Borrow, 61),
                        access: Access::Borrow,
                    },
                ),
                ins(
                    62,
                    Some(1),
                    InstructionKind::Call {
                        callee: operand(Source::Function(FunctionId(1)), UseMode::Read, 62),
                        arguments: vec![value(0, UseMode::Borrow, 62)],
                    },
                ),
                ins(
                    63,
                    Some(2),
                    InstructionKind::Constant(Constant::Integer("3".into())),
                ),
                ins(
                    64,
                    None,
                    InstructionKind::Assign {
                        target: LocalId(0),
                        value: value(2, UseMode::Consume, 64),
                        initialize: false,
                    },
                ),
            ],
            TerminatorKind::Return(None),
        )],
    );
    assert!(codes(vec![caller, borrow_callee]).is_empty());

    let (param, owner) = owned_i32("immutable", false);
    let immutable = function(
        "immutable",
        vec![param],
        vec![owner],
        vec![reference(Access::Share)],
        vec![block(
            &[],
            vec![ins(
                64,
                Some(0),
                InstructionKind::Borrow {
                    loan: LoanId(0),
                    owner: local(0, UseMode::Share, 64),
                    access: Access::Share,
                },
            )],
            TerminatorKind::Return(None),
        )],
    );
    assert!(codes(vec![immutable]).contains(&"BE005".into()));
}

#[test]
fn loop_reentry_with_live_share_site_is_rejected() {
    let (owner_param, owner) = owned_i32("owner", true);
    let cond = ParameterType {
        access: Access::Owned,
        ty: bool_ty(),
    };
    let f = function(
        "loop",
        vec![owner_param, cond],
        vec![owner, local_slot("condition", bool_ty(), false)],
        vec![
            reference(Access::Share),
            reference(Access::Share),
            reference(Access::Share),
            reference(Access::Share),
            i32_ty(),
        ],
        vec![
            block(
                &[],
                vec![ins(
                    70,
                    Some(0),
                    InstructionKind::Borrow {
                        loan: LoanId(9),
                        owner: local(0, UseMode::Share, 70),
                        access: Access::Share,
                    },
                )],
                TerminatorKind::Goto(edge(1, vec![value(0, UseMode::Share, 70)])),
            ),
            block(
                &[1],
                vec![],
                TerminatorKind::Branch {
                    condition: local(1, UseMode::Read, 71),
                    then_edge: edge(2, vec![value(1, UseMode::Share, 71)]),
                    else_edge: edge(3, vec![]),
                },
            ),
            block(
                &[2],
                vec![
                    ins(
                        72,
                        Some(3),
                        InstructionKind::Borrow {
                            loan: LoanId(0),
                            owner: local(0, UseMode::Share, 72),
                            access: Access::Share,
                        },
                    ),
                    ins(
                        73,
                        Some(4),
                        InstructionKind::Load {
                            reference: value(2, UseMode::Share, 73),
                        },
                    ),
                ],
                TerminatorKind::Goto(edge(1, vec![value(3, UseMode::Share, 74)])),
            ),
            block(&[], vec![], TerminatorKind::Return(None)),
        ],
    );
    let diagnostics = check_loans(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert!(
        diagnostics
            .iter()
            .any(|d| d.code.to_string() == "BE005" && d.message.contains("re-entered")),
        "{diagnostics:?}"
    );
}

#[test]
fn move_pass_accepts_supported_borrow_modes() {
    let (param, owner) = owned_i32("owner", true);
    let f = function(
        "legacy",
        vec![param],
        vec![owner],
        vec![reference(Access::Borrow)],
        vec![block(
            &[],
            vec![ins(
                80,
                Some(0),
                InstructionKind::Borrow {
                    loan: LoanId(0),
                    owner: local(0, UseMode::Borrow, 80),
                    access: Access::Borrow,
                },
            )],
            TerminatorKind::Return(None),
        )],
    );
    let program = Program {
        functions: vec![f],
        ..Program::default()
    };
    assert!(memobits_ownership::check_moves(&program).is_empty());
    assert!(check_loans(&program).is_empty());
}

#[test]
fn malformed_control_flow_is_rejected_before_loan_analysis() {
    let f = function(
        "malformed",
        vec![],
        vec![],
        vec![],
        vec![block(&[], vec![], TerminatorKind::Goto(edge(1, vec![])))],
    );
    let diagnostics = check_loans(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert!(
        diagnostics.iter().any(|d| d.code.to_string() == "BE003"),
        "{diagnostics:?}"
    );
}

#[test]
fn branch_operand_cannot_read_owner_during_live_share_loan() {
    let owner_ty = bool_ty();
    let owner_param = ParameterType {
        access: Access::Owned,
        ty: owner_ty.clone(),
    };
    let ref_bool = Type::Reference {
        access: Access::Share,
        inner: Box::new(owner_ty.clone()),
    };
    let f = function(
        "branch_owner",
        vec![owner_param],
        vec![local_slot("owner", owner_ty, true)],
        vec![ref_bool, bool_ty()],
        vec![
            block(
                &[],
                vec![ins(
                    90,
                    Some(0),
                    InstructionKind::Borrow {
                        loan: LoanId(0),
                        owner: local(0, UseMode::Share, 90),
                        access: Access::Share,
                    },
                )],
                TerminatorKind::Branch {
                    condition: local(0, UseMode::Read, 91),
                    then_edge: edge(1, vec![]),
                    else_edge: edge(2, vec![]),
                },
            ),
            block(
                &[],
                vec![ins(
                    92,
                    Some(1),
                    InstructionKind::Load {
                        reference: value(0, UseMode::Share, 92),
                    },
                )],
                TerminatorKind::Return(None),
            ),
            block(&[], vec![], TerminatorKind::Return(None)),
        ],
    );
    let diagnostics = check_loans(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert!(
        diagnostics.iter().any(|d| d.code.to_string() == "BE005"),
        "{diagnostics:?}"
    );
}

#[test]
fn direct_owner_reads_obey_live_loan_access() {
    for access in [Access::Borrow, Access::Share] {
        for read_after_last_use in [false, true] {
            let (param, owner) = owned_i32("owner", true);
            let read = ins(
                101,
                Some(1),
                InstructionKind::Capture(local(0, UseMode::Read, 101)),
            );
            let load = ins(
                102,
                Some(2),
                InstructionKind::Load {
                    reference: value(
                        0,
                        if access == Access::Share {
                            UseMode::Share
                        } else {
                            UseMode::Borrow
                        },
                        102,
                    ),
                },
            );
            let mut instructions = vec![ins(
                100,
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
                        100,
                    ),
                    access,
                },
            )];
            instructions.extend(if read_after_last_use {
                vec![load, read]
            } else {
                vec![read, load]
            });
            let program = Program {
                functions: vec![function(
                    "read_owner",
                    vec![param],
                    vec![owner],
                    vec![reference(access), i32_ty(), i32_ty()],
                    vec![block(&[], instructions, TerminatorKind::Return(None))],
                )],
                ..Program::default()
            };
            program.validate().unwrap();
            let diagnostics = check_loans(&program);
            assert_eq!(
                diagnostics
                    .iter()
                    .any(|d| d.code.to_string() == "BE005" && d.span.unwrap().start == 101),
                access == Access::Share && !read_after_last_use,
                "{diagnostics:?}"
            );
        }
    }
}

#[test]
fn reference_load_and_reborrow_respect_descendant_access() {
    for child_access in [Access::Borrow, Access::Share] {
        for use_after_child in [false, true] {
            let (param, owner) = owned_i32("owner", true);
            let parent_load = ins(
                112,
                Some(2),
                InstructionKind::Load {
                    reference: value(0, UseMode::Share, 112),
                },
            );
            let child_load = ins(
                113,
                Some(3),
                InstructionKind::Load {
                    reference: value(
                        1,
                        if child_access == Access::Share {
                            UseMode::Share
                        } else {
                            UseMode::Borrow
                        },
                        113,
                    ),
                },
            );
            let mut instructions = vec![
                ins(
                    110,
                    Some(0),
                    InstructionKind::Borrow {
                        loan: LoanId(0),
                        owner: local(0, UseMode::Share, 110),
                        access: Access::Share,
                    },
                ),
                ins(
                    111,
                    Some(1),
                    InstructionKind::Borrow {
                        loan: LoanId(1),
                        owner: value(
                            0,
                            if child_access == Access::Share {
                                UseMode::Share
                            } else {
                                UseMode::Borrow
                            },
                            111,
                        ),
                        access: child_access,
                    },
                ),
            ];
            instructions.extend(if use_after_child {
                vec![child_load, parent_load]
            } else {
                vec![parent_load, child_load]
            });
            let program = Program {
                functions: vec![function(
                    "load_parent",
                    vec![param],
                    vec![owner],
                    vec![
                        reference(Access::Share),
                        reference(child_access),
                        i32_ty(),
                        i32_ty(),
                    ],
                    vec![block(&[], instructions, TerminatorKind::Return(None))],
                )],
                ..Program::default()
            };
            program.validate().unwrap();
            let diagnostics = check_loans(&program);
            assert_eq!(
                diagnostics
                    .iter()
                    .any(|d| d.code.to_string() == "BE005" && d.span.unwrap().start == 112),
                child_access == Access::Share && !use_after_child,
                "{diagnostics:?}"
            );
            assert!(
                !diagnostics
                    .iter()
                    .any(|d| d.span.unwrap().start == 111 || d.span.unwrap().start == 113),
                "{diagnostics:?}"
            );
        }
    }
}

#[test]
fn distinct_reference_parameters_keep_independent_roots() {
    for second_access in [Access::Borrow, Access::Share] {
        let parameters = vec![
            ParameterType {
                access: Access::Share,
                ty: i32_ty(),
            },
            ParameterType {
                access: second_access,
                ty: i32_ty(),
            },
        ];
        let f = function(
            "independent",
            parameters,
            vec![
                local_slot("first", reference(Access::Share), false),
                local_slot("second", reference(second_access), false),
            ],
            vec![i32_ty(), i32_ty()],
            vec![block(
                &[],
                vec![
                    ins(
                        120,
                        Some(0),
                        InstructionKind::Constant(Constant::Integer("7".into())),
                    ),
                    ins(
                        121,
                        None,
                        InstructionKind::Store {
                            reference: local(0, UseMode::Share, 121),
                            value: value(0, UseMode::Consume, 121),
                        },
                    ),
                    ins(
                        122,
                        Some(1),
                        InstructionKind::Load {
                            reference: local(
                                1,
                                if second_access == Access::Share {
                                    UseMode::Share
                                } else {
                                    UseMode::Borrow
                                },
                                122,
                            ),
                        },
                    ),
                ],
                TerminatorKind::Return(None),
            )],
        );
        let program = Program {
            functions: vec![f],
            ..Program::default()
        };
        program.validate().unwrap();
        assert!(
            check_loans(&program).is_empty(),
            "{:?}",
            check_loans(&program)
        );
        assert!(memobits_ownership::check_ownership(&program).is_empty());
    }
}

#[test]
fn combined_gate_reports_structural_failures_once() {
    let f = function(
        "malformed_gate",
        vec![],
        vec![],
        vec![],
        vec![block(&[], vec![], TerminatorKind::Goto(edge(1, vec![])))],
    );
    let program = Program {
        functions: vec![f],
        ..Program::default()
    };
    assert_eq!(
        memobits_ownership::check_ownership(&program),
        memobits_ownership::check_moves(&program)
    );
}

#[test]
fn independent_parameter_contract_is_enforced_at_calls() {
    let callee = function(
        "two_shares",
        vec![
            ParameterType {
                access: Access::Share,
                ty: i32_ty()
            };
            2
        ],
        vec![
            local_slot("first", reference(Access::Share), false),
            local_slot("second", reference(Access::Share), false),
        ],
        vec![],
        vec![block(&[], vec![], TerminatorKind::Return(None))],
    );
    let (param, owner) = owned_i32("owner", true);
    let caller = function(
        "alias_call",
        vec![param],
        vec![owner],
        vec![reference(Access::Share), Type::Primitive(Primitive::Unit)],
        vec![block(
            &[],
            vec![
                ins(
                    129,
                    Some(0),
                    InstructionKind::Borrow {
                        loan: LoanId(0),
                        owner: local(0, UseMode::Share, 129),
                        access: Access::Share,
                    },
                ),
                ins(
                    130,
                    Some(1),
                    InstructionKind::Call {
                        callee: operand(Source::Function(FunctionId(1)), UseMode::Read, 130),
                        arguments: vec![
                            value(0, UseMode::Share, 130),
                            value(0, UseMode::Share, 130),
                        ],
                    },
                ),
            ],
            TerminatorKind::Return(None),
        )],
    );
    let program = Program {
        functions: vec![caller, callee],
        ..Program::default()
    };
    program.validate().unwrap();
    assert!(check_loans(&program)
        .iter()
        .any(|d| d.code.to_string() == "BE005"
            && d.message.contains("another argument of this call")));
}

#[test]
fn reborrow_cannot_bypass_a_live_exclusive_descendant() {
    let (param, owner) = owned_i32("owner", true);
    let f = function(
        "sibling_reborrow",
        vec![param],
        vec![owner],
        vec![
            reference(Access::Share),
            reference(Access::Share),
            reference(Access::Borrow),
            i32_ty(),
        ],
        vec![block(
            &[],
            vec![
                ins(
                    140,
                    Some(0),
                    InstructionKind::Borrow {
                        loan: LoanId(0),
                        owner: local(0, UseMode::Share, 140),
                        access: Access::Share,
                    },
                ),
                ins(
                    141,
                    Some(1),
                    InstructionKind::Borrow {
                        loan: LoanId(1),
                        owner: value(0, UseMode::Share, 141),
                        access: Access::Share,
                    },
                ),
                ins(
                    142,
                    Some(2),
                    InstructionKind::Borrow {
                        loan: LoanId(2),
                        owner: value(0, UseMode::Borrow, 142),
                        access: Access::Borrow,
                    },
                ),
                ins(
                    143,
                    Some(3),
                    InstructionKind::Load {
                        reference: value(1, UseMode::Share, 143),
                    },
                ),
            ],
            TerminatorKind::Return(None),
        )],
    );
    let program = Program {
        functions: vec![f],
        ..Program::default()
    };
    program.validate().unwrap();
    assert!(check_loans(&program)
        .iter()
        .any(|d| d.code.to_string() == "BE005" && d.span.unwrap().start == 142));
}

#[test]
fn share_call_cannot_write_through_immutable_reference_handle_local() {
    let callee = function(
        "write",
        vec![ParameterType {
            access: Access::Share,
            ty: i32_ty(),
        }],
        vec![local_slot("value", reference(Access::Share), false)],
        vec![],
        vec![block(&[], vec![], TerminatorKind::Return(None))],
    );
    for mutable in [false, true] {
        let (param, owner) = owned_i32("owner", true);
        let caller = function(
            "caller",
            vec![param],
            vec![
                owner,
                local_slot("handle", reference(Access::Share), mutable),
            ],
            vec![reference(Access::Share), Type::Primitive(Primitive::Unit)],
            vec![block(
                &[],
                vec![
                    ins(
                        150,
                        Some(0),
                        InstructionKind::Borrow {
                            loan: LoanId(0),
                            owner: local(0, UseMode::Share, 150),
                            access: Access::Share,
                        },
                    ),
                    ins(
                        151,
                        None,
                        InstructionKind::Assign {
                            target: LocalId(1),
                            value: value(0, UseMode::Consume, 151),
                            initialize: true,
                        },
                    ),
                    ins(
                        152,
                        Some(1),
                        InstructionKind::Call {
                            callee: operand(Source::Function(FunctionId(1)), UseMode::Read, 152),
                            arguments: vec![local(1, UseMode::Share, 152)],
                        },
                    ),
                ],
                TerminatorKind::Return(None),
            )],
        );
        let program = Program {
            functions: vec![caller, callee.clone()],
            ..Program::default()
        };
        program.validate().unwrap();
        let diagnostics = memobits_ownership::check_ownership(&program);
        assert_eq!(
            diagnostics
                .iter()
                .any(|d| d.code.to_string() == "BE004" && d.span.unwrap().start == 152),
            !mutable,
            "{diagnostics:?}"
        );
    }
}
