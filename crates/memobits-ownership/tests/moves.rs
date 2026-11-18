use memobits_diagnostics::{SourceId, Span};
use memobits_ir::*;
use memobits_ownership::check_moves;

fn span(at: usize) -> Span {
    Span {
        source: SourceId(7),
        start: at,
        end: at + 1,
    }
}
fn ty() -> Type {
    Type::Primitive(Primitive::I32)
}
fn local(id: u32, mode: UseMode, at: usize) -> Operand {
    Operand {
        source: Source::Local(LocalId(id)),
        mode,
        span: Some(span(at)),
    }
}
fn value(id: u32, mode: UseMode, at: usize) -> Operand {
    Operand {
        source: Source::Value(ValueId(id)),
        mode,
        span: Some(span(at)),
    }
}
fn edge(target: u32) -> Edge {
    Edge {
        target: BlockId(target),
        arguments: vec![],
    }
}
fn term(kind: TerminatorKind) -> Terminator {
    Terminator { span: None, kind }
}
fn block(instructions: Vec<Instruction>, end: TerminatorKind) -> Block {
    Block {
        parameters: vec![],
        instructions,
        terminator: term(end),
    }
}
fn assign(target: u32, source: Operand) -> Instruction {
    Instruction {
        span: Some(span(0)),
        output: None,
        kind: InstructionKind::Assign {
            target: LocalId(target),
            value: source,
            initialize: true,
        },
    }
}
fn consume(source: Operand) -> Instruction {
    assign(1, source)
}
fn base() -> Function {
    Function {
        path: CanonicalFunction {
            package: "test".into(),
            module: vec!["main".into()],
            name: "run".into(),
        },
        span: span(0),
        signature: Signature {
            parameters: vec![ParameterType {
                access: Access::Owned,
                ty: ty(),
            }],
            result: Box::new(Type::Primitive(Primitive::Unit)),
        },
        parameter_locals: vec![LocalId(0)],
        locals: vec![
            Local {
                name: "x".into(),
                ty: ty(),
                mutable: true,
                span: span(1),
            },
            Local {
                name: "y".into(),
                ty: ty(),
                mutable: true,
                span: span(2),
            },
        ],
        values: vec![],
        blocks: vec![block(vec![], TerminatorKind::Return(None))],
        entry: BlockId(0),
    }
}
fn codes(function: Function) -> Vec<String> {
    let program = Program {
        functions: vec![function],
        ..Program::default()
    };
    check_moves(&program)
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

#[test]
fn reads_do_not_consume_but_second_consume_fails() {
    let mut f = base();
    f.blocks[0].instructions = vec![
        consume(local(0, UseMode::Read, 10)),
        consume(local(0, UseMode::Read, 11)),
        consume(local(0, UseMode::Consume, 12)),
        consume(local(0, UseMode::Consume, 13)),
    ];
    let diagnostics = check_moves(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].code.to_string(), "BE001");
    assert_eq!(diagnostics[0].span.unwrap().start, 13);
}

#[test]
fn branch_move_reaches_join_and_unreachable_block_is_ignored() {
    let mut f = base();
    f.values.push(Type::Primitive(Primitive::Bool));
    f.blocks = vec![
        block(
            vec![Instruction {
                span: Some(span(3)),
                output: Some(ValueId(0)),
                kind: InstructionKind::Constant(Constant::Bool(true)),
            }],
            TerminatorKind::Branch {
                condition: value(0, UseMode::Read, 4),
                then_edge: edge(1),
                else_edge: edge(2),
            },
        ),
        block(
            vec![consume(local(0, UseMode::Consume, 5))],
            TerminatorKind::Goto(edge(3)),
        ),
        block(vec![], TerminatorKind::Goto(edge(3))),
        block(
            vec![consume(local(0, UseMode::Read, 6))],
            TerminatorKind::Return(None),
        ),
        block(
            vec![
                consume(local(0, UseMode::Consume, 7)),
                consume(local(0, UseMode::Consume, 8)),
            ],
            TerminatorKind::Return(None),
        ),
    ];
    let diagnostics = check_moves(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].span.unwrap().start, 6);
}

#[test]
fn branch_edges_transfer_the_same_owner_independently() {
    let mut f = base();
    f.signature.parameters[0].ty = Type::String;
    f.locals[0].ty = Type::String;
    f.locals[1].ty = Type::String;
    f.values = vec![Type::Primitive(Primitive::Bool), Type::String];
    f.blocks = vec![
        block(
            vec![Instruction {
                span: Some(span(3)),
                output: Some(ValueId(0)),
                kind: InstructionKind::Constant(Constant::Bool(true)),
            }],
            TerminatorKind::Branch {
                condition: value(0, UseMode::Read, 4),
                then_edge: Edge {
                    target: BlockId(1),
                    arguments: vec![local(0, UseMode::Consume, 5)],
                },
                else_edge: Edge {
                    target: BlockId(1),
                    arguments: vec![local(0, UseMode::Consume, 6)],
                },
            },
        ),
        Block {
            parameters: vec![ValueId(1)],
            ..block(
                vec![
                    consume(value(1, UseMode::Consume, 7)),
                    consume(local(0, UseMode::Consume, 8)),
                ],
                TerminatorKind::Return(None),
            )
        },
    ];
    let diagnostics = check_moves(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].code.to_string(), "BE001");
    assert_eq!(diagnostics[0].span.unwrap().start, 8);
}

#[test]
fn loop_backedge_reaches_fixed_point() {
    let mut f = base();
    f.values.push(Type::Primitive(Primitive::Bool));
    f.blocks = vec![
        block(vec![], TerminatorKind::Goto(edge(1))),
        block(
            vec![Instruction {
                span: Some(span(2)),
                output: Some(ValueId(0)),
                kind: InstructionKind::Constant(Constant::Bool(true)),
            }],
            TerminatorKind::Branch {
                condition: value(0, UseMode::Read, 3),
                then_edge: edge(2),
                else_edge: edge(3),
            },
        ),
        block(
            vec![consume(local(0, UseMode::Consume, 4))],
            TerminatorKind::Goto(edge(1)),
        ),
        block(
            vec![consume(local(0, UseMode::Read, 5))],
            TerminatorKind::Return(None),
        ),
    ];
    let diagnostics = check_moves(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert!(
        diagnostics
            .iter()
            .any(|d| d.code.to_string() == "BE001" && d.span.unwrap().start == 5),
        "{diagnostics:?}"
    );
}

#[test]
fn assignment_restores_after_rhs_and_shadow_ids_are_separate() {
    let mut f = base();
    f.blocks[0].instructions = vec![
        consume(local(0, UseMode::Consume, 1)),
        assign(0, local(0, UseMode::Consume, 2)),
        assign(0, local(1, UseMode::Read, 3)),
        assign(1, local(0, UseMode::Read, 4)),
    ];
    let diagnostics = check_moves(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert_eq!(
        diagnostics
            .iter()
            .map(|d| d.span.unwrap().start)
            .collect::<Vec<_>>(),
        [2]
    );

    let mut f = base();
    f.locals[1].name = "x".into();
    f.blocks[0].instructions = vec![
        consume(local(0, UseMode::Consume, 5)),
        assign(1, local(0, UseMode::Read, 6)),
        consume(local(1, UseMode::Read, 7)),
    ];
    let diagnostics = check_moves(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert_eq!(
        diagnostics
            .iter()
            .map(|d| d.span.unwrap().start)
            .collect::<Vec<_>>(),
        [6]
    );
}

#[test]
fn temporary_values_cannot_be_consumed_twice() {
    let mut f = base();
    f.values.push(ty());
    f.blocks[0].instructions = vec![
        Instruction {
            span: Some(span(1)),
            output: Some(ValueId(0)),
            kind: InstructionKind::Constant(Constant::Integer("1".into())),
        },
        consume(value(0, UseMode::Consume, 2)),
        consume(value(0, UseMode::Consume, 3)),
    ];
    let diagnostics = check_moves(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].span.unwrap().start, 3);
}

#[test]
fn borrowing_checks_availability_and_malformed_ir_is_reported() {
    let mut f = base();
    f.blocks[0].instructions = vec![consume(local(0, UseMode::Borrow, 4))];
    assert!(codes(f).is_empty());

    let mut f = base();
    f.entry = BlockId(99);
    assert!(codes(f).contains(&"BE003".into()));
}

#[test]
fn reassignment_to_immutable_local_is_rejected() {
    let mut f = base();
    f.locals[1].mutable = false;
    f.blocks[0].instructions = vec![Instruction {
        span: Some(span(18)),
        output: None,
        kind: InstructionKind::Assign {
            target: LocalId(1),
            value: local(0, UseMode::Read, 19),
            initialize: false,
        },
    }];

    let diagnostics = check_moves(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].code.to_string(), "BE004");
    assert_eq!(diagnostics[0].span.unwrap().start, 18);
}

fn copy_into(output: u32, source: Operand) -> Instruction {
    Instruction {
        span: Some(span(0)),
        output: Some(ValueId(output)),
        kind: InstructionKind::Copy { source },
    }
}

#[test]
fn copy_reads_its_source_and_is_rejected_after_a_move() {
    let mut f = base();
    f.values = vec![ty(), ty()];
    f.blocks[0].instructions = vec![
        copy_into(0, local(0, UseMode::Read, 10)),
        copy_into(1, local(0, UseMode::Read, 11)),
        consume(value(0, UseMode::Consume, 12)),
        consume(local(0, UseMode::Consume, 13)),
    ];
    let first = check_moves(&Program {
        functions: vec![f.clone()],
        ..Program::default()
    });
    assert!(first.is_empty(), "{first:?}");
    f.values.push(ty());
    f.blocks[0]
        .instructions
        .push(copy_into(2, local(0, UseMode::Read, 14)));
    let diagnostics = check_moves(&Program {
        functions: vec![f],
        ..Program::default()
    });
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].code.to_string(), "BE001");
    assert_eq!(diagnostics[0].span.unwrap().start, 14);
}
