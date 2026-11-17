use memobits_diagnostics::{SourceId, Span};
use memobits_ir::*;
use memobits_ownership::check_ownership;

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
fn owned_i32(name: &str, mutable: bool) -> (ParameterType, Local) {
    (
        ParameterType {
            access: Access::Owned,
            ty: i32_ty(),
        },
        local_slot(name, i32_ty(), mutable),
    )
}

fn run(f: Function) -> Vec<memobits_diagnostics::Diagnostic> {
    let program = Program {
        functions: vec![f],
        ..Program::default()
    };
    assert!(program.validate().is_ok(), "{:?}", program.validate());
    check_ownership(&program)
}
fn borrow(owner: Operand, access: Access, output: u32, at: usize) -> Instruction {
    ins(
        at,
        Some(output),
        InstructionKind::Borrow {
            loan: LoanId(output),
            owner,
            access,
        },
    )
}
fn load(reference: Operand, output: u32, at: usize) -> Instruction {
    ins(at, Some(output), InstructionKind::Load { reference })
}
fn capture(operand: Operand, output: u32, at: usize) -> Instruction {
    ins(at, Some(output), InstructionKind::Capture(operand))
}
fn fixture(access: Access) -> Function {
    let (param, owner) = owned_i32("owner", true);
    function(
        "run",
        vec![param],
        vec![owner],
        vec![reference(access), i32_ty()],
        vec![block(&[], vec![], TerminatorKind::Return(None))],
    )
}
fn has_move_at(ds: &[memobits_diagnostics::Diagnostic], at: usize) -> bool {
    ds.iter()
        .any(|d| d.code.to_string() == "BE001" && d.span == Some(span(at)))
}

#[test]
fn valid_borrow_and_share_handles_check_through_combined_gate() {
    for (access, mode) in [
        (Access::Borrow, UseMode::Borrow),
        (Access::Share, UseMode::Share),
    ] {
        let mut f = fixture(access);
        f.blocks[0].instructions = vec![
            borrow(local(0, mode, 10), access, 0, 10),
            load(value(0, mode, 11), 1, 11),
        ];
        assert!(run(f).is_empty());
    }
}

#[test]
fn reference_parameters_start_available() {
    for access in [Access::Borrow, Access::Share] {
        let f = function(
            "parameter",
            vec![ParameterType {
                access,
                ty: i32_ty(),
            }],
            vec![local_slot("reference", reference(access), true)],
            vec![i32_ty()],
            vec![block(
                &[],
                vec![load(
                    local(
                        0,
                        if access == Access::Share {
                            UseMode::Share
                        } else {
                            UseMode::Borrow
                        },
                        10,
                    ),
                    0,
                    10,
                )],
                TerminatorKind::Return(None),
            )],
        );
        assert!(run(f).is_empty());
    }
}

#[test]
fn borrowing_moved_or_uninitialized_owner_is_rejected() {
    for (access, mode) in [
        (Access::Borrow, UseMode::Borrow),
        (Access::Share, UseMode::Share),
    ] {
        let mut f = fixture(access);
        f.values.push(i32_ty());
        f.blocks[0].instructions = vec![
            capture(local(0, UseMode::Consume, 8), 2, 8),
            borrow(local(0, mode, 10), access, 0, 10),
            load(value(0, mode, 11), 1, 11),
        ];
        assert!(has_move_at(&run(f), 10));
        let mut f = fixture(access);
        f.signature.parameters.clear();
        f.parameter_locals.clear();
        f.blocks[0].instructions = vec![
            borrow(local(0, mode, 12), access, 0, 12),
            load(value(0, mode, 13), 1, 13),
        ];
        assert!(has_move_at(&run(f), 12));
    }
}

#[test]
fn uninitialized_reference_local_is_unavailable() {
    let mut f = fixture(Access::Borrow);
    f.locals
        .push(local_slot("empty", reference(Access::Borrow), false));
    f.blocks[0].instructions = vec![
        borrow(local(0, UseMode::Borrow, 8), Access::Borrow, 0, 8),
        load(local(1, UseMode::Borrow, 10), 1, 10),
    ];
    assert!(has_move_at(&run(f), 10));
}

#[test]
fn consuming_exclusive_handle_moves_it_but_keeps_destination_available() {
    let mut f = fixture(Access::Share);
    f.values.push(reference(Access::Share));
    f.values.push(i32_ty());
    f.blocks[0].instructions = vec![
        borrow(local(0, UseMode::Share, 8), Access::Share, 0, 8),
        capture(value(0, UseMode::Consume, 9), 2, 9),
        load(value(2, UseMode::Share, 10), 1, 10),
        load(value(0, UseMode::Share, 11), 3, 11),
    ];
    let ds = run(f);
    assert!(has_move_at(&ds, 11), "{ds:?}");
    assert!(!has_move_at(&ds, 10), "{ds:?}");
}

#[test]
fn branch_join_does_not_restore_consumed_handle() {
    let mut f = fixture(Access::Share);
    f.values.extend([bool_ty(), reference(Access::Share)]);
    f.blocks = vec![
        block(
            &[],
            vec![
                borrow(local(0, UseMode::Share, 8), Access::Share, 0, 8),
                ins(9, Some(2), InstructionKind::Constant(Constant::Bool(true))),
            ],
            TerminatorKind::Branch {
                condition: value(2, UseMode::Read, 10),
                then_edge: edge(1, vec![]),
                else_edge: edge(2, vec![]),
            },
        ),
        block(
            &[],
            vec![capture(value(0, UseMode::Consume, 11), 3, 11)],
            TerminatorKind::Goto(edge(3, vec![])),
        ),
        block(&[], vec![], TerminatorKind::Goto(edge(3, vec![]))),
        block(
            &[],
            vec![load(value(0, UseMode::Share, 12), 1, 12)],
            TerminatorKind::Return(None),
        ),
    ];
    assert!(has_move_at(&run(f), 12));
}

#[test]
fn loop_backedge_detects_repeated_handle_move() {
    let mut f = fixture(Access::Share);
    f.values.push(reference(Access::Share));
    f.blocks = vec![
        block(
            &[],
            vec![borrow(local(0, UseMode::Share, 8), Access::Share, 0, 8)],
            TerminatorKind::Goto(edge(1, vec![])),
        ),
        block(
            &[],
            vec![
                capture(value(0, UseMode::Consume, 10), 2, 10),
                load(value(2, UseMode::Share, 11), 1, 11),
            ],
            TerminatorKind::Goto(edge(1, vec![])),
        ),
    ];
    assert!(has_move_at(&run(f), 10));
}

#[test]
fn invalid_edge_argument_does_not_initialize_reference_block_parameter() {
    let mut f = fixture(Access::Share);
    f.locals
        .push(local_slot("empty", reference(Access::Share), false));
    f.values.push(reference(Access::Share));
    f.blocks = vec![
        block(
            &[],
            vec![borrow(local(0, UseMode::Share, 8), Access::Share, 0, 8)],
            TerminatorKind::Goto(edge(1, vec![local(1, UseMode::Consume, 10)])),
        ),
        block(
            &[2],
            vec![load(value(2, UseMode::Share, 11), 1, 11)],
            TerminatorKind::Return(None),
        ),
    ];
    let ds = run(f);
    assert!(has_move_at(&ds, 10) && has_move_at(&ds, 11), "{ds:?}");
}

#[test]
fn loop_block_parameter_is_initialized_by_incoming_handle() {
    let mut f = fixture(Access::Share);
    f.values.push(reference(Access::Share));
    f.blocks = vec![
        block(
            &[],
            vec![borrow(local(0, UseMode::Share, 8), Access::Share, 0, 8)],
            TerminatorKind::Goto(edge(1, vec![value(0, UseMode::Consume, 9)])),
        ),
        block(
            &[2],
            vec![load(value(2, UseMode::Share, 10), 1, 10)],
            TerminatorKind::Goto(edge(1, vec![value(2, UseMode::Consume, 11)])),
        ),
    ];
    let ds = run(f);
    assert!(ds.is_empty(), "{ds:?}");
}
