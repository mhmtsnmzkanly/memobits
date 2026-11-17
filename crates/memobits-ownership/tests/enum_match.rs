//! Move and loan checks around `EnumTag`, `Switch` and `VariantExtract`: the
//! scrutinee cell is consumed once per path, payload moves are legal only on
//! the arm's path, and a live reference to the enum blocks the consuming match.
use memobits_diagnostics::{SourceId, Span};
use memobits_ir::*;
use memobits_ownership::{check_loans, check_moves};

fn span(at: usize) -> Span {
    Span {
        source: SourceId(8),
        start: at,
        end: at + 1,
    }
}
fn i32_ty() -> Type {
    Type::Primitive(Primitive::I32)
}
fn enum_ty() -> Type {
    Type::Enum(TypeId(0))
}
fn local(id: u32, mode: UseMode) -> Operand {
    Operand {
        source: Source::Local(LocalId(id)),
        mode,
        span: Some(span(id as usize + 10)),
    }
}
fn value(id: u32, mode: UseMode) -> Operand {
    Operand {
        source: Source::Value(ValueId(id)),
        mode,
        span: Some(span(id as usize + 20)),
    }
}
fn ins(output: Option<u32>, kind: InstructionKind) -> Instruction {
    Instruction {
        span: Some(span(0)),
        output: output.map(ValueId),
        kind,
    }
}
fn assign(target: u32, source: Operand) -> Instruction {
    ins(
        None,
        InstructionKind::Assign {
            target: LocalId(target),
            value: source,
            initialize: true,
        },
    )
}
fn extract(output: u32, variant: u32, mode: UseMode) -> Instruction {
    ins(
        Some(output),
        InstructionKind::VariantExtract {
            base: local(0, mode),
            variant,
            field: 0,
        },
    )
}
fn edge(target: u32) -> Edge {
    Edge {
        target: BlockId(target),
        arguments: vec![],
    }
}
fn block(instructions: Vec<Instruction>, kind: TerminatorKind) -> Block {
    Block {
        parameters: vec![],
        instructions,
        terminator: Terminator { span: None, kind },
    }
}

/// `type E [ A, B(i32) ]`. Local 0 is `e = E::B(1)`, local 1 receives payloads.
/// Value 0 is the constant, 1 the enum, 2 the tag; `tail_values` types the rest.
/// Block 0 builds and switches; block 1 (variant A) and block 2 (variant B)
/// are given by the caller and both continue to the final block 3.
fn program(
    arm_a: Vec<Instruction>,
    arm_b: Vec<Instruction>,
    after: Vec<Instruction>,
    extra_block0: Vec<Instruction>,
    tail_values: Vec<Type>,
) -> Program {
    let mut head = vec![
        ins(
            Some(0),
            InstructionKind::Constant(Constant::Integer("1".into())),
        ),
        ins(
            Some(1),
            InstructionKind::EnumNew {
                ty: TypeId(0),
                variant: 1,
                payload: vec![value(0, UseMode::Consume)],
            },
        ),
        assign(0, value(1, UseMode::Consume)),
    ];
    head.extend(extra_block0);
    head.push(ins(
        Some(2),
        InstructionKind::EnumTag {
            base: local(0, UseMode::Read),
        },
    ));
    Program {
        functions: vec![Function {
            path: CanonicalFunction {
                package: "test".into(),
                module: vec!["main".into()],
                name: "f".into(),
            },
            span: span(0),
            signature: Signature {
                parameters: vec![],
                result: Box::new(Type::Primitive(Primitive::Unit)),
            },
            parameter_locals: vec![],
            locals: vec![
                Local {
                    name: "e".into(),
                    ty: enum_ty(),
                    mutable: true,
                    span: span(1),
                },
                Local {
                    name: "n".into(),
                    ty: i32_ty(),
                    mutable: false,
                    span: span(2),
                },
            ],
            values: [i32_ty(), enum_ty(), Type::Primitive(Primitive::U32)]
                .into_iter()
                .chain(tail_values)
                .collect(),
            blocks: vec![
                block(
                    head,
                    TerminatorKind::Switch {
                        tag: value(2, UseMode::Read),
                        ty: TypeId(0),
                        targets: vec![(0, edge(1)), (1, edge(2))],
                        default: None,
                    },
                ),
                block(arm_a, TerminatorKind::Goto(edge(3))),
                block(arm_b, TerminatorKind::Goto(edge(3))),
                block(after, TerminatorKind::Return(None)),
            ],
            entry: BlockId(0),
        }],
        types: vec![TypeDef {
            path: CanonicalType {
                package: "test".into(),
                module: vec!["main".into()],
                name: "E".into(),
            },
            span: span(0),
            kind: TypeDefKind::Enum {
                variants: vec![
                    VariantDef {
                        name: "A".into(),
                        payload: vec![],
                    },
                    VariantDef {
                        name: "B".into(),
                        payload: vec![i32_ty()],
                    },
                ],
            },
        }],
    }
}

fn moves(p: &Program) -> Vec<String> {
    p.validate().unwrap_or_else(|e| panic!("{e:?}"));
    check_moves(p).iter().map(|d| d.code.to_string()).collect()
}
fn loans(p: &Program) -> Vec<String> {
    p.validate().unwrap_or_else(|e| panic!("{e:?}"));
    check_loans(p).iter().map(|d| d.code.to_string()).collect()
}

fn payload_into_n(output: u32) -> Vec<Instruction> {
    vec![
        extract(output, 1, UseMode::Consume),
        assign(1, value(output, UseMode::Consume)),
    ]
}

#[test]
fn a_payload_move_on_the_arm_path_is_legal() {
    let p = program(vec![], payload_into_n(3), vec![], vec![], vec![i32_ty()]);
    assert!(moves(&p).is_empty(), "{:?}", moves(&p));
    assert!(loans(&p).is_empty(), "{:?}", loans(&p));
}

#[test]
fn consuming_in_one_arm_makes_the_enum_unavailable_at_the_join() {
    // Block 3 consumes an enum that only the B arm already consumed.
    let after = vec![ins(
        Some(4),
        InstructionKind::Capture(local(0, UseMode::Consume)),
    )];
    let p = program(
        vec![],
        payload_into_n(3),
        after,
        vec![],
        vec![i32_ty(), enum_ty()],
    );
    assert_eq!(moves(&p), ["BE001"]);
}

#[test]
fn a_second_extraction_after_the_consuming_one_is_a_use_after_move() {
    let arm = vec![
        extract(3, 1, UseMode::Consume),
        extract(4, 1, UseMode::Read),
    ];
    let p = program(vec![], arm, vec![], vec![], vec![i32_ty(), i32_ty()]);
    assert_eq!(moves(&p), ["BE001"]);
}

#[test]
fn the_tag_cannot_be_read_after_the_cell_was_consumed() {
    let consume_early = vec![ins(
        Some(3),
        InstructionKind::Capture(local(0, UseMode::Consume)),
    )];
    let p = program(
        vec![],
        payload_into_n(4),
        vec![],
        consume_early,
        vec![enum_ty(), i32_ty()],
    );
    assert!(moves(&p).contains(&"BE001".to_string()), "{:?}", moves(&p));
}

#[test]
fn a_live_reference_blocks_the_consuming_extraction() {
    // r := &e in block 0; the B arm consumes e while r is still used after the join.
    let borrow = vec![ins(
        Some(3),
        InstructionKind::Borrow {
            loan: LoanId(0),
            owner: local(0, UseMode::Borrow),
            access: Access::Borrow,
        },
    )];
    let after = vec![ins(
        Some(5),
        InstructionKind::Capture(value(3, UseMode::Borrow)),
    )];
    let reference = Type::Reference {
        access: Access::Borrow,
        inner: Box::new(enum_ty()),
    };
    let p = program(
        vec![],
        payload_into_n(4),
        after,
        borrow,
        vec![reference.clone(), i32_ty(), reference],
    );
    assert!(loans(&p).contains(&"BE005".to_string()), "{:?}", loans(&p));
}

fn variant_addr(loan: u32, access: Access, mode: UseMode) -> InstructionKind {
    InstructionKind::VariantAddr {
        loan: LoanId(loan),
        base: local(0, mode),
        variant: 1,
        field: 0,
        access,
    }
}

fn ref_i32(access: Access) -> Type {
    Type::Reference {
        access,
        inner: Box::new(i32_ty()),
    }
}

#[test]
fn a_payload_borrow_conflicts_with_a_write_to_the_same_payload() {
    // r := &e.B.0; w := &mut e.B.0; *w = 5; read through r afterwards.
    let head = vec![
        ins(Some(3), variant_addr(0, Access::Borrow, UseMode::Borrow)),
        ins(
            Some(4),
            InstructionKind::Constant(Constant::Integer("5".into())),
        ),
        ins(Some(5), variant_addr(1, Access::Share, UseMode::Share)),
        ins(
            None,
            InstructionKind::Store {
                reference: value(5, UseMode::Share),
                value: value(4, UseMode::Consume),
            },
        ),
        ins(
            Some(6),
            InstructionKind::Load {
                reference: value(3, UseMode::Borrow),
            },
        ),
    ];
    let p = program(
        vec![],
        vec![],
        vec![],
        head,
        vec![
            ref_i32(Access::Borrow),
            i32_ty(),
            ref_i32(Access::Share),
            i32_ty(),
        ],
    );
    assert_eq!(loans(&p), ["BE005"]);
}

#[test]
fn a_payload_borrow_conflicts_with_a_write_to_the_whole_enum() {
    // r := &e.B.0 stays live while the whole enum is reassigned.
    let head = vec![
        ins(Some(3), variant_addr(0, Access::Borrow, UseMode::Borrow)),
        ins(
            Some(4),
            InstructionKind::EnumNew {
                ty: TypeId(0),
                variant: 0,
                payload: vec![],
            },
        ),
        InstructionKind::Assign {
            target: LocalId(0),
            value: value(4, UseMode::Consume),
            initialize: false,
        }
        .into_ins(),
        ins(
            Some(5),
            InstructionKind::Load {
                reference: value(3, UseMode::Borrow),
            },
        ),
    ];
    let p = program(
        vec![],
        vec![],
        vec![],
        head,
        vec![ref_i32(Access::Borrow), enum_ty(), i32_ty()],
    );
    assert!(loans(&p).contains(&"BE005".to_string()), "{:?}", loans(&p));
}

trait IntoIns {
    fn into_ins(self) -> Instruction;
}
impl IntoIns for InstructionKind {
    fn into_ins(self) -> Instruction {
        ins(None, self)
    }
}

#[test]
fn a_payload_borrow_that_is_not_used_again_allows_the_write() {
    let head = vec![
        ins(Some(3), variant_addr(0, Access::Borrow, UseMode::Borrow)),
        ins(
            Some(4),
            InstructionKind::Load {
                reference: value(3, UseMode::Borrow),
            },
        ),
        ins(
            Some(5),
            InstructionKind::EnumNew {
                ty: TypeId(0),
                variant: 0,
                payload: vec![],
            },
        ),
        assign(0, value(5, UseMode::Consume)),
    ];
    let p = program(
        vec![],
        vec![],
        vec![],
        head,
        vec![ref_i32(Access::Borrow), i32_ty(), enum_ty()],
    );
    assert!(loans(&p).is_empty(), "{:?}", loans(&p));
}
