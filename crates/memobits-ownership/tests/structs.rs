//! Move and loan checks for struct owners and field references.
use memobits_diagnostics::{SourceId, Span};
use memobits_ir::*;
use memobits_ownership::{check_loans, check_moves};

fn span(at: usize) -> Span {
    Span {
        source: SourceId(6),
        start: at,
        end: at + 1,
    }
}
fn i32_ty() -> Type {
    Type::Primitive(Primitive::I32)
}
fn struct_ty() -> Type {
    Type::Struct(TypeId(0))
}
fn reference(access: Access) -> Type {
    Type::Reference {
        access,
        inner: Box::new(i32_ty()),
    }
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
fn constant(output: u32) -> Instruction {
    ins(
        Some(output),
        InstructionKind::Constant(Constant::Integer("1".into())),
    )
}
fn field_addr(output: u32, loan: u32, base: u32, field: u32, access: Access) -> Instruction {
    let mode = match access {
        Access::Share => UseMode::Share,
        _ => UseMode::Borrow,
    };
    ins(
        Some(output),
        InstructionKind::FieldAddr {
            loan: LoanId(loan),
            base: local(base, mode),
            field,
            access,
        },
    )
}
fn load(output: u32, reference: u32, access: Access) -> Instruction {
    let mode = if access == Access::Share {
        UseMode::Share
    } else {
        UseMode::Borrow
    };
    ins(
        Some(output),
        InstructionKind::Load {
            reference: value(reference, mode),
        },
    )
}
fn assign(target: u32, source: Operand, initialize: bool) -> Instruction {
    ins(
        None,
        InstructionKind::Assign {
            target: LocalId(target),
            value: source,
            initialize,
        },
    )
}

/// Locals `p` and `q` (struct `{ x: i32, y: i32 }`, mutable per argument).
/// Values 0 and 1 are constants and 2 is the struct built from them, stored in
/// `p`; further values come from `extra_values`.
fn function(mutable: bool, extra_values: Vec<Type>, instructions: Vec<Instruction>) -> Program {
    let mut values = vec![i32_ty(), i32_ty(), struct_ty()];
    values.extend(extra_values);
    let slot = |name: &str| Local {
        name: name.into(),
        ty: struct_ty(),
        mutable,
        span: span(1),
    };
    let mut body = vec![
        constant(0),
        constant(1),
        ins(
            Some(2),
            InstructionKind::StructNew {
                ty: TypeId(0),
                fields: vec![value(0, UseMode::Consume), value(1, UseMode::Consume)],
            },
        ),
        assign(0, value(2, UseMode::Consume), true),
    ];
    body.extend(instructions);
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
            locals: vec![slot("p"), slot("q")],
            values,
            blocks: vec![Block {
                parameters: vec![],
                instructions: body,
                terminator: Terminator {
                    span: None,
                    kind: TerminatorKind::Return(None),
                },
            }],
            entry: BlockId(0),
        }],
        types: vec![TypeDef {
            path: CanonicalType {
                package: "test".into(),
                module: vec!["main".into()],
                name: "P".into(),
            },
            span: span(0),
            error_ancestry: None,
            entry_outcome: None,
            kind: TypeDefKind::Struct {
                fields: vec![
                    FieldDef {
                        name: "x".into(),
                        ty: i32_ty(),
                    },
                    FieldDef {
                        name: "y".into(),
                        ty: i32_ty(),
                    },
                ],
            },
        }],
    }
}
fn move_codes(program: &Program) -> Vec<String> {
    program.validate().unwrap();
    check_moves(program)
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}
fn loan_codes(program: &Program) -> Vec<String> {
    program.validate().unwrap();
    check_loans(program)
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

#[test]
fn field_reads_do_not_consume_the_struct() {
    let program = function(
        false,
        vec![
            reference(Access::Borrow),
            i32_ty(),
            reference(Access::Borrow),
            i32_ty(),
        ],
        vec![
            field_addr(3, 0, 0, 0, Access::Borrow),
            load(4, 3, Access::Borrow),
            field_addr(5, 1, 0, 1, Access::Borrow),
            load(6, 5, Access::Borrow),
        ],
    );
    assert!(move_codes(&program).is_empty());
    assert!(loan_codes(&program).is_empty());
}

#[test]
fn field_address_requires_an_available_struct() {
    // Moving the struct local into `q` leaves `p` unavailable.
    let program = function(
        false,
        vec![reference(Access::Borrow)],
        vec![
            assign(1, local(0, UseMode::Consume), true),
            field_addr(3, 0, 0, 0, Access::Borrow),
        ],
    );
    assert!(move_codes(&program).contains(&"BE001".to_string()));
}

#[test]
fn struct_creation_consumes_its_field_operands() {
    let mut program = function(false, vec![i32_ty()], vec![]);
    // Value 0 was consumed by the struct literal.
    program.functions[0].blocks[0].instructions.push(ins(
        Some(3),
        InstructionKind::Capture(value(0, UseMode::Consume)),
    ));
    assert!(move_codes(&program).contains(&"BE001".to_string()));
}

#[test]
fn a_field_reference_keeps_the_whole_struct_borrowed() {
    // A live field reference blocks reassigning the struct it points into.
    let program = function(
        true,
        vec![
            reference(Access::Borrow),
            i32_ty(),
            i32_ty(),
            struct_ty(),
            i32_ty(),
        ],
        vec![
            field_addr(3, 0, 0, 0, Access::Borrow),
            constant(4),
            constant(5),
            ins(
                Some(6),
                InstructionKind::StructNew {
                    ty: TypeId(0),
                    fields: vec![value(4, UseMode::Consume), value(5, UseMode::Consume)],
                },
            ),
            assign(0, value(6, UseMode::Consume), false),
            load(7, 3, Access::Borrow),
        ],
    );
    assert!(loan_codes(&program).contains(&"BE005".to_string()));
}

#[test]
fn field_references_to_different_fields_are_disjoint() {
    // Distinct fields of one struct are independent locations (A4): a live
    // Share reference to field 0 does not block a write through field 1.
    let program = function(
        true,
        vec![reference(Access::Share), reference(Access::Share), i32_ty()],
        vec![
            field_addr(3, 0, 0, 0, Access::Share),
            field_addr(4, 1, 0, 1, Access::Share),
            constant(5),
            ins(
                None,
                InstructionKind::Store {
                    reference: value(3, UseMode::Share),
                    value: value(5, UseMode::Consume),
                },
            ),
        ],
    );
    assert!(loan_codes(&program).is_empty());
}

#[test]
fn share_field_access_requires_a_mutable_owner() {
    let program = function(
        false,
        vec![reference(Access::Share)],
        vec![field_addr(3, 0, 0, 0, Access::Share)],
    );
    assert!(loan_codes(&program).contains(&"BE005".to_string()));
}
