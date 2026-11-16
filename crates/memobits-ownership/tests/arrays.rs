//! Move and loan checks for array owners and element references.
use memobits_diagnostics::{SourceId, Span};
use memobits_ir::*;
use memobits_ownership::{check_loans, check_moves};

fn span(at: usize) -> Span {
    Span {
        source: SourceId(5),
        start: at,
        end: at + 1,
    }
}
fn i32_ty() -> Type {
    Type::Primitive(Primitive::I32)
}
fn array_ty() -> Type {
    Type::Array {
        element: Box::new(i32_ty()),
        len: 2,
    }
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
fn array_new(output: u32, first: u32, second: u32) -> Instruction {
    ins(
        Some(output),
        InstructionKind::ArrayNew {
            init: ArrayInit::Elements(vec![
                value(first, UseMode::Consume),
                value(second, UseMode::Consume),
            ]),
        },
    )
}
fn init(target: u32, from: u32) -> Instruction {
    ins(
        None,
        InstructionKind::Assign {
            target: LocalId(target),
            value: value(from, UseMode::Consume),
            initialize: true,
        },
    )
}
fn element_addr(output: u32, loan: u32, base: u32, index: u32, access: Access) -> Instruction {
    let mode = match access {
        Access::Share => UseMode::Share,
        _ => UseMode::Borrow,
    };
    ins(
        Some(output),
        InstructionKind::ElementAddr {
            loan: LoanId(loan),
            base: local(base, mode),
            index: value(index, UseMode::Read),
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
/// Two array locals `a` (mutable per argument) and `b`; values 0..=1 are
/// constants, 2 is an array, 3 an index; further values come from `types`.
fn function(mutable: bool, extra_values: Vec<Type>, instructions: Vec<Instruction>) -> Program {
    let mut values = vec![i32_ty(), i32_ty(), array_ty(), i32_ty()];
    values.extend(extra_values);
    let local = |name: &str| Local {
        name: name.into(),
        ty: array_ty(),
        mutable,
        span: span(1),
    };
    let mut prelude = vec![
        constant(0),
        constant(1),
        array_new(2, 0, 1),
        init(0, 2),
        constant(3),
    ];
    prelude.extend(instructions);
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
            locals: vec![local("a"), local("b")],
            values,
            blocks: vec![Block {
                parameters: vec![],
                instructions: prelude,
                terminator: Terminator {
                    span: None,
                    kind: TerminatorKind::Return(None),
                },
            }],
            entry: BlockId(0),
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
fn element_address_does_not_consume_the_array_or_index() {
    let program = function(
        false,
        vec![
            reference(Access::Borrow),
            i32_ty(),
            reference(Access::Borrow),
            i32_ty(),
        ],
        vec![
            element_addr(4, 0, 0, 3, Access::Borrow),
            load(5, 4, Access::Borrow),
            element_addr(6, 1, 0, 3, Access::Borrow),
            load(7, 6, Access::Borrow),
        ],
    );
    assert!(move_codes(&program).is_empty());
    assert!(loan_codes(&program).is_empty());
}

#[test]
fn element_address_requires_an_available_array() {
    // Moving the array local into `b` (array Assign) leaves `a` unavailable.
    let program = function(
        false,
        vec![reference(Access::Borrow)],
        vec![
            ins(
                None,
                InstructionKind::Assign {
                    target: LocalId(1),
                    value: local(0, UseMode::Consume),
                    initialize: true,
                },
            ),
            element_addr(4, 0, 0, 3, Access::Borrow),
        ],
    );
    assert!(move_codes(&program).contains(&"BE001".to_string()));
}

#[test]
fn array_literal_consumes_its_element_operands() {
    let mut program = function(false, vec![], vec![]);
    // Reuse value 0 after the literal consumed it.
    program.functions[0].values.push(i32_ty());
    program.functions[0].blocks[0].instructions.push(ins(
        Some(4),
        InstructionKind::Capture(value(0, UseMode::Consume)),
    ));
    assert!(move_codes(&program).contains(&"BE001".to_string()));
}

#[test]
fn element_reference_keeps_the_whole_array_borrowed() {
    // A live element reference blocks reassigning the array it points into.
    let program = function(
        true,
        vec![reference(Access::Borrow), i32_ty()],
        vec![
            element_addr(4, 0, 0, 3, Access::Borrow),
            ins(
                None,
                InstructionKind::Assign {
                    target: LocalId(0),
                    value: value(2, UseMode::Consume),
                    initialize: false,
                },
            ),
            load(5, 4, Access::Borrow),
        ],
    );
    assert!(loan_codes(&program).contains(&"BE005".to_string()));
}

#[test]
fn element_borrows_may_overlap_but_share_conflicts_with_any_element() {
    // Shared read-only element borrows of one array coexist; an exclusive Share
    // element reference conflicts with every other live element reference.
    let program = function(
        true,
        vec![
            reference(Access::Share),
            reference(Access::Borrow),
            i32_ty(),
        ],
        vec![
            element_addr(4, 0, 0, 3, Access::Share),
            element_addr(5, 1, 0, 3, Access::Borrow),
            load(6, 5, Access::Borrow),
            ins(
                None,
                InstructionKind::Store {
                    reference: value(4, UseMode::Share),
                    value: value(3, UseMode::Consume),
                },
            ),
        ],
    );
    assert!(loan_codes(&program).contains(&"BE005".to_string()));
}

#[test]
fn share_element_access_requires_a_mutable_array() {
    let program = function(
        false,
        vec![reference(Access::Share)],
        vec![element_addr(4, 0, 0, 3, Access::Share)],
    );
    assert!(loan_codes(&program).contains(&"BE005".to_string()));
    let program = function(
        true,
        vec![reference(Access::Share)],
        vec![element_addr(4, 0, 0, 3, Access::Share)],
    );
    assert!(loan_codes(&program).is_empty());
}

#[test]
fn element_write_conflicts_with_a_live_element_reference() {
    // `a[i] = v` is ElementAddr(Share) + Store. A borrow of the array that is
    // still read afterwards (value 4 is loaded last) conflicts with that write.
    let program = function(
        true,
        vec![
            reference(Access::Borrow),
            reference(Access::Share),
            i32_ty(),
        ],
        vec![
            element_addr(4, 0, 0, 3, Access::Borrow),
            element_addr(5, 1, 0, 3, Access::Share),
            ins(
                None,
                InstructionKind::Store {
                    reference: value(5, UseMode::Share),
                    value: value(3, UseMode::Consume),
                },
            ),
            load(6, 4, Access::Borrow),
        ],
    );
    assert!(loan_codes(&program).contains(&"BE005".to_string()));
}

#[test]
fn element_write_after_the_last_use_of_a_reference_is_accepted() {
    let program = function(
        true,
        vec![
            reference(Access::Borrow),
            i32_ty(),
            reference(Access::Share),
        ],
        vec![
            element_addr(4, 0, 0, 3, Access::Borrow),
            load(5, 4, Access::Borrow),
            element_addr(6, 1, 0, 3, Access::Share),
            ins(
                None,
                InstructionKind::Store {
                    reference: value(6, UseMode::Share),
                    value: value(3, UseMode::Consume),
                },
            ),
        ],
    );
    assert!(loan_codes(&program).is_empty());
}
