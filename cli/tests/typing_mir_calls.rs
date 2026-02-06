use kernel::ast::FunctionKind;
use mir::analysis::typing::TypingChecker;
use mir::types::MirType;
use mir::{
    BasicBlock, BasicBlockData, Body, BorrowKind, CallOperand, Local, LocalDecl, Operand, Place,
    Terminator,
};

#[test]
fn typing_rejects_call_operand_kind_mismatch() {
    let mut body = Body::new(0);
    body.local_decls
        .push(LocalDecl::new(MirType::Nat, Some("_return".to_string())));
    body.local_decls.push(LocalDecl::new(
        MirType::Fn(
            FunctionKind::FnOnce,
            Vec::new(),
            vec![MirType::Nat],
            Box::new(MirType::Nat),
        ),
        None,
    ));
    body.local_decls.push(LocalDecl::new(MirType::Nat, None));

    body.basic_blocks.push(BasicBlockData {
        statements: vec![],
        terminator: Some(Terminator::Call {
            func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(1))),
            args: vec![Operand::Copy(Place::from(Local(2)))],
            destination: Place::from(Local(0)),
            target: Some(BasicBlock(1)),
        }),
    });
    body.basic_blocks.push(BasicBlockData {
        statements: vec![],
        terminator: Some(Terminator::Return),
    });

    let mut checker = TypingChecker::new(&body);
    checker.check();
    assert!(
        checker.errors().iter().any(|e| e
            .to_string()
            .contains("Call operand does not match function kind")),
        "Expected function kind mismatch error, got {:?}",
        checker.errors()
    );
}
