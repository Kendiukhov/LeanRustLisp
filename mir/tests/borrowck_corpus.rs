//! Extended Borrow Checker Test Corpus
//!
//! This corpus tests NLL (Non-Lexical Lifetimes) semantics and
//! documents the expected accept/reject decisions for various patterns.

use kernel::ast::FunctionKind;
use mir::analysis::nll::{BorrowCheckResult, Location, NllChecker};
use mir::errors::BorrowError;
use mir::lints::PanicFreeLinter;
use mir::types::*;
use mir::*;

// =============================================================================
// HELPER FUNCTIONS
// =============================================================================

fn create_body_with_locals(local_types: Vec<MirType>) -> Body {
    let mut body = Body::new(0);
    for (i, ty) in local_types.into_iter().enumerate() {
        let name = if i == 0 {
            Some("_return".to_string())
        } else {
            None
        };
        body.local_decls.push(LocalDecl::new(ty, name));
    }
    body
}

fn nat_const(n: u64) -> Operand {
    Operand::Constant(Box::new(Constant {
        literal: Literal::Nat(n),
        ty: MirType::Nat,
    }))
}

fn check_accepts(body: &Body) -> BorrowCheckResult {
    let mut checker = NllChecker::new(body);
    checker.check();
    checker.into_result()
}

#[test]
fn mir_ref_copy_semantics() {
    let shared = MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Not);
    let unique = MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Mut);

    assert!(shared.is_copy(), "Shared references should be Copy");
    assert!(!unique.is_copy(), "Mutable references should not be Copy");
}

// =============================================================================
// NLL ACCEPTANCE TESTS
// Tests that NLL should accept but lexical lifetimes would reject
// =============================================================================

/// NLL Accept: Borrow ends before mutation in same block
/// Lexical would reject because borrow and mutation are in same scope
#[test]
fn nll_accept_borrow_ends_early() {
    // let x = 0;
    // let y = &x;   // borrow starts
    // let z = *y;   // last use of y
    // x = 1;        // mutation - OK because y is dead

    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                     // _0: return
        MirType::Nat,                                                     // _1: x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // _2: y
        MirType::Nat,                                                     // _3: z
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            // x = 0
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            // y = &x
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            // z = *y (last use of y)
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
            // x = 1 (mutation after borrow ends)
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(1))),
            // _0 = z
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place::from(Local(3)))),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: borrow ends before mutation. Errors: {:?}",
        result.errors
    );
}

/// NLL Accept: Shared borrow ends before mutable borrow begins
#[test]
fn nll_accept_shared_then_mut_after_last_use() {
    // let x = 0;
    // let r = &x;
    // use(*r);    // last use of r
    // let m = &mut x; // OK: r is dead
    // *m = 1;

    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                     // _0: return
        MirType::Nat,                                                     // _1: x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // _2: r
        MirType::Ref(Region(3), Box::new(MirType::Nat), Mutability::Mut), // _3: m
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place {
                    local: Local(3),
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Use(nat_const(1)),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: shared borrow ends before mutable borrow. Errors: {:?}",
        result.errors
    );
}

/// NLL Accept: Different branches with non-overlapping borrows
#[test]
fn nll_accept_branch_borrows() {
    // if cond {
    //     let y = &x;
    //     use(y);
    // } else {
    //     x = 1;  // OK - y doesn't exist in this branch
    // }

    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                     // _0: return
        MirType::Nat,                                                     // _1: x
        MirType::Bool,                                                    // _2: cond
        MirType::Ref(Region(3), Box::new(MirType::Nat), Mutability::Not), // _3: y
    ]);

    // bb0: switch on cond
    body.basic_blocks.push(BasicBlockData {
        statements: vec![Statement::Assign(
            Place::from(Local(1)),
            Rvalue::Use(nat_const(0)),
        )],
        terminator: Some(Terminator::SwitchInt {
            discr: Operand::Copy(Place::from(Local(2))),
            targets: SwitchTargets {
                values: vec![0],
                targets: vec![BasicBlock(2), BasicBlock(1)], // false->bb2, true->bb1
            },
        }),
    });

    // bb1: borrow branch
    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(3),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::Goto {
            target: BasicBlock(3),
        }),
    });

    // bb2: mutation branch (no borrow)
    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(42))),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
            ),
        ],
        terminator: Some(Terminator::Goto {
            target: BasicBlock(3),
        }),
    });

    // bb3: join
    body.basic_blocks.push(BasicBlockData {
        statements: vec![],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: non-overlapping borrows in branches. Errors: {:?}",
        result.errors
    );
}

/// NLL Accept: Repeated Fn calls borrow the function operand
#[test]
fn nll_accepts_repeated_fn_calls() {
    let mut body = create_body_with_locals(vec![
        MirType::Nat, // _0: return
        MirType::Fn(
            FunctionKind::Fn,
            Vec::new(),
            vec![MirType::Nat],
            Box::new(MirType::Nat),
        ), // _1: f
        MirType::Nat, // _2: x
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            ),
            Statement::Assign(Place::from(Local(2)), Rvalue::Use(nat_const(0))),
        ],
        terminator: Some(Terminator::Call {
            func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(1))),
            args: vec![Operand::Copy(Place::from(Local(2)))],
            destination: Place::from(Local(0)),
            target: Some(BasicBlock(1)),
        }),
    });

    body.basic_blocks.push(BasicBlockData {
        statements: vec![],
        terminator: Some(Terminator::Call {
            func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(1))),
            args: vec![Operand::Copy(Place::from(Local(2)))],
            destination: Place::from(Local(0)),
            target: Some(BasicBlock(2)),
        }),
    });

    body.basic_blocks.push(BasicBlockData {
        statements: vec![],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: repeated Fn calls via borrow operand. Errors: {:?}",
        result.errors
    );
}

/// NLL Accept: Repeated FnMut calls borrow the function operand mutably
#[test]
fn nll_accepts_repeated_fnmut_calls() {
    let mut body = create_body_with_locals(vec![
        MirType::Nat, // _0: return
        MirType::Fn(
            FunctionKind::FnMut,
            Vec::new(),
            vec![MirType::Nat],
            Box::new(MirType::Nat),
        ), // _1: f
        MirType::Nat, // _2: x
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            ),
            Statement::Assign(Place::from(Local(2)), Rvalue::Use(nat_const(1))),
        ],
        terminator: Some(Terminator::Call {
            func: CallOperand::Borrow(BorrowKind::Mut, Place::from(Local(1))),
            args: vec![Operand::Copy(Place::from(Local(2)))],
            destination: Place::from(Local(0)),
            target: Some(BasicBlock(1)),
        }),
    });

    body.basic_blocks.push(BasicBlockData {
        statements: vec![],
        terminator: Some(Terminator::Call {
            func: CallOperand::Borrow(BorrowKind::Mut, Place::from(Local(1))),
            args: vec![Operand::Copy(Place::from(Local(2)))],
            destination: Place::from(Local(0)),
            target: Some(BasicBlock(2)),
        }),
    });

    body.basic_blocks.push(BasicBlockData {
        statements: vec![],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: repeated FnMut calls via mut borrow operand. Errors: {:?}",
        result.errors
    );
}

/// NLL Accept: Call region params are instantiated per call
#[test]
fn nll_accepts_independent_call_regions() {
    // let x = 0;
    // let r1 = id_ref(&x);
    // use(*r1);
    // drop(r1);
    // let y = 1;
    // let r2 = id_ref(&y);
    // use(*r2);
    // x = 2; // OK: r1 is dead, call2 should not extend it

    let shared_ref = MirType::Ref(Region(5), Box::new(MirType::Nat), Mutability::Not);
    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                     // _0: return
        MirType::Nat,                                                     // _1: x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // _2: r1
        MirType::Nat,                                                     // _3: y
        MirType::Ref(Region(3), Box::new(MirType::Nat), Mutability::Not), // _4: r2
        MirType::Fn(
            FunctionKind::Fn,
            vec![Region(5)],
            vec![shared_ref.clone()],
            Box::new(shared_ref.clone()),
        ), // _5: id_ref
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(5)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            ),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
        ],
        terminator: Some(Terminator::Call {
            func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(5))),
            args: vec![Operand::Copy(Place::from(Local(2)))],
            destination: Place::from(Local(2)),
            target: Some(BasicBlock(1)),
        }),
    });

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
            Statement::StorageDead(Local(2)),
            Statement::Assign(Place::from(Local(3)), Rvalue::Use(nat_const(1))),
            Statement::Assign(
                Place::from(Local(4)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(3))),
            ),
        ],
        terminator: Some(Terminator::Call {
            func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(5))),
            args: vec![Operand::Copy(Place::from(Local(4)))],
            destination: Place::from(Local(4)),
            target: Some(BasicBlock(2)),
        }),
    });

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(4),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(2))),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: independent call regions. Errors: {:?}",
        result.errors
    );
}

/// NLL Accept: Shared borrow in one branch ends before mutable borrow after join
#[test]
fn nll_accept_branch_shared_then_mut_after_join() {
    // if cond {
    //   let r = &x;
    //   use(*r);
    // }
    // let m = &mut x; // OK: r does not live past join
    // *m = 1;

    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                     // _0: return
        MirType::Nat,                                                     // _1: x
        MirType::Bool,                                                    // _2: cond
        MirType::Ref(Region(3), Box::new(MirType::Nat), Mutability::Not), // _3: r
        MirType::Ref(Region(4), Box::new(MirType::Nat), Mutability::Mut), // _4: m
    ]);

    // bb0: init + branch
    body.basic_blocks.push(BasicBlockData {
        statements: vec![Statement::Assign(
            Place::from(Local(1)),
            Rvalue::Use(nat_const(0)),
        )],
        terminator: Some(Terminator::SwitchInt {
            discr: Operand::Copy(Place::from(Local(2))),
            targets: SwitchTargets {
                values: vec![0],
                targets: vec![BasicBlock(2), BasicBlock(1)], // false->bb2, true->bb1
            },
        }),
    });

    // bb1: shared borrow branch
    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(3),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::Goto {
            target: BasicBlock(3),
        }),
    });

    // bb2: no borrow branch
    body.basic_blocks.push(BasicBlockData {
        statements: vec![Statement::Assign(
            Place::from(Local(0)),
            Rvalue::Use(nat_const(0)),
        )],
        terminator: Some(Terminator::Goto {
            target: BasicBlock(3),
        }),
    });

    // bb3: join, then mutable borrow
    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(4)),
                Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place {
                    local: Local(4),
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Use(nat_const(1)),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: branch-local shared borrow ends before mutable borrow after join. Errors: {:?}",
        result.errors
    );
}

/// NLL Reject: Mutation while closure-borrow capture is live
#[test]
fn nll_rejects_mutation_while_closure_capture_live() {
    let mut body = create_body_with_locals(vec![
        MirType::Unit,                                                    // _0: return
        MirType::Nat,                                                     // _1: x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // _2: r = &x
        MirType::Fn(
            FunctionKind::Fn,
            Vec::new(),
            vec![MirType::Nat],
            Box::new(MirType::Nat),
        ), // _3: f
    ]);

    // Attach capture types to the closure local to keep the borrow alive.
    body.local_decls[3].closure_captures = vec![MirType::Ref(
        Region(2),
        Box::new(MirType::Nat),
        Mutability::Not,
    )];

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            // x = 0
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            // r = &x
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            // f = <closure> (value doesn't matter for borrowck)
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            ),
            // drop r
            Statement::StorageDead(Local(2)),
            // x = 1 (should conflict because f keeps the borrow alive)
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(1))),
            // use f so it's live across the mutation
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place::from(Local(3)))),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        !result.is_ok(),
        "Expected borrow error when mutating while closure capture is live"
    );
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, BorrowError::AssignWhileBorrowed { .. })),
        "Expected AssignWhileBorrowed error, got: {:?}",
        result.errors
    );
}

/// NLL Reject: Second mutable borrow while FnMut closure capture is live
#[test]
fn nll_rejects_second_mut_borrow_while_fnmut_capture_live() {
    let mut body = create_body_with_locals(vec![
        MirType::Unit,                                                    // _0: return
        MirType::Nat,                                                     // _1: x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Mut), // _2: r = &mut x
        MirType::Fn(
            FunctionKind::FnMut,
            Vec::new(),
            vec![MirType::Nat],
            Box::new(MirType::Nat),
        ), // _3: f
        MirType::Ref(Region(3), Box::new(MirType::Nat), Mutability::Mut), // _4: m = &mut x
    ]);

    // FnMut closure captures a mutable reference to x.
    body.local_decls[3].closure_captures = vec![MirType::Ref(
        Region(2),
        Box::new(MirType::Nat),
        Mutability::Mut,
    )];

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            // x = 0
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            // r = &mut x
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
            ),
            // f = <closure>
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            ),
            // drop r, keep borrow alive via closure capture
            Statement::StorageDead(Local(2)),
            // m = &mut x (should conflict with captured mutable borrow)
            Statement::Assign(
                Place::from(Local(4)),
                Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
            ),
            // use f so it's live across the borrow
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Move(Place::from(Local(3)))),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        !result.is_ok(),
        "Expected borrow error when taking a second mutable borrow while FnMut capture is live"
    );
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, BorrowError::ConflictingBorrow { .. })),
        "Expected ConflictingBorrow error, got: {:?}",
        result.errors
    );
}

/// NLL Reject: Closure capture stays live after move into another local
#[test]
fn nll_rejects_mutation_after_closure_move() {
    let mut body = create_body_with_locals(vec![
        MirType::Unit,                                                    // _0: return
        MirType::Nat,                                                     // _1: x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // _2: r = &x
        MirType::Fn(
            FunctionKind::Fn,
            Vec::new(),
            vec![MirType::Nat],
            Box::new(MirType::Nat),
        ), // _3: f
        MirType::Fn(
            FunctionKind::Fn,
            Vec::new(),
            vec![MirType::Nat],
            Box::new(MirType::Nat),
        ), // _4: g
    ]);

    body.local_decls[3].closure_captures = vec![MirType::Ref(
        Region(2),
        Box::new(MirType::Nat),
        Mutability::Not,
    )];

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            ),
            Statement::Assign(
                Place::from(Local(4)),
                Rvalue::Use(Operand::Copy(Place::from(Local(3)))),
            ),
            Statement::StorageDead(Local(3)),
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(1))),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place::from(Local(4)))),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        !result.is_ok(),
        "Expected borrow error when mutating after closure move"
    );
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, BorrowError::AssignWhileBorrowed { .. })),
        "Expected AssignWhileBorrowed error, got: {:?}",
        result.errors
    );
}

/// NLL Reject: Closure capture stays live after moving through an aggregate field
#[test]
fn nll_rejects_mutation_after_closure_move_through_aggregate() {
    let agg_adt = AdtId::new("Pair");
    let agg_ty = MirType::Adt(agg_adt, vec![]);
    let mut body = create_body_with_locals(vec![
        MirType::Unit,                                                    // _0: return
        MirType::Nat,                                                     // _1: x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // _2: r = &x
        MirType::Fn(
            FunctionKind::Fn,
            Vec::new(),
            vec![MirType::Nat],
            Box::new(MirType::Nat),
        ), // _3: f
        agg_ty.clone(),                                                   // _4: agg
        agg_ty.clone(),                                                   // _5: agg2
    ]);

    body.local_decls[3].closure_captures = vec![MirType::Ref(
        Region(2),
        Box::new(MirType::Nat),
        Mutability::Not,
    )];

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            ),
            Statement::Assign(
                Place {
                    local: Local(4),
                    projection: vec![PlaceElem::Field(0)],
                },
                Rvalue::Use(Operand::Move(Place::from(Local(3)))),
            ),
            Statement::StorageDead(Local(3)),
            Statement::StorageDead(Local(2)),
            Statement::Assign(
                Place::from(Local(5)),
                Rvalue::Use(Operand::Move(Place::from(Local(4)))),
            ),
            Statement::StorageDead(Local(4)),
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(1))),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Move(Place::from(Local(5)))),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        !result.is_ok(),
        "Expected borrow error when mutating after closure move through aggregate"
    );
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, BorrowError::AssignWhileBorrowed { .. })),
        "Expected AssignWhileBorrowed error, got: {:?}",
        result.errors
    );
}

/// NLL Reject: Returned reference from closure call cannot outlive the closure borrow
#[test]
fn nll_rejects_closure_return_ref_outliving_closure() {
    let ret_region = Region(1);
    let self_region = Region(2);
    let ret_ty = MirType::Ref(ret_region, Box::new(MirType::Nat), Mutability::Not);

    let mut body = create_body_with_locals(vec![
        MirType::Nat, // _0: return
        MirType::Closure(
            FunctionKind::Fn,
            self_region,
            vec![],
            vec![MirType::Nat],
            Box::new(ret_ty.clone()),
        ), // _1: f
        ret_ty,       // _2: r
        MirType::Nat, // _3: arg
    ]);

    body.local_decls[1].closure_captures = vec![MirType::Nat];

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            ),
            Statement::Assign(Place::from(Local(3)), Rvalue::Use(nat_const(0))),
        ],
        terminator: Some(Terminator::Call {
            func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(1))),
            args: vec![Operand::Copy(Place::from(Local(3)))],
            destination: Place::from(Local(2)),
            target: Some(BasicBlock(1)),
        }),
    });

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::StorageDead(Local(1)),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        !result.is_ok(),
        "Expected borrow error when returned ref outlives closure borrow"
    );
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, BorrowError::DanglingReference { .. })),
        "Expected DanglingReference error, got: {:?}",
        result.errors
    );
}

/// NLL Accept: Reborrow of mutable reference
#[test]
fn nll_accept_reborrow() {
    // let x = 0;
    // let r = &mut x;
    // let r2 = &mut *r;  // reborrow
    // *r2 = 1;
    // // r can be used again after r2 dies

    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                     // _0
        MirType::Nat,                                                     // _1: x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Mut), // _2: r
        MirType::Ref(Region(3), Box::new(MirType::Nat), Mutability::Mut), // _3: r2
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
            ),
            // reborrow: r2 = &mut *r
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Ref(
                    BorrowKind::Mut,
                    Place {
                        local: Local(2),
                        projection: vec![PlaceElem::Deref],
                    },
                ),
            ),
            // *r2 = 1
            Statement::Assign(
                Place {
                    local: Local(3),
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Use(nat_const(1)),
            ),
            Statement::Assign(Place::from(Local(0)), Rvalue::Use(nat_const(0))),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: reborrow pattern. Errors: {:?}",
        result.errors
    );
}

/// NLL Accept: Reborrow ends before original mutable ref is reused
#[test]
fn nll_accept_reborrow_then_reuse() {
    // let x = 0;
    // let r = &mut x;
    // let r2 = &mut *r;
    // *r2 = 1;  // last use of r2
    // *r = 2;   // ok after r2 ends

    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                     // _0
        MirType::Nat,                                                     // _1: x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Mut), // _2: r
        MirType::Ref(Region(3), Box::new(MirType::Nat), Mutability::Mut), // _3: r2
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Ref(
                    BorrowKind::Mut,
                    Place {
                        local: Local(2),
                        projection: vec![PlaceElem::Deref],
                    },
                ),
            ),
            Statement::Assign(
                Place {
                    local: Local(3),
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Use(nat_const(1)),
            ),
            Statement::Assign(
                Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Use(nat_const(2)),
            ),
            Statement::Assign(Place::from(Local(0)), Rvalue::Use(nat_const(0))),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: reborrow ends before reusing original. Errors: {:?}",
        result.errors
    );
}

/// NLL Accept: Reborrow stays live while writing disjoint field
#[test]
fn nll_accept_reborrow_disjoint_field_write() {
    // let p = Pair(...);
    // let r = &mut p.0;
    // let r2 = &mut *r; // reborrow
    // p.1 = ...;        // ok, disjoint field while r2 is live
    // *r2 = ...;

    let pair_adt = AdtId::new("Pair");
    let pair_ty = MirType::Adt(pair_adt.clone(), vec![]);
    let pair_ctor = CtorId::new(pair_adt.clone(), 0);
    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                        // _0
        pair_ty.clone(),                                                     // _1: p
        MirType::Ref(Region(2), Box::new(pair_ty.clone()), Mutability::Mut), // _2: r
        MirType::Ref(Region(3), Box::new(pair_ty.clone()), Mutability::Mut), // _3: r2
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::InductiveCtor(pair_ctor.clone(), 0, 0),
                    ty: pair_ty.clone(),
                }))),
            ),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(
                    BorrowKind::Mut,
                    Place {
                        local: Local(1),
                        projection: vec![PlaceElem::Field(0)],
                    },
                ),
            ),
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Ref(
                    BorrowKind::Mut,
                    Place {
                        local: Local(2),
                        projection: vec![PlaceElem::Deref],
                    },
                ),
            ),
            Statement::Assign(
                Place {
                    local: Local(1),
                    projection: vec![PlaceElem::Field(1)],
                },
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::InductiveCtor(pair_ctor.clone(), 0, 0),
                    ty: pair_ty.clone(),
                }))),
            ),
            Statement::Assign(
                Place {
                    local: Local(3),
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::InductiveCtor(pair_ctor.clone(), 0, 0),
                    ty: pair_ty.clone(),
                }))),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: reborrow with disjoint field write. Errors: {:?}",
        result.errors
    );
}

/// NLL Accept: Loop with local borrow
#[test]
fn nll_accept_loop_local_borrow() {
    // loop {
    //     let y = &x;
    //     use(*y);
    //     // y dies here
    // }
    // x = 1;  // OK after loop

    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                     // _0
        MirType::Nat,                                                     // _1: x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // _2: y
        MirType::Nat,                                                     // _3: temp
    ]);

    // bb0: init
    body.basic_blocks.push(BasicBlockData {
        statements: vec![Statement::Assign(
            Place::from(Local(1)),
            Rvalue::Use(nat_const(0)),
        )],
        terminator: Some(Terminator::Goto {
            target: BasicBlock(1),
        }),
    });

    // bb1: loop body
    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::SwitchInt {
            discr: nat_const(0), // simplified: always exit
            targets: SwitchTargets {
                values: vec![0],
                targets: vec![BasicBlock(2), BasicBlock(1)],
            },
        }),
    });

    // bb2: after loop
    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(42))),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: loop with local borrow. Errors: {:?}",
        result.errors
    );
}

/// NLL Accept: Nested loops with reborrow inside inner loop
#[test]
fn nll_accept_nested_loops_with_reborrow() {
    // outer: r = &mut x
    // inner: r2 = &mut *r; *r2 = 1; repeat
    // after inner: *r = 2; repeat outer

    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                     // _0: return
        MirType::Nat,                                                     // _1: x
        MirType::Bool,                                                    // _2: cond_outer
        MirType::Bool,                                                    // _3: cond_inner
        MirType::Ref(Region(4), Box::new(MirType::Nat), Mutability::Mut), // _4: r
        MirType::Ref(Region(5), Box::new(MirType::Nat), Mutability::Mut), // _5: r2
    ]);

    // bb0: init
    body.basic_blocks.push(BasicBlockData {
        statements: vec![Statement::Assign(
            Place::from(Local(1)),
            Rvalue::Use(nat_const(0)),
        )],
        terminator: Some(Terminator::Goto {
            target: BasicBlock(1),
        }),
    });

    // bb1: outer loop header
    body.basic_blocks.push(BasicBlockData {
        statements: vec![],
        terminator: Some(Terminator::SwitchInt {
            discr: Operand::Copy(Place::from(Local(2))),
            targets: SwitchTargets {
                values: vec![0],
                targets: vec![BasicBlock(6), BasicBlock(2)], // false -> exit, true -> outer body
            },
        }),
    });

    // bb2: outer loop body (create r)
    body.basic_blocks.push(BasicBlockData {
        statements: vec![Statement::Assign(
            Place::from(Local(4)),
            Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
        )],
        terminator: Some(Terminator::Goto {
            target: BasicBlock(3),
        }),
    });

    // bb3: inner loop header
    body.basic_blocks.push(BasicBlockData {
        statements: vec![],
        terminator: Some(Terminator::SwitchInt {
            discr: Operand::Copy(Place::from(Local(3))),
            targets: SwitchTargets {
                values: vec![0],
                targets: vec![BasicBlock(5), BasicBlock(4)], // false -> inner exit, true -> body
            },
        }),
    });

    // bb5: inner loop body (reborrow)
    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(5)),
                Rvalue::Ref(
                    BorrowKind::Mut,
                    Place {
                        local: Local(4),
                        projection: vec![PlaceElem::Deref],
                    },
                ),
            ),
            Statement::Assign(
                Place {
                    local: Local(5),
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Use(nat_const(1)),
            ),
        ],
        terminator: Some(Terminator::Goto {
            target: BasicBlock(3),
        }),
    });

    // bb4: inner exit, reuse outer borrow
    body.basic_blocks.push(BasicBlockData {
        statements: vec![Statement::Assign(
            Place {
                local: Local(4),
                projection: vec![PlaceElem::Deref],
            },
            Rvalue::Use(nat_const(2)),
        )],
        terminator: Some(Terminator::Goto {
            target: BasicBlock(1),
        }),
    });

    // bb6: exit
    body.basic_blocks.push(BasicBlockData {
        statements: vec![Statement::Assign(
            Place::from(Local(0)),
            Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
        )],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: nested loops with reborrows. Errors: {:?}",
        result.errors
    );
}

/// NLL Accept: Disjoint field borrow and write
#[test]
fn nll_accept_disjoint_field_borrow() {
    // let p = Pair(...);
    // let r = &p.0;
    // p.1 = ...; // ok, disjoint field
    // use(*r);

    let pair_adt = AdtId::new("Pair");
    let pair_ty = MirType::Adt(pair_adt.clone(), vec![]);
    let pair_ctor = CtorId::new(pair_adt.clone(), 0);
    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                        // _0
        pair_ty.clone(),                                                     // _1: p
        MirType::Ref(Region(2), Box::new(pair_ty.clone()), Mutability::Not), // _2: r
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::InductiveCtor(pair_ctor.clone(), 0, 0),
                    ty: pair_ty.clone(),
                }))),
            ),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(
                    BorrowKind::Shared,
                    Place {
                        local: Local(1),
                        projection: vec![PlaceElem::Field(0)],
                    },
                ),
            ),
            Statement::Assign(
                Place {
                    local: Local(1),
                    projection: vec![PlaceElem::Field(1)],
                },
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::InductiveCtor(pair_ctor.clone(), 0, 0),
                    ty: pair_ty.clone(),
                }))),
            ),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: disjoint field borrow/write. Errors: {:?}",
        result.errors
    );
}

/// NLL Accept: Disjoint index borrow and write (constant indices)
#[test]
fn nll_accept_disjoint_index_borrow() {
    // let v = Vec(...);
    // let i = 0;
    // let j = 1;
    // let r = &v[i];
    // v[j] = 42; // ok, disjoint indices
    // use(*r);

    let vec_adt = AdtId::new("Vec");
    let vec_ty = MirType::Adt(vec_adt.clone(), vec![MirType::Nat]);
    let vec_ctor = CtorId::new(vec_adt.clone(), 0);
    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                     // _0
        vec_ty.clone(),                                                   // _1: v
        MirType::Nat,                                                     // _2: i
        MirType::Nat,                                                     // _3: j
        MirType::Ref(Region(4), Box::new(MirType::Nat), Mutability::Not), // _4: r
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(2)), Rvalue::Use(nat_const(0))),
            Statement::Assign(Place::from(Local(3)), Rvalue::Use(nat_const(1))),
            Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::InductiveCtor(vec_ctor.clone(), 0, 0),
                    ty: vec_ty.clone(),
                }))),
            ),
            Statement::Assign(
                Place::from(Local(4)),
                Rvalue::Ref(
                    BorrowKind::Shared,
                    Place {
                        local: Local(1),
                        projection: vec![PlaceElem::Index(Local(2))],
                    },
                ),
            ),
            Statement::Assign(
                Place {
                    local: Local(1),
                    projection: vec![PlaceElem::Index(Local(3))],
                },
                Rvalue::Use(nat_const(42)),
            ),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(4),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: disjoint index borrow/write. Errors: {:?}",
        result.errors
    );
}

// =============================================================================
// NLL REJECTION TESTS
// =============================================================================

/// NLL Reject: Borrow error carries constraint explanation
#[test]
fn nll_reject_borrow_error_has_constraint_explanation() {
    // let x = 0;
    // let r = &x;
    // x = 1;      // ERROR: x is borrowed
    // use(*r);

    let mut body = create_body_with_locals(vec![
        MirType::Nat,
        MirType::Nat,                                                     // x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // r: &x
        MirType::Nat,                                                     // tmp
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(1))),
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        !result.is_ok(),
        "Expected borrow error with constraint explanation"
    );

    let error = result
        .errors
        .iter()
        .find(|e| matches!(e, BorrowError::AssignWhileBorrowed { .. }))
        .expect("Expected AssignWhileBorrowed error");

    match error {
        BorrowError::AssignWhileBorrowed { context, .. } => {
            let loan = context.loan.as_ref().expect("Expected loan context");
            let region = context
                .region
                .as_ref()
                .expect("Expected region constraint context");
            assert!(!region.chain.is_empty(), "Expected non-empty region chain");
            assert_eq!(
                region.chain.first().copied(),
                Some(loan.region),
                "Expected region chain to start with loan region"
            );
        }
        _ => panic!("Expected AssignWhileBorrowed error"),
    }
}

/// NLL Reject: Use of mutable borrow while shared borrow active
#[test]
fn nll_reject_mut_while_shared() {
    // let x = 0;
    // let r = &x;
    // let m = &mut x;  // ERROR: can't borrow mutably while borrowed
    // use(*r);

    let mut body = create_body_with_locals(vec![
        MirType::Nat,
        MirType::Nat,                                                     // x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // r: &x
        MirType::Ref(Region(3), Box::new(MirType::Nat), Mutability::Mut), // m: &mut x
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        !result.is_ok(),
        "NLL should reject: mutable borrow while shared borrow active"
    );
}

/// NLL Reject: Write to borrowed location
#[test]
fn nll_reject_write_while_borrowed() {
    // let x = 0;
    // let r = &x;
    // x = 1;      // ERROR: x is borrowed
    // use(*r);

    let mut body = create_body_with_locals(vec![
        MirType::Nat,
        MirType::Nat,                                                     // x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // r
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(1))), // write!
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(!result.is_ok(), "NLL should reject: write while borrowed");
}

/// NLL Reject: Write through shared reference
#[test]
fn nll_reject_shared_deref_write() {
    // let x = 0;
    // let r = &x;
    // *r = 1; // ERROR: shared ref

    let mut body = create_body_with_locals(vec![
        MirType::Nat,
        MirType::Nat,                                                     // x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // r
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Use(nat_const(1)),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        !result.is_ok(),
        "NLL should reject: write through shared ref"
    );
}

/// NLL Reject: Use after StorageDead
#[test]
fn nll_reject_use_after_storage_dead() {
    // let x = 0;
    // let r = &x;
    // drop(x);    // StorageDead
    // use(*r);    // ERROR: dangling reference

    let mut body = create_body_with_locals(vec![
        MirType::Nat,
        MirType::Nat,                                                     // x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // r
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::StorageDead(Local(1)), // x dies
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        !result.is_ok(),
        "NLL should reject: use after storage dead (dangling)"
    );
}

/// NLL Reject: Return reference to local (escape)
#[test]
fn nll_reject_return_ref_to_local() {
    // let x = 0;
    // return &x; // ERROR: escaping reference

    let mut body = create_body_with_locals(vec![
        MirType::Ref(Region(1), Box::new(MirType::Nat), Mutability::Not), // return ref
        MirType::Nat,                                                     // x
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    mir::transform::storage::insert_exit_storage_deads(&mut body);

    let result = check_accepts(&body);
    assert!(
        !result.is_ok(),
        "NLL should reject: returning reference to local"
    );
}

/// NLL Reject: Return reference through call (escape via function boundary)
#[test]
fn nll_reject_call_return_ref_escape() {
    // let x = 0;
    // let r = &x;
    // return id_ref(r); // ERROR: escaping reference

    let shared_ref = MirType::Ref(Region(5), Box::new(MirType::Nat), Mutability::Not);
    let mut body = create_body_with_locals(vec![
        MirType::Ref(Region(1), Box::new(MirType::Nat), Mutability::Not), // _0: return ref
        MirType::Nat,                                                     // _1: x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // _2: r
        MirType::Fn(
            FunctionKind::Fn,
            vec![Region(5)],
            vec![shared_ref.clone()],
            Box::new(shared_ref.clone()),
        ), // _3: id_ref
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            ),
        ],
        terminator: Some(Terminator::Call {
            func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(3))),
            args: vec![Operand::Copy(Place::from(Local(2)))],
            destination: Place::from(Local(0)),
            target: Some(BasicBlock(1)),
        }),
    });

    body.basic_blocks.push(BasicBlockData {
        statements: vec![],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        !result.is_ok(),
        "NLL should reject: returning reference through call"
    );
}

/// NLL Reject: Return ref tied to first arg overlaps mutable borrow
#[test]
fn nll_reject_call_return_ref_tied_to_first_arg() {
    // let x = 0;
    // let y = 1;
    // let r1 = &x;
    // let r2 = &y;
    // let r = choose_left(r1, r2); // r tied to r1
    // let m = &mut x;              // ERROR: shared borrow still live via r
    // use(*r);

    let ref_a = MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not);
    let ref_b = MirType::Ref(Region(3), Box::new(MirType::Nat), Mutability::Not);
    let func_ty = MirType::Fn(
        FunctionKind::Fn,
        vec![Region(10), Region(11)],
        vec![ref_a.clone(), ref_b.clone()],
        Box::new(ref_a.clone()),
    );

    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                     // _0: return
        MirType::Nat,                                                     // _1: x
        MirType::Nat,                                                     // _2: y
        ref_a.clone(),                                                    // _3: r1
        ref_b.clone(),                                                    // _4: r2
        MirType::Ref(Region(4), Box::new(MirType::Nat), Mutability::Not), // _5: r
        MirType::Ref(Region(5), Box::new(MirType::Nat), Mutability::Mut), // _6: m
        func_ty,                                                          // _7: choose_left
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(Place::from(Local(2)), Rvalue::Use(nat_const(1))),
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(4)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(2))),
            ),
            Statement::Assign(
                Place::from(Local(7)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            ),
        ],
        terminator: Some(Terminator::Call {
            func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(7))),
            args: vec![
                Operand::Copy(Place::from(Local(3))),
                Operand::Copy(Place::from(Local(4))),
            ],
            destination: Place::from(Local(5)),
            target: Some(BasicBlock(1)),
        }),
    });

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(6)),
                Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(5),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        !result.is_ok(),
        "NLL should reject: return ref tied to first arg overlaps mutable borrow"
    );
}

/// NLL Accept: Return ref tied to second arg allows mutating first arg
#[test]
fn nll_accept_call_return_ref_tied_to_second_arg_allows_mutating_first() {
    // let x = 0;
    // let y = 1;
    // let r1 = &x;
    // let r2 = &y;
    // let r = choose_right(r1, r2); // r tied to r2
    // let m = &mut x;               // OK: r borrows y, not x
    // use(*r);

    let ref_a = MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not);
    let ref_b = MirType::Ref(Region(3), Box::new(MirType::Nat), Mutability::Not);
    let func_ty = MirType::Fn(
        FunctionKind::Fn,
        vec![Region(10), Region(11)],
        vec![ref_a.clone(), ref_b.clone()],
        Box::new(ref_b.clone()),
    );

    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                     // _0: return
        MirType::Nat,                                                     // _1: x
        MirType::Nat,                                                     // _2: y
        ref_a.clone(),                                                    // _3: r1
        ref_b.clone(),                                                    // _4: r2
        MirType::Ref(Region(4), Box::new(MirType::Nat), Mutability::Not), // _5: r
        MirType::Ref(Region(5), Box::new(MirType::Nat), Mutability::Mut), // _6: m
        func_ty,                                                          // _7: choose_right
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(Place::from(Local(2)), Rvalue::Use(nat_const(1))),
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(4)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(2))),
            ),
            Statement::Assign(
                Place::from(Local(7)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            ),
        ],
        terminator: Some(Terminator::Call {
            func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(7))),
            args: vec![
                Operand::Copy(Place::from(Local(3))),
                Operand::Copy(Place::from(Local(4))),
            ],
            destination: Place::from(Local(5)),
            target: Some(BasicBlock(1)),
        }),
    });

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(6)),
                Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(5),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "NLL should accept: return ref tied to second arg allows mutating first. Errors: {:?}",
        result.errors
    );
}

/// NLL Reject: Return ref tied to second arg overlaps mutable borrow of second
#[test]
fn nll_reject_call_return_ref_tied_to_second_arg_overlaps_mut_borrow() {
    // let x = 0;
    // let y = 1;
    // let r1 = &x;
    // let r2 = &y;
    // let r = choose_right(r1, r2); // r tied to r2
    // let m = &mut y;               // ERROR: shared borrow still live via r
    // use(*r);

    let ref_a = MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not);
    let ref_b = MirType::Ref(Region(3), Box::new(MirType::Nat), Mutability::Not);
    let func_ty = MirType::Fn(
        FunctionKind::Fn,
        vec![Region(10), Region(11)],
        vec![ref_a.clone(), ref_b.clone()],
        Box::new(ref_b.clone()),
    );

    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                     // _0: return
        MirType::Nat,                                                     // _1: x
        MirType::Nat,                                                     // _2: y
        ref_a.clone(),                                                    // _3: r1
        ref_b.clone(),                                                    // _4: r2
        MirType::Ref(Region(4), Box::new(MirType::Nat), Mutability::Not), // _5: r
        MirType::Ref(Region(5), Box::new(MirType::Nat), Mutability::Mut), // _6: m
        func_ty,                                                          // _7: choose_right
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(Place::from(Local(2)), Rvalue::Use(nat_const(1))),
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(4)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(2))),
            ),
            Statement::Assign(
                Place::from(Local(7)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            ),
        ],
        terminator: Some(Terminator::Call {
            func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(7))),
            args: vec![
                Operand::Copy(Place::from(Local(3))),
                Operand::Copy(Place::from(Local(4))),
            ],
            destination: Place::from(Local(5)),
            target: Some(BasicBlock(1)),
        }),
    });

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(6)),
                Rvalue::Ref(BorrowKind::Mut, Place::from(Local(2))),
            ),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(5),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        !result.is_ok(),
        "NLL should reject: return ref tied to second arg overlaps mutable borrow"
    );
}

/// NLL Reject: Double mutable borrow
#[test]
fn nll_reject_double_mut_borrow() {
    // let x = 0;
    // let r1 = &mut x;
    // let r2 = &mut x;  // ERROR: x already mutably borrowed
    // *r1 = 1;

    let mut body = create_body_with_locals(vec![
        MirType::Nat,
        MirType::Nat,                                                     // x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Mut), // r1
        MirType::Ref(Region(3), Box::new(MirType::Nat), Mutability::Mut), // r2
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(3)),
                Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Use(nat_const(1)),
            ),
            Statement::Assign(Place::from(Local(0)), Rvalue::Use(nat_const(0))),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(!result.is_ok(), "NLL should reject: double mutable borrow");
}

/// NLL Reject: Mutable borrow stored in opaque local still enforces conflicts
#[test]
fn nll_reject_opaque_ref_borrow_conflict() {
    // let x = 0;
    // let r : Opaque = &mut x;
    // x = 1;        // ERROR: x mutably borrowed by r
    // let z = *r;

    let mut body = create_body_with_locals(vec![
        MirType::Nat, // _0: return
        MirType::Nat, // _1: x
        MirType::Opaque {
            reason: "opaque alias".to_string(),
        }, // _2: r (opaque alias to &mut)
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
            ),
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(1))),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);
    assert!(
        !result.is_ok(),
        "NLL should reject: opaque borrow should still conflict"
    );
}

// =============================================================================
// INTERIOR MUTABILITY TESTS
// =============================================================================

/// Test: RefCell is allowed in normal mode
#[test]
fn interior_mut_refcell_allowed() {
    let mut body = create_body_with_locals(vec![
        MirType::Unit,
        MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell),
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![Statement::Nop],
        terminator: Some(Terminator::Return),
    });

    // Normal linter should not error on RefCell
    let mut checker = NllChecker::new(&body);
    checker.check();
    let result = checker.into_result();

    // Borrow checking itself passes
    assert!(result.is_ok(), "RefCell types should pass borrow check");
}

/// Test: RefCell flagged in panic-free profile
#[test]
fn interior_mut_refcell_flagged_panic_free() {
    let mut body = create_body_with_locals(vec![
        MirType::Unit,
        MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell),
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![Statement::Nop],
        terminator: Some(Terminator::Return),
    });

    let mut linter = PanicFreeLinter::new(&body);
    linter.check();

    assert!(
        !linter.errors.is_empty(),
        "Panic-free profile should flag RefCell usage"
    );
    assert!(
        linter.errors[0].contains("interior mutability"),
        "Error should mention interior mutability"
    );
}

/// Test: Mutex is rejected in panic-free profile
#[test]
fn interior_mut_mutex_rejected_panic_free() {
    let mut body = create_body_with_locals(vec![
        MirType::Unit,
        MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::Mutex),
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![Statement::Nop],
        terminator: Some(Terminator::Return),
    });

    let mut linter = PanicFreeLinter::new(&body);
    linter.check();

    assert!(
        !linter.errors.is_empty(),
        "Panic-free profile should reject Mutex: {:?}",
        linter.errors
    );
}

/// Test: Atomic is rejected in panic-free profile
#[test]
fn interior_mut_atomic_rejected_panic_free() {
    let mut body = create_body_with_locals(vec![
        MirType::Unit,
        MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::Atomic),
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![Statement::Nop],
        terminator: Some(Terminator::Return),
    });

    let mut linter = PanicFreeLinter::new(&body);
    linter.check();

    assert!(
        !linter.errors.is_empty(),
        "Panic-free profile should reject Atomic"
    );
}

/// Test: Indexing is rejected in panic-free profile
#[test]
fn panic_free_rejects_indexing() {
    let mut body = create_body_with_locals(vec![
        MirType::Unit,
        MirType::Nat, // container placeholder
        MirType::Nat, // index
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::RuntimeCheck(RuntimeCheckKind::BoundsCheck {
                local: Local(1),
                index: Local(2),
            }),
            Statement::Assign(Place::from(Local(0)), Rvalue::Use(nat_const(0))),
        ],
        terminator: Some(Terminator::Return),
    });

    let mut linter = PanicFreeLinter::new(&body);
    linter.check();

    assert!(
        linter.errors.iter().any(|e| e.contains("Indexing")),
        "Panic-free profile should reject indexing: {:?}",
        linter.errors
    );
}

/// Test: Index projection without a bounds check is still rejected in panic-free profile
#[test]
fn panic_free_rejects_index_projection_without_bounds_check() {
    let mut body = create_body_with_locals(vec![
        MirType::Unit,
        MirType::Nat, // container placeholder
        MirType::Nat, // index
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![Statement::Assign(
            Place::from(Local(0)),
            Rvalue::Use(Operand::Move(Place {
                local: Local(1),
                projection: vec![PlaceElem::Index(Local(2))],
            })),
        )],
        terminator: Some(Terminator::Return),
    });

    let mut linter = PanicFreeLinter::new(&body);
    linter.check();

    assert!(
        linter.errors.iter().any(|e| e.contains("Indexing")),
        "Panic-free profile should reject index projection: {:?}",
        linter.errors
    );
}

/// Test: Borrow axioms are rejected in panic-free profile
#[test]
fn panic_free_rejects_borrow_axioms() {
    let mut body = create_body_with_locals(vec![
        MirType::Unit,
        MirType::Nat,
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not),
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let mut linter = PanicFreeLinter::new(&body);
    linter.check();

    assert!(
        linter.errors.iter().any(|e| e.contains("Borrowing")),
        "Panic-free profile should reject borrow axioms: {:?}",
        linter.errors
    );
}

// =============================================================================
// BORROW CHECK RESULT API TESTS
// =============================================================================

/// Stress: Large CFG should not blow up NLL region storage
#[test]
fn nll_stress_cfg_size() {
    let num_blocks = 200;
    let mut body = create_body_with_locals(vec![
        MirType::Nat,                                                     // _0: return
        MirType::Nat,                                                     // _1: x
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // _2: r
        MirType::Nat,                                                     // _3: tmp
    ]);

    for i in 0..num_blocks {
        let mut statements = Vec::new();
        if i == 0 {
            statements.push(Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(nat_const(0)),
            ));
            statements.push(Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ));
        }
        statements.push(Statement::Assign(
            Place::from(Local(3)),
            Rvalue::Use(Operand::Copy(Place {
                local: Local(2),
                projection: vec![PlaceElem::Deref],
            })),
        ));

        let terminator = if i + 1 < num_blocks {
            Terminator::Goto {
                target: BasicBlock((i + 1) as u32),
            }
        } else {
            Terminator::Return
        };

        body.basic_blocks.push(BasicBlockData {
            statements,
            terminator: Some(terminator),
        });
    }

    let result = check_accepts(&body);
    assert!(
        result.is_ok(),
        "Large CFG should still pass NLL. Errors: {:?}",
        result.errors
    );
    assert!(
        !result.loans_with_ranges.is_empty(),
        "Expected at least one loan"
    );
    assert!(
        !result.loans_with_ranges[0].live_at.is_empty(),
        "Loan should have a live range"
    );
}

/// Test: BorrowCheckResult provides useful information
#[test]
fn borrowck_result_api() {
    let mut body = create_body_with_locals(vec![
        MirType::Nat,
        MirType::Nat,
        MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not),
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                })),
            ),
        ],
        terminator: Some(Terminator::Return),
    });

    let result = check_accepts(&body);

    // Test API methods
    assert!(result.is_ok());
    assert!(!result.loans_with_ranges.is_empty(), "Should have loans");

    // Test active_loans_at
    let loc = Location::new(BasicBlock(0), 2);
    let active = result.active_loans_at(loc);
    assert!(!active.is_empty(), "Should have active loan at use site");
}
