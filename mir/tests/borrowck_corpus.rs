//! Extended Borrow Checker Test Corpus
//!
//! This corpus tests NLL (Non-Lexical Lifetimes) semantics and
//! documents the expected accept/reject decisions for various patterns.

use mir::*;
use mir::types::*;
use mir::analysis::nll::{NllChecker, Location, BorrowCheckResult};
use mir::lints::PanicFreeLinter;

// =============================================================================
// HELPER FUNCTIONS
// =============================================================================

fn create_body_with_locals(local_types: Vec<MirType>) -> Body {
    let mut body = Body::new(0);
    for (i, ty) in local_types.into_iter().enumerate() {
        let name = if i == 0 { Some("_return".to_string()) } else { None };
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
        MirType::Nat,  // _0: return
        MirType::Nat,  // _1: x
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Not),  // _2: y
        MirType::Nat,  // _3: z
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
            Statement::Assign(Place::from(Local(0)), Rvalue::Use(Operand::Copy(Place::from(Local(3))))),
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
        MirType::Nat,  // _0: return
        MirType::Nat,  // _1: x
        MirType::Bool, // _2: cond
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Not),  // _3: y
    ]);

    // bb0: switch on cond
    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
        ],
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
        terminator: Some(Terminator::Goto { target: BasicBlock(3) }),
    });

    // bb2: mutation branch (no borrow)
    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(42))),
            Statement::Assign(Place::from(Local(0)), Rvalue::Use(Operand::Copy(Place::from(Local(1))))),
        ],
        terminator: Some(Terminator::Goto { target: BasicBlock(3) }),
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

/// NLL Accept: Reborrow of mutable reference
#[test]
fn nll_accept_reborrow() {
    // let x = 0;
    // let r = &mut x;
    // let r2 = &mut *r;  // reborrow
    // *r2 = 1;
    // // r can be used again after r2 dies

    let mut body = create_body_with_locals(vec![
        MirType::Nat,  // _0
        MirType::Nat,  // _1: x
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Mut),  // _2: r
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Mut),  // _3: r2
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
                Rvalue::Ref(BorrowKind::Mut, Place {
                    local: Local(2),
                    projection: vec![PlaceElem::Deref],
                }),
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
        MirType::Nat,  // _0
        MirType::Nat,  // _1: x
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Mut),  // _2: r
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Mut),  // _3: r2
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
                Rvalue::Ref(BorrowKind::Mut, Place { local: Local(2), projection: vec![PlaceElem::Deref] }),
            ),
            Statement::Assign(
                Place { local: Local(3), projection: vec![PlaceElem::Deref] },
                Rvalue::Use(nat_const(1)),
            ),
            Statement::Assign(
                Place { local: Local(2), projection: vec![PlaceElem::Deref] },
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
        MirType::Nat,  // _0
        MirType::Nat,  // _1: x
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Not),  // _2: y
        MirType::Nat,  // _3: temp
    ]);

    // bb0: init
    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
        ],
        terminator: Some(Terminator::Goto { target: BasicBlock(1) }),
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
            discr: nat_const(0),  // simplified: always exit
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
            Statement::Assign(Place::from(Local(0)), Rvalue::Use(Operand::Copy(Place::from(Local(1))))),
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

/// NLL Accept: Disjoint field borrow and write
#[test]
fn nll_accept_disjoint_field_borrow() {
    // let p = Pair(...);
    // let r = &p.0;
    // p.1 = ...; // ok, disjoint field
    // use(*r);

    let pair_ty = MirType::Adt(AdtId("Pair".to_string()), vec![]);
    let mut body = create_body_with_locals(vec![
        MirType::Nat,  // _0
        pair_ty.clone(), // _1: p
        MirType::Ref(Region(0), Box::new(pair_ty.clone()), Mutability::Not), // _2: r
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::InductiveCtor("Pair".to_string(), 0, 0),
                    ty: pair_ty.clone(),
                }))),
            ),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(
                    BorrowKind::Shared,
                    Place { local: Local(1), projection: vec![PlaceElem::Field(0)] },
                ),
            ),
            Statement::Assign(
                Place { local: Local(1), projection: vec![PlaceElem::Field(1)] },
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::InductiveCtor("Pair".to_string(), 0, 0),
                    ty: pair_ty.clone(),
                }))),
            ),
            Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place { local: Local(2), projection: vec![PlaceElem::Deref] })),
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

// =============================================================================
// NLL REJECTION TESTS
// =============================================================================

/// NLL Reject: Use of mutable borrow while shared borrow active
#[test]
fn nll_reject_mut_while_shared() {
    // let x = 0;
    // let r = &x;
    // let m = &mut x;  // ERROR: can't borrow mutably while borrowed
    // use(*r);

    let mut body = create_body_with_locals(vec![
        MirType::Nat,
        MirType::Nat,  // x
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Not),   // r: &x
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Mut),   // m: &mut x
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
        MirType::Nat,  // x
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Not),  // r
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(1))),  // write!
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
        "NLL should reject: write while borrowed"
    );
}

/// NLL Reject: Write through shared reference
#[test]
fn nll_reject_shared_deref_write() {
    // let x = 0;
    // let r = &x;
    // *r = 1; // ERROR: shared ref

    let mut body = create_body_with_locals(vec![
        MirType::Nat,
        MirType::Nat,  // x
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Not),  // r
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::Assign(
                Place { local: Local(2), projection: vec![PlaceElem::Deref] },
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
        MirType::Nat,  // x
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Not),  // r
    ]);

    body.basic_blocks.push(BasicBlockData {
        statements: vec![
            Statement::Assign(Place::from(Local(1)), Rvalue::Use(nat_const(0))),
            Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            ),
            Statement::StorageDead(Local(1)),  // x dies
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

/// NLL Reject: Double mutable borrow
#[test]
fn nll_reject_double_mut_borrow() {
    // let x = 0;
    // let r1 = &mut x;
    // let r2 = &mut x;  // ERROR: x already mutably borrowed
    // *r1 = 1;

    let mut body = create_body_with_locals(vec![
        MirType::Nat,
        MirType::Nat,  // x
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Mut),  // r1
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Mut),  // r2
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
    assert!(
        !result.is_ok(),
        "NLL should reject: double mutable borrow"
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
        linter.errors[0].contains("RefCell"),
        "Error should mention RefCell"
    );
}

/// Test: Mutex is allowed in panic-free profile
#[test]
fn interior_mut_mutex_allowed_panic_free() {
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
        linter.errors.is_empty(),
        "Panic-free profile should allow Mutex: {:?}",
        linter.errors
    );
}

/// Test: Atomic is allowed everywhere
#[test]
fn interior_mut_atomic_allowed() {
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
        linter.errors.is_empty(),
        "Atomic should be allowed everywhere"
    );
}

// =============================================================================
// BORROW CHECK RESULT API TESTS
// =============================================================================

/// Test: BorrowCheckResult provides useful information
#[test]
fn borrowck_result_api() {
    let mut body = create_body_with_locals(vec![
        MirType::Nat,
        MirType::Nat,
        MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Not),
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
