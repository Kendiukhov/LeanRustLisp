#[cfg(test)]
mod tests {
    use crate::analysis::nll::NllChecker;
    use crate::types::{AdtId, CtorId, MirType, Mutability, Region};
    use crate::LocalDecl;
    use crate::*;
    use kernel::ast::FunctionKind;

    // Helper to create a body with N locals of type Nat
    fn create_body(locals: usize) -> Body {
        let mut body = Body::new(0);
        for _ in 0..=locals {
            body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        }
        body
    }

    // Helper to add a reference local
    fn add_ref_local(body: &mut Body, inner: MirType, mutability: Mutability) -> Local {
        let idx = body.local_decls.len();
        body.local_decls.push(LocalDecl::new(
            MirType::Ref(Region(idx), Box::new(inner), mutability),
            None,
        ));
        Local(idx as u32)
    }

    // -------------------------------------------------------------------------
    // ACCEPTED CASES
    // -------------------------------------------------------------------------

    #[test]
    fn test_nll_accept_basic_borrow() {
        // let mut x = 0;
        // let y = &x;
        // let z = *y;
        let mut body = create_body(1);
        let l_y = add_ref_local(&mut body, MirType::Nat, Mutability::Not);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(l_y),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: l_y,
                        projection: vec![PlaceElem::Deref],
                    })),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(checker.errors.is_empty(), "Basic borrow should pass");
    }

    #[test]
    fn test_nll_accept_mutation_after_loan_end() {
        // let mut x = 0;
        // let y = &x;
        // let z = *y; // last use of y
        // x = 1; // Allowed in NLL because y is dead
        let mut body = create_body(1);
        let l_y = add_ref_local(&mut body, MirType::Nat, Mutability::Not);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(l_y),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: l_y,
                        projection: vec![PlaceElem::Deref],
                    })),
                ), // Read y
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(1),
                        ty: MirType::Nat,
                    }))),
                ), // Mutate x
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            checker.errors.is_empty(),
            "Mutation after last use should pass in NLL"
        );
    }

    #[test]
    fn test_nll_accept_reborrow() {
        // let mut x = 0;
        // let y = &mut x;
        // let z = &mut *y; // Reborrow
        // *z = 1;
        let mut body = create_body(1);
        let l_y = add_ref_local(&mut body, MirType::Nat, Mutability::Mut);
        let l_z = add_ref_local(&mut body, MirType::Nat, Mutability::Mut);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(l_y),
                    Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(l_z),
                    Rvalue::Ref(
                        BorrowKind::Mut,
                        Place {
                            local: l_y,
                            projection: vec![PlaceElem::Deref],
                        },
                    ),
                ),
                Statement::Assign(
                    Place {
                        local: l_z,
                        projection: vec![PlaceElem::Deref],
                    },
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(1),
                        ty: MirType::Nat,
                    }))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(checker.errors.is_empty(), "Reborrow should pass");
    }

    #[test]
    fn test_nll_accept_cond_branch_borrow() {
        let mut body = create_body(1);
        let l_y = add_ref_local(&mut body, MirType::Nat, Mutability::Not);

        // BB0: Switch
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(0),
                    ty: MirType::Nat,
                }))),
            )],
            terminator: Some(Terminator::SwitchInt {
                discr: Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(0),
                    ty: MirType::Nat,
                })),
                targets: SwitchTargets {
                    values: vec![0],
                    targets: vec![BasicBlock(1), BasicBlock(2)],
                },
            }),
        });

        // BB1: Borrow
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(l_y),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: l_y,
                        projection: vec![PlaceElem::Deref],
                    })),
                ),
            ],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(3),
            }),
        });

        // BB2: No Borrow
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(3),
            }),
        });

        // BB3: Mutate x (y is dead here)
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(1),
                    ty: MirType::Nat,
                }))),
            )],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            checker.errors.is_empty(),
            "Conditional borrow end should allow mutation"
        );
    }

    #[test]
    fn test_nll_rejects_call_return_ref_escape() {
        // let x = 0;
        // let r = &x;
        // let out = id_ref(r);
        // drop r; drop x;
        // use(*out); // ERROR: out still tied to x via call constraints

        let shared_ref = MirType::Ref(Region(5), Box::new(MirType::Nat), Mutability::Not);
        let mut body = Body::new(0);
        body.local_decls
            .push(LocalDecl::new(MirType::Unit, Some("_return".to_string()))); // _0
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("x".to_string()))); // _1
        body.local_decls.push(LocalDecl::new(
            MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not),
            Some("r".to_string()),
        )); // _2
        body.local_decls.push(LocalDecl::new(
            MirType::Ref(Region(3), Box::new(MirType::Nat), Mutability::Not),
            Some("out".to_string()),
        )); // _3
        body.local_decls.push(LocalDecl::new(
            MirType::Fn(
                FunctionKind::Fn,
                vec![Region(5)],
                vec![shared_ref.clone()],
                Box::new(shared_ref.clone()),
            ),
            Some("id_ref".to_string()),
        )); // _4

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(Local(4)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Unit,
                        ty: MirType::Unit,
                    }))),
                ),
            ],
            terminator: Some(Terminator::Call {
                func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(4))),
                args: vec![Operand::Copy(Place::from(Local(2)))],
                destination: Place::from(Local(3)),
                target: Some(BasicBlock(1)),
            }),
        });

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::StorageDead(Local(2)),
                Statement::StorageDead(Local(1)),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: Local(3),
                        projection: vec![PlaceElem::Deref],
                    })),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            !checker.errors.is_empty(),
            "Call return should keep borrow live across x drop"
        );
    }

    #[test]
    fn test_nll_accept_loop_reborrow() {
        // loop {
        //   let y = &x;
        //   use(y);
        // }
        // x = 1;
        let mut body = create_body(1);
        let l_y = add_ref_local(&mut body, MirType::Nat, Mutability::Not);

        // BB0: Init
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(0),
                    ty: MirType::Nat,
                }))),
            )],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(1),
            }),
        });

        // BB1: Loop Body
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(l_y),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: l_y,
                        projection: vec![PlaceElem::Deref],
                    })),
                ),
            ],
            terminator: Some(Terminator::SwitchInt {
                discr: Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(0),
                    ty: MirType::Nat,
                })),
                targets: SwitchTargets {
                    values: vec![0],
                    targets: vec![BasicBlock(1), BasicBlock(2)],
                }, // Loop back to 1 or exit to 2
            }),
        });

        // BB2: Exit and Mutate
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(1),
                    ty: MirType::Nat,
                }))),
            )],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            checker.errors.is_empty(),
            "Loop borrowing locally should be fine"
        );
    }

    #[test]
    fn test_nll_accept_early_return_borrow_branch() {
        // if cond { let y = &x; use(y); return; } else { x = 1; return; }
        let mut body = create_body(1);
        let l_y = add_ref_local(&mut body, MirType::Nat, Mutability::Not);

        // BB0: init and branch
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(0),
                    ty: MirType::Nat,
                }))),
            )],
            terminator: Some(Terminator::SwitchInt {
                discr: Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(0),
                    ty: MirType::Nat,
                })),
                targets: SwitchTargets {
                    values: vec![0],
                    targets: vec![BasicBlock(1), BasicBlock(2)],
                },
            }),
        });

        // BB1: borrow and return
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(l_y),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: l_y,
                        projection: vec![PlaceElem::Deref],
                    })),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        // BB2: mutate and return
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(1),
                    ty: MirType::Nat,
                }))),
            )],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            checker.errors.is_empty(),
            "Borrow on early-return path should not block other path"
        );
    }

    #[test]
    fn test_nll_accept_mut_after_shared_reborrow_ends() {
        // let mut x = 0;
        // let y = &mut x;
        // let z = &*y;
        // use(z); // last use of z
        // *y = 1; // Allowed after z ends
        let mut body = create_body(1);
        let l_y = add_ref_local(&mut body, MirType::Nat, Mutability::Mut);
        let l_z = add_ref_local(&mut body, MirType::Nat, Mutability::Not);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(l_y),
                    Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(l_z),
                    Rvalue::Ref(
                        BorrowKind::Shared,
                        Place {
                            local: l_y,
                            projection: vec![PlaceElem::Deref],
                        },
                    ),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: l_z,
                        projection: vec![PlaceElem::Deref],
                    })),
                ),
                Statement::Assign(
                    Place {
                        local: l_y,
                        projection: vec![PlaceElem::Deref],
                    },
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(1),
                        ty: MirType::Nat,
                    }))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            checker.errors.is_empty(),
            "Mutating after shared reborrow ends should be allowed"
        );
    }

    #[test]
    fn test_nll_accept_reborrow_chain_across_blocks() {
        // let mut x = 0;
        // let y = &mut x;
        // let z = &mut *y;
        // *z = 1;
        // *y = 2; // Allowed after z ends
        let mut body = create_body(1);
        let l_y = add_ref_local(&mut body, MirType::Nat, Mutability::Mut);
        let l_z = add_ref_local(&mut body, MirType::Nat, Mutability::Mut);

        // BB0: init and borrow y
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(l_y),
                    Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
                ),
            ],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(1),
            }),
        });

        // BB1: reborrow z
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(l_z),
                Rvalue::Ref(
                    BorrowKind::Mut,
                    Place {
                        local: l_y,
                        projection: vec![PlaceElem::Deref],
                    },
                ),
            )],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(2),
            }),
        });

        // BB2: use z
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place {
                    local: l_z,
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(1),
                    ty: MirType::Nat,
                }))),
            )],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(3),
            }),
        });

        // BB3: use y after z ends
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place {
                    local: l_y,
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(2),
                    ty: MirType::Nat,
                }))),
            )],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            checker.errors.is_empty(),
            "Reborrow chain across blocks should allow y after z ends"
        );
    }

    // -------------------------------------------------------------------------
    // REJECTED CASES
    // -------------------------------------------------------------------------

    #[test]
    fn test_nll_reject_mutate_while_borrowed() {
        // let mut x = 0;
        // let y = &x;
        // x = 1; // Conflict
        // let z = *y; // Use extends loan
        let mut body = create_body(1);
        let l_y = add_ref_local(&mut body, MirType::Nat, Mutability::Not);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(l_y),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(1),
                        ty: MirType::Nat,
                    }))),
                ), // Mutate x
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: l_y,
                        projection: vec![PlaceElem::Deref],
                    })),
                ), // Use y
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            !checker.errors.is_empty(),
            "Should reject mutation while borrowed"
        );
    }

    #[test]
    fn test_nll_reject_mutate_during_shared_reborrow_from_mut() {
        // let mut x = 0;
        // let y = &mut x;
        // let z = &*y;
        // *y = 1; // Conflict: z is live
        // use(z);
        let mut body = create_body(1);
        let l_y = add_ref_local(&mut body, MirType::Nat, Mutability::Mut);
        let l_z = add_ref_local(&mut body, MirType::Nat, Mutability::Not);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(l_y),
                    Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(l_z),
                    Rvalue::Ref(
                        BorrowKind::Shared,
                        Place {
                            local: l_y,
                            projection: vec![PlaceElem::Deref],
                        },
                    ),
                ),
                Statement::Assign(
                    Place {
                        local: l_y,
                        projection: vec![PlaceElem::Deref],
                    },
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(1),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: l_z,
                        projection: vec![PlaceElem::Deref],
                    })),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            !checker.errors.is_empty(),
            "Shared reborrow should block mutable use until it ends"
        );
    }

    #[test]
    fn test_nll_reject_borrow_live_across_loop_mutation() {
        // Regression: borrow is live across loop backedge.
        // let x = 0;
        // let y = &x;
        // loop { x = 1; }
        // use(y);
        let mut body = create_body(1);
        let l_y = add_ref_local(&mut body, MirType::Nat, Mutability::Not);

        // BB0: init and borrow
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(l_y),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
            ],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(1),
            }),
        });

        // BB1: mutate in loop, or exit
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(1),
                    ty: MirType::Nat,
                }))),
            )],
            terminator: Some(Terminator::SwitchInt {
                discr: Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(0),
                    ty: MirType::Nat,
                })),
                targets: SwitchTargets {
                    values: vec![0],
                    targets: vec![BasicBlock(1), BasicBlock(2)],
                },
            }),
        });

        // BB2: use y after loop exit
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: l_y,
                    projection: vec![PlaceElem::Deref],
                })),
            )],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            !checker.errors.is_empty(),
            "Borrow live across loop should reject mutation in loop"
        );
    }

    #[test]
    fn test_nll_reject_mut_borrow_alias() {
        // let mut x = 0;
        // let y = &mut x;
        // let z = &x; // Conflict: read while mutably borrowed
        // *y = 1;
        let mut body = create_body(1);
        let l_y = add_ref_local(&mut body, MirType::Nat, Mutability::Mut);
        let l_z = add_ref_local(&mut body, MirType::Nat, Mutability::Not);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(l_y),
                    Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(l_z),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ), // Read x
                Statement::Assign(
                    Place {
                        local: l_y,
                        projection: vec![PlaceElem::Deref],
                    },
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(1),
                        ty: MirType::Nat,
                    }))),
                ), // Use y
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(!checker.errors.is_empty());
    }

    #[test]
    fn test_nll_reject_drop_while_borrowed() {
        // let x = 0;
        // let y = &x;
        // drop(x); // Error
        // use(y);
        let mut body = create_body(1);
        let l_y = add_ref_local(&mut body, MirType::Nat, Mutability::Not);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(l_y),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::StorageDead(Local(1)),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: l_y,
                        projection: vec![PlaceElem::Deref],
                    })),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(!checker.errors.is_empty());
    }

    #[test]
    fn test_nll_reject_two_phase_borrow_conservative() {
        // x.f(&mut x) -> tmp = &mut x; f(tmp, &x) -> Error in MVP
        // let mut x = 0;
        // let tmp = &mut x;
        // let arg = &x; // Conflict!
        // *tmp = 1;
        let mut body = create_body(1);
        let l_tmp = add_ref_local(&mut body, MirType::Nat, Mutability::Mut);
        let l_arg = add_ref_local(&mut body, MirType::Nat, Mutability::Not);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(l_tmp),
                    Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(l_arg),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place {
                        local: l_tmp,
                        projection: vec![PlaceElem::Deref],
                    },
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(1),
                        ty: MirType::Nat,
                    }))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            !checker.errors.is_empty(),
            "MVP should reject two-phase borrow pattern"
        );
    }

    // -------------------------------------------------------------------------
    // NO-NAME-DEPENDENCE TESTS (Section 6.3 of contract)
    // These tests prove that naming variables/types "Ref", "Mut", etc.
    // does NOT affect borrow checking behavior.
    // -------------------------------------------------------------------------

    /// Test that a user-defined ADT named "Ref" doesn't confuse the borrow checker
    #[test]
    fn test_no_name_dependence_user_type_named_ref() {
        // User defines: struct Ref { value: Nat }
        // This should NOT be treated as a reference type
        let mut body = create_body(1);

        // Add a local with a user-defined type named "Ref"
        let ref_adt = AdtId::new("Ref");
        let user_ref_type = MirType::Adt(ref_adt.clone(), vec![MirType::Nat]);
        body.local_decls.push(LocalDecl::new(
            user_ref_type.clone(),
            Some("my_ref".to_string()),
        ));
        let l_ref = Local(body.local_decls.len() as u32 - 1);

        // This should be allowed: moving a user "Ref" type twice would fail ownership,
        // but copying the same place twice is fine for Copy types
        // The key test: the borrow checker should NOT treat "Ref" specially
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                // Assign to the user Ref type
                Statement::Assign(
                    Place::from(l_ref),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::InductiveCtor(CtorId::new(ref_adt.clone(), 0), 1, 1),
                        ty: user_ref_type.clone(),
                    }))),
                ),
                // Use it - should work, no special borrow semantics
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Move(Place::from(l_ref))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        // The user type "Ref" is NOT treated as a reference - no special handling
        assert!(
            checker.errors.is_empty(),
            "User type named 'Ref' should not trigger special borrow semantics"
        );
    }

    /// Test that a user-defined ADT named "Mut" doesn't confuse the borrow checker
    #[test]
    fn test_no_name_dependence_user_type_named_mut() {
        // User defines: struct Mut { value: Nat }
        let mut body = create_body(1);

        let mut_adt = AdtId::new("Mut");
        let user_mut_type = MirType::Adt(mut_adt.clone(), vec![]);
        body.local_decls.push(LocalDecl::new(
            user_mut_type.clone(),
            Some("my_mut".to_string()),
        ));
        let l_mut = Local(body.local_decls.len() as u32 - 1);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(l_mut),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::InductiveCtor(CtorId::new(mut_adt.clone(), 0), 0, 0),
                        ty: user_mut_type.clone(),
                    }))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Move(Place::from(l_mut))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            checker.errors.is_empty(),
            "User type named 'Mut' should not trigger special borrow semantics"
        );
    }

    /// Test that a user-defined type named "Shared" doesn't confuse the borrow checker
    #[test]
    fn test_no_name_dependence_user_type_named_shared() {
        let mut body = create_body(1);

        let shared_adt = AdtId::new("Shared");
        let user_shared_type = MirType::Adt(shared_adt.clone(), vec![]);
        body.local_decls.push(LocalDecl::new(
            user_shared_type.clone(),
            Some("my_shared".to_string()),
        ));
        let l_shared = Local(body.local_decls.len() as u32 - 1);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(l_shared),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::InductiveCtor(CtorId::new(shared_adt.clone(), 0), 0, 0),
                        ty: user_shared_type.clone(),
                    }))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Move(Place::from(l_shared))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            checker.errors.is_empty(),
            "User type named 'Shared' should not trigger special borrow semantics"
        );
    }

    /// Test that renaming a local variable to "borrow" doesn't affect checking
    #[test]
    fn test_no_name_dependence_variable_named_borrow() {
        let mut body = create_body(1);
        let l_ref = add_ref_local(&mut body, MirType::Nat, Mutability::Not);

        // Give the reference local a suspicious name
        body.local_decls[l_ref.index()].name = Some("borrow".to_string());

        // Standard borrow pattern - should work regardless of variable name
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(l_ref),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: l_ref,
                        projection: vec![PlaceElem::Deref],
                    })),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            checker.errors.is_empty(),
            "Variable named 'borrow' should work normally"
        );
    }

    /// Test that multiple user types with borrow-related names work correctly
    #[test]
    fn test_no_name_dependence_combined() {
        // Create a scenario with user types named Ref, Mut, Borrow, Shared, Lifetime
        let mut body = create_body(1);

        let types = vec![
            ("Ref", MirType::Adt(AdtId::new("Ref"), vec![])),
            ("Mut", MirType::Adt(AdtId::new("Mut"), vec![])),
            ("Borrow", MirType::Adt(AdtId::new("Borrow"), vec![])),
            ("Shared", MirType::Adt(AdtId::new("Shared"), vec![])),
            ("Lifetime", MirType::Adt(AdtId::new("Lifetime"), vec![])),
        ];

        let mut locals = vec![];
        for (name, ty) in &types {
            body.local_decls
                .push(LocalDecl::new(ty.clone(), Some(name.to_string())));
            locals.push(Local(body.local_decls.len() as u32 - 1));
        }

        // None of these should be treated specially
        let mut statements = vec![];
        for (i, (name, ty)) in types.iter().enumerate() {
            statements.push(Statement::Assign(
                Place::from(locals[i]),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::InductiveCtor(CtorId::new(AdtId::new(name), 0), 0, 0),
                    ty: ty.clone(),
                }))),
            ));
        }

        body.basic_blocks.push(BasicBlockData {
            statements,
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        assert!(
            checker.errors.is_empty(),
            "User types with borrow-related names should not affect checking"
        );
    }

    /// Prove that ACTUAL references are distinguished by MirType::Ref, not by name
    #[test]
    fn test_name_vs_type_distinction() {
        let mut body = create_body(1);

        // Create an actual MirType::Ref (this SHOULD be treated as a reference)
        let actual_ref = MirType::Ref(Region(1), Box::new(MirType::Nat), Mutability::Not);
        body.local_decls
            .push(LocalDecl::new(actual_ref, Some("not_a_ref".to_string())));
        let l_actual = Local(body.local_decls.len() as u32 - 1);

        // Create a user type named "ActualRef" (this should NOT be treated as a reference)
        let actual_ref_adt = AdtId::new("ActualRef");
        let fake_ref = MirType::Adt(actual_ref_adt.clone(), vec![]);
        body.local_decls.push(LocalDecl::new(
            fake_ref.clone(),
            Some("looks_like_ref".to_string()),
        ));
        let l_fake = Local(body.local_decls.len() as u32 - 1);

        // Borrow Local(1) into the actual reference
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(l_actual),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(l_fake),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::InductiveCtor(
                            CtorId::new(actual_ref_adt.clone(), 0),
                            0,
                            0,
                        ),
                        ty: fake_ref.clone(),
                    }))),
                ),
                // Mutate Local(1) while l_actual is alive - should fail!
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(1),
                        ty: MirType::Nat,
                    }))),
                ),
                // Use l_actual - this makes the borrow active at the mutation point
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: l_actual,
                        projection: vec![PlaceElem::Deref],
                    })),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();

        // The actual MirType::Ref SHOULD cause a borrow error
        // The user type "ActualRef" should have no effect
        assert!(!checker.errors.is_empty(),
            "MirType::Ref (named 'not_a_ref') should still cause borrow error, proving type-based not name-based checking");
    }
}
