//! Golden snapshot tests for MIR.
//!
//! These tests verify that MIR output remains stable across changes.

#[cfg(test)]
mod tests {
    use crate::pretty::pretty_print_body;
    use crate::types::*;
    use crate::*;
    use kernel::ast::{BinderInfo, Constructor, FunctionKind, InductiveDecl, Level, Term};
    use kernel::checker::Env;

    /// Snapshot: Simple identity function
    /// MIR for: fn identity(x: Nat) -> Nat { x }
    #[test]
    fn snapshot_identity() {
        let mut body = Body::new(1);
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("_return".to_string())));
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("x".to_string())));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
            )],
            terminator: Some(Terminator::Return),
        });

        let output = pretty_print_body(&body);
        let expected = r#"fn (arg_count: 1) {
    // Locals:
    //   _0: Nat (_return) [copy]
    //   _1: Nat (x) [copy]

    bb0: {
        _0 = copy _1;
        return
    }

}
"#;
        assert_eq!(output, expected, "Identity function MIR snapshot mismatch");
    }

    /// Snapshot: Borrow and dereference
    /// MIR for: fn deref_borrow(x: Nat) -> Nat { let r = &x; *r }
    #[test]
    fn snapshot_borrow_deref() {
        let mut body = Body::new(1);
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("_return".to_string())));
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("x".to_string())));
        body.local_decls.push(LocalDecl::new(
            MirType::Ref(Region(1), Box::new(MirType::Nat), Mutability::Not),
            Some("r".to_string()),
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
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

        let output = pretty_print_body(&body);
        let expected = r#"fn (arg_count: 1) {
    // Locals:
    //   _0: Nat (_return) [copy]
    //   _1: Nat (x) [copy]
    //   _2: &'1 Nat (r) [copy]

    bb0: {
        _2 = &_1;
        _0 = copy (*_2);
        return
    }

}
"#;
        assert_eq!(output, expected, "Borrow/deref MIR snapshot mismatch");
    }

    /// Snapshot: Opaque type is printed explicitly
    #[test]
    fn snapshot_opaque_local() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(
            MirType::Opaque {
                reason: "unsupported".to_string(),
            },
            Some("_return".to_string()),
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let output = pretty_print_body(&body);
        let expected = r#"fn (arg_count: 0) {
    // Locals:
    //   _0: Opaque (_return)

    bb0: {
        return
    }

}
"#;
        assert_eq!(output, expected, "Opaque MIR snapshot mismatch");
    }

    /// Snapshot: Mutable borrow and assignment
    /// MIR for: fn mutate(x: &mut Nat) { *x = 42 }
    #[test]
    fn snapshot_mut_borrow() {
        let mut body = Body::new(1);
        body.local_decls
            .push(LocalDecl::new(MirType::Unit, Some("_return".to_string())));
        body.local_decls.push(LocalDecl::new(
            MirType::Ref(Region(1), Box::new(MirType::Nat), Mutability::Mut),
            Some("x".to_string()),
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place {
                    local: Local(1),
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(42),
                    ty: MirType::Nat,
                }))),
            )],
            terminator: Some(Terminator::Return),
        });

        let output = pretty_print_body(&body);
        let expected = r#"fn (arg_count: 1) {
    // Locals:
    //   _0: () (_return) [copy]
    //   _1: &'1 mut Nat (x)

    bb0: {
        (*_1) = 42_nat;
        return
    }

}
"#;
        assert_eq!(output, expected, "Mut borrow MIR snapshot mismatch");
    }

    /// Snapshot: Conditional branch
    /// MIR for: fn branch(c: Bool) -> Nat { if c { 1 } else { 0 } }
    #[test]
    fn snapshot_conditional() {
        let mut body = Body::new(1);
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("_return".to_string())));
        body.local_decls
            .push(LocalDecl::new(MirType::Bool, Some("c".to_string())));

        // bb0: switch on c
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::SwitchInt {
                discr: Operand::Copy(Place::from(Local(1))),
                targets: SwitchTargets {
                    values: vec![0],                             // false = 0
                    targets: vec![BasicBlock(2), BasicBlock(1)], // false -> bb2, true -> bb1
                },
            }),
        });

        // bb1: true branch
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(1),
                    ty: MirType::Nat,
                }))),
            )],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(3),
            }),
        });

        // bb2: false branch
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Nat(0),
                    ty: MirType::Nat,
                }))),
            )],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(3),
            }),
        });

        // bb3: join
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let output = pretty_print_body(&body);
        let expected = r#"fn (arg_count: 1) {
    // Locals:
    //   _0: Nat (_return) [copy]
    //   _1: Bool (c) [copy]

    bb0: {
        switchInt(copy _1) -> [0: bb2, otherwise: bb1]
    }

    bb1: {
        _0 = 1_nat;
        goto -> bb3
    }

    bb2: {
        _0 = 0_nat;
        goto -> bb3
    }

    bb3: {
        return
    }

}
"#;
        assert_eq!(output, expected, "Conditional MIR snapshot mismatch");
    }

    /// Snapshot: Function type with region parameters
    #[test]
    fn snapshot_fn_type_with_regions() {
        let mut body = Body::new(0);
        body.local_decls
            .push(LocalDecl::new(MirType::Unit, Some("_return".to_string())));

        let region = Region(1);
        let fn_ty = MirType::Fn(
            FunctionKind::Fn,
            vec![region],
            vec![MirType::Ref(
                region,
                Box::new(MirType::Nat),
                Mutability::Not,
            )],
            Box::new(MirType::Ref(
                region,
                Box::new(MirType::Nat),
                Mutability::Not,
            )),
        );
        body.local_decls
            .push(LocalDecl::new(fn_ty, Some("f".to_string())));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let output = pretty_print_body(&body);
        let expected = r#"fn (arg_count: 0) {
    // Locals:
    //   _0: () (_return) [copy]
    //   _1: fn<'1>(&'1 Nat) -> &'1 Nat (f)

    bb0: {
        return
    }

}
"#;
        assert_eq!(output, expected, "Fn type MIR snapshot mismatch");
    }

    /// Snapshot: Interior mutability type
    #[test]
    fn snapshot_interior_mutable() {
        let mut body = Body::new(0);
        body.local_decls
            .push(LocalDecl::new(MirType::Unit, Some("_return".to_string())));
        body.local_decls.push(LocalDecl::new(
            MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell),
            Some("cell".to_string()),
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Nop],
            terminator: Some(Terminator::Return),
        });

        let output = pretty_print_body(&body);
        assert!(output.contains("RefCell<Nat>"), "Should show RefCell type");
        assert!(output.contains("(cell)"), "Should show local name");
    }

    /// Snapshot: Function call
    #[test]
    fn snapshot_call() {
        let mut body = Body::new(1);
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("_return".to_string())));
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("x".to_string())));
        body.local_decls.push(LocalDecl::new(
            MirType::Fn(
                FunctionKind::Fn,
                Vec::new(),
                vec![MirType::Nat],
                Box::new(MirType::Nat),
            ),
            Some("f".to_string()),
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Call {
                func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(2))),
                args: vec![Operand::Move(Place::from(Local(1)))],
                destination: Place::from(Local(0)),
                target: Some(BasicBlock(1)),
            }),
        });

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let output = pretty_print_body(&body);
        assert!(
            output.contains("_0 = &_2(move _1) -> bb1"),
            "Should format call correctly"
        );
    }

    /// Snapshot: Storage markers
    #[test]
    fn snapshot_storage_markers() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("tmp".to_string())));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::StorageLive(Local(1)),
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::StorageDead(Local(1)),
            ],
            terminator: Some(Terminator::Return),
        });

        let output = pretty_print_body(&body);
        assert!(
            output.contains("StorageLive(_1)"),
            "Should have StorageLive"
        );
        assert!(
            output.contains("StorageDead(_1)"),
            "Should have StorageDead"
        );
    }

    /// Snapshot: Field projection
    #[test]
    fn snapshot_field_projection() {
        let mut body = Body::new(1);
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        body.local_decls.push(LocalDecl::new(
            MirType::Adt(AdtId::new("Pair"), vec![MirType::Nat, MirType::Bool]),
            Some("p".to_string()),
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(1),
                    projection: vec![PlaceElem::Field(0)],
                })),
            )],
            terminator: Some(Terminator::Return),
        });

        let output = pretty_print_body(&body);
        assert!(
            output.contains("_0 = copy _1.0"),
            "Should format field access"
        );
        assert!(output.contains("Pair<Nat, Bool>"), "Should format ADT type");
    }

    /// Snapshot: Param field is not erased to Unit
    #[test]
    fn snapshot_param_field_not_unit() {
        let mut env = Env::new();
        let sort1 = Term::sort(Level::Succ(Box::new(Level::Zero)));

        let token_decl = InductiveDecl::new(
            "Token".to_string(),
            sort1.clone(),
            vec![Constructor {
                name: "mkToken".to_string(),
                ty: Term::ind("Token".to_string()),
            }],
        );
        env.add_inductive(token_decl).expect("add Token");

        let box_ty = Term::pi(sort1.clone(), sort1.clone(), BinderInfo::Default);
        let box_ctor_ty = Term::pi(
            sort1,
            Term::pi(
                Term::var(0),
                Term::app(Term::ind("Box".to_string()), Term::var(1)),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let box_decl = InductiveDecl::new(
            "Box".to_string(),
            box_ty,
            vec![Constructor {
                name: "mkBox".to_string(),
                ty: box_ctor_ty,
            }],
        );
        env.add_inductive(box_decl).expect("add Box");

        let ids = IdRegistry::from_env(&env);
        let token_id = ids.adt_id("Token").expect("Token id");
        let box_id = ids.adt_id("Box").expect("Box id");

        let box_args = vec![MirType::Adt(token_id.clone(), vec![])];
        let field_ty = ids
            .adt_layouts()
            .field_type(&box_id, None, 0, &box_args)
            .unwrap_or(MirType::Unit);

        assert!(
            !matches!(field_ty, MirType::Unit),
            "Field type should not lower to Unit"
        );

        let mut body = Body::new(0);
        body.local_decls
            .push(LocalDecl::new(field_ty, Some("_return".to_string())));
        body.local_decls.push(LocalDecl::new(
            MirType::Adt(box_id, box_args),
            Some("b".to_string()),
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(1),
                    projection: vec![PlaceElem::Field(0)],
                })),
            )],
            terminator: Some(Terminator::Return),
        });

        let output = pretty_print_body(&body);
        assert!(output.contains("Token"), "Field type should be Token");
        assert!(output.contains("Box<Token>"), "Box should keep param type");
        assert!(
            !output.contains("_0: ()"),
            "Field type should not pretty-print as Unit"
        );
    }
}
