pub mod ast;
#[cfg(test)]
mod test_support;
pub mod checker;
pub mod nbe;
pub mod ownership;

pub use ast::*;
pub use ast::{Totality, Definition, WellFoundedInfo};

/// Transparency levels for reduction
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Transparency {
    All,
    Reducible,
    Instances,
    None,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{InductiveDecl, Constructor, Term, Level};
    use crate::test_support::Parser;
    use crate::checker::{check, infer, Context, Env};
    use std::rc::Rc;

    #[test]
    fn test_identity_function() {
        // \x:Prop. x
        let input = "(lam (sort 0) 0)"; 
        let mut parser = Parser::new(input);
        let term = parser.parse_term().expect("Failed to parse");
        
        let env = Env::new();
        let ctx = Context::new();
        
        // Expected type: Prop -> Prop  => (pi (sort 0) (sort 0))
        let expected_input = "(pi (sort 0) (sort 0))";
        let mut parser2 = Parser::new(expected_input);
        let expected = parser2.parse_term().expect("Failed to parse expected");
        
        let inferred = infer(&env, &ctx, term.clone()).expect("Failed to infer");
        println!("Inferred: {:?}", inferred);
        
        check(&env, &ctx, term, expected).expect("Type check failed");
    }

    #[test]
    fn test_polymorphic_identity() {
        // \A:Prop. \x:A. x
        let input = "(lam (sort 0) (lam 0 0))";
        let mut parser = Parser::new(input);
        let term = parser.parse_term().expect("Failed to parse");

        let env = Env::new();
        let ctx = Context::new();

        // Expected type: (x:Prop) -> (y:x) -> x  => (pi (sort 0) (pi 0 1))
        let expected_input = "(pi (sort 0) (pi 0 1))";
        let mut parser2 = Parser::new(expected_input);
        let expected = parser2.parse_term().expect("Failed to parse expected");

        let inferred = infer(&env, &ctx, term.clone()).expect("Failed to infer");
        println!("Inferred Poly: {:?}", inferred);

        check(&env, &ctx, term, expected).expect("Type check failed");
    }

    #[test]
    fn test_nat_inductive() {
        use crate::ast::{Constructor, InductiveDecl, BinderInfo};
        // Register Nat: Type 0
        // Nat.zero : Nat
        // Nat.succ : Nat -> Nat
        let mut env = Env::new();
        
        let nat_ty = Term::sort(Level::Succ(Box::new(Level::Zero))); // Type 0
        let nat_ref = Term::ind("Nat".to_string());
        
        let nat_decl = InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: nat_ty.clone(),
            ctors: vec![
                Constructor {
                    name: "zero".to_string(),
                    ty: nat_ref.clone(), // zero : Nat
                },
                Constructor {
                    name: "succ".to_string(),
                    ty: Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default), // succ : Nat -> Nat
                },
            ],
            is_copy: true, // Nat has Copy semantics
        };

        env.add_inductive(nat_decl).expect("Failed to add Nat");
        let ctx = Context::new();
        
        // Check that (ind Nat) has type Type 0
        let ind_nat = Term::ind("Nat".to_string());
        let inferred = infer(&env, &ctx, ind_nat).expect("Failed to infer Nat");
        println!("Nat type: {:?}", inferred);
        assert!(matches!(&*inferred, Term::Sort(Level::Succ(_))));
        
        // Check that (ctor Nat 0) = zero has type Nat
        let zero = Term::ctor("Nat".to_string(), 0);
        let zero_ty = infer(&env, &ctx, zero).expect("Failed to infer zero");
        println!("zero type: {:?}", zero_ty);
        assert!(matches!(&*zero_ty, Term::Ind(name, _) if name == "Nat"));
        
        // Check that (ctor Nat 1) = succ has type Nat -> Nat
        let succ = Term::ctor("Nat".to_string(), 1);
        let succ_ty = infer(&env, &ctx, succ).expect("Failed to infer succ");
        println!("succ type: {:?}", succ_ty);
        assert!(matches!(&*succ_ty, Term::Pi(_, _, _)));
    }

    #[test]
    fn test_parse_ind_ctor() {
        // Test parsing (ind Nat)
        let input = "(ind Nat)";
        let mut parser = Parser::new(input);
        let term = parser.parse_term().expect("Failed to parse ind");
        assert!(matches!(&*term, Term::Ind(name, _) if name == "Nat"));
        
        // Test parsing (ctor Nat 0)
        let input2 = "(ctor Nat 0)";
        let mut parser2 = Parser::new(input2);
        let term2 = parser2.parse_term().expect("Failed to parse ctor");
        assert!(matches!(&*term2, Term::Ctor(name, 0, _) if name == "Nat"));
        
        // Test parsing (rec Nat)
        let input3 = "(rec Nat)";
        let mut parser3 = Parser::new(input3);
        let term3 = parser3.parse_term().expect("Failed to parse rec");
        assert!(matches!(&*term3, Term::Rec(name, _) if name == "Nat"));
    }

    #[test]
    fn test_unknown_inductive_error() {
        let env = Env::new();
        let ctx = Context::new();
        
        // Trying to infer type of unknown inductive should fail
        let ind = Term::ind("Unknown".to_string());
        let result = infer(&env, &ctx, ind);
        assert!(result.is_err());
    }

    #[test]
    fn test_recursor_type() {
        use crate::checker::compute_recursor_type;
        use crate::ast::BinderInfo;
        
        // Set up Nat inductive
        let mut env = Env::new();
        let nat_ty = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let nat_ref = Term::ind("Nat".to_string());
        
        let nat_decl = InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: nat_ty.clone(),
            ctors: vec![
                Constructor {
                    name: "zero".to_string(),
                    ty: nat_ref.clone(),
                },
                Constructor {
                    name: "succ".to_string(),
                    ty: Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default),
                },
            ],
            is_copy: true,
        };

        env.add_inductive(nat_decl.clone()).expect("Failed to add Nat");
        let ctx = Context::new();
        
        // Check that (rec Nat) has a Pi type (motive → ... → result)
        let rec_nat = Term::rec("Nat".to_string());
        let rec_ty = infer(&env, &ctx, rec_nat).expect("Failed to infer recursor type");
        println!("Nat.rec type: {:?}", rec_ty);
        
        // The computed type should be a Pi
        assert!(matches!(&*rec_ty, Term::Pi(_, _, _)));
        
        // Also test compute_recursor_type directly
        let computed = compute_recursor_type(&nat_decl, &[]);
        println!("Computed type: {:?}", computed);
        assert!(matches!(&*computed, Term::Pi(_, _, _)));
    }

    #[test]
    fn test_iota_reduction() {
        use crate::checker::whnf;
        use crate::ast::BinderInfo;
        
        // Set up Nat inductive with zero and succ
        let mut env = Env::new();
        let nat_ty = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let nat_ref = Term::ind("Nat".to_string());
        
        let nat_decl = InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: nat_ty.clone(),
            ctors: vec![
                Constructor {
                    name: "zero".to_string(),
                    ty: nat_ref.clone(),
                },
                Constructor {
                    name: "succ".to_string(),
                    ty: Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default),
                },
            ],
            is_copy: true,
        };

        env.add_inductive(nat_decl).expect("Failed to add Nat");

        // Build: Nat.rec motive base step zero
        // Where: motive = λ_. Nat, base = zero, step = λn. λih. succ ih
        let rec = Term::rec("Nat".to_string());
        let motive = Term::lam(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default); // λ_. Nat (constant motive)
        let base = Term::ctor("Nat".to_string(), 0); // zero
        let step = Term::lam(
            nat_ref.clone(),
            Term::lam(nat_ref.clone(), Term::app(Term::ctor("Nat".to_string(), 1), Term::var(0)), BinderInfo::Default),
            BinderInfo::Default
        ); // λn. λih. succ ih
        let major = Term::ctor("Nat".to_string(), 0); // zero
        
        // Apply: rec motive base step zero
        let app1 = Term::app(rec, motive);
        let app2 = Term::app(app1, base.clone());
        let app3 = Term::app(app2, step);
        let app4 = Term::app(app3, major);
        
        // After iota reduction, should reduce to base (zero)
        let result = whnf(&env, app4, crate::Transparency::All);
        println!("Iota reduction result: {:?}", result);
        
        // Result should be zero (ctor Nat 0)
        assert!(matches!(&*result, Term::Ctor(name, 0, _) if name == "Nat"));
    }

    #[test]
    fn test_universe_levels() {
        use crate::checker::{level_imax, level_max, reduce_level};
        use crate::ast::BinderInfo;
        
        let env = Env::new();
        let ctx = Context::new();
        
        let prop = Term::sort(Level::Zero);
        let type0 = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let type1 = Term::sort(Level::Succ(Box::new(Level::Succ(Box::new(Level::Zero)))));

        // Test 1: Prop → Prop has type Type 0 
        // (Pi Prop Prop) : Type 0 (since imax(1, 1) = 1)
        // Note: Prop itself is Type 0. Prop -> Prop is the type of functions mapping props to props.
        let prop_to_prop = Term::pi(
            Term::sort(Level::Zero),
            Term::sort(Level::Zero),
            BinderInfo::Default
        );
        let ty = infer(&env, &ctx, prop_to_prop).expect("Failed to infer Prop → Prop");
        println!("Prop → Prop : {:?}", ty);
        assert!(checker::is_def_eq(&env, ty, type0.clone(), crate::Transparency::All));

        // Test 1b: Impredicativity check
        // (p : Prop) -> p has type Prop
        // u1 = level(Prop) = 1
        // u2 = level(p) = 0
        // imax(1, 0) = 0
        let impredicative = Term::pi(
            Term::sort(Level::Zero), // domain: Prop
            Term::var(0),            // codomain: p
            BinderInfo::Default /* ast::BinderInfo */
        );
        let ty_impred = infer(&env, &ctx, impredicative).expect("Failed to infer (p:Prop) -> p");
        println!("(p:Prop) -> p : {:?}", ty_impred);
        assert!(checker::is_def_eq(&env, ty_impred, prop.clone(), crate::Transparency::All));
        
        // Test 2: Type 0 → Type 0 has type Type 1
        // (Pi (Type 0) (Type 0)) : Type 1 (since imax(2, 2) = 2)
        let type0_level = Level::Succ(Box::new(Level::Zero));
        let type0_to_type0 = Term::pi(
            Term::sort(type0_level.clone()),
            Term::sort(type0_level.clone()),
            BinderInfo::Default
        );
        let ty2 = infer(&env, &ctx, type0_to_type0).expect("Failed to infer Type 0 → Type 0");
        println!("Type 0 → Type 0 : {:?}", ty2);
        assert!(checker::is_def_eq(&env, ty2, type1.clone(), crate::Transparency::All));
        
        // Test 3: Prop → Type 0 has type Type 1
        // Domain Prop (u=1). Codomain Type 0 (v=2). imax(1, 2) = 2.
        let prop_to_type0 = Term::pi(
            Term::sort(Level::Zero),
            Term::sort(Level::Succ(Box::new(Level::Zero))),
            BinderInfo::Default
        );
        let ty3 = infer(&env, &ctx, prop_to_type0).expect("Failed to infer Prop → Type 0");
        println!("Prop → Type 0 : {:?}", ty3);
        assert!(checker::is_def_eq(&env, ty3, type1.clone(), crate::Transparency::All));
        
        // Test universe helper functions
        assert_eq!(reduce_level(level_imax(Level::Zero, Level::Zero)), Level::Zero);
        assert!(matches!(
            reduce_level(level_max(Level::Zero, Level::Succ(Box::new(Level::Zero)))),
            Level::Succ(_)
        ));
    }

    #[test]
    fn test_eta_reduction() {
        use crate::checker::is_def_eq;
        use crate::ast::BinderInfo;
        
        let env = Env::new();
        // Define f = (lam (sort 0) 0)  -- Identity function
        let f = Term::lam(Term::sort(Level::Zero), Term::var(0), BinderInfo::Default);
        
        // Define eta = (lam (sort 0) (app f 0))
        // Note: f must be shifted if it were a variable, but it's a closed term here?
        // Wait, f is constructed above. If we embed it in `eta`, does it need shifting?
        // Terms are immutable Rc. `f` has no free variables.
        // `eta` body: `app f 0`. 
        // `f` is closed, so no shift needed for embedding.
        let eta = Term::lam(
            Term::sort(Level::Zero), 
            Term::app(f.clone(), Term::var(0)),
            BinderInfo::Default
        );
        
        // Check if f == eta
        assert!(is_def_eq(&env, f, eta, crate::Transparency::All));
    }

    #[test]
    fn test_inductive_positivity_fail() {
        // Inductive Bad | mk : (Bad -> Prop) -> Bad
        use crate::ast::BinderInfo;
        let mut env = Env::new();
        let prop = Term::sort(Level::Zero);
        let bad_ref = Term::ind("Bad".to_string());

        let bad_decl = InductiveDecl {
            name: "Bad".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: prop.clone(),
            ctors: vec![
                Constructor {
                    name: "mk".to_string(),
                    // (Bad -> Prop) -> Bad
                    ty: Term::pi(
                        Term::pi(bad_ref.clone(), prop.clone(), BinderInfo::Default),
                        bad_ref.clone(),
                        BinderInfo::Default
                    ),
                }
            ],
            is_copy: false,
        };

        let result = env.add_inductive(bad_decl);
        assert!(result.is_err());
        match result {
            Err(crate::checker::TypeError::NonPositiveOccurrence(..)) => {}, // Expected
            _ => panic!("Expected NonPositiveOccurrence error, got {:?}", result),
        }
    }

    // =============================================================================
    // Phase 1D: Termination / Totality Tests
    // =============================================================================

    #[test]
    fn test_totality_markers() {
        use crate::ast::{Definition, Totality, BinderInfo};

        // Test that Definition correctly tracks totality
        let ty = Term::pi(Term::sort(Level::Zero), Term::sort(Level::Zero), BinderInfo::Default);
        let val = Term::lam(Term::sort(Level::Zero), Term::var(0), BinderInfo::Default);

        let total_def = Definition::total("id".to_string(), ty.clone(), val.clone());
        assert_eq!(total_def.totality, Totality::Total);
        assert!(total_def.is_type_safe());

        let partial_def = Definition::partial("loop".to_string(), ty.clone(), val.clone());
        assert_eq!(partial_def.totality, Totality::Partial);
        assert!(!partial_def.is_type_safe());

        let axiom_def = Definition::axiom("funext".to_string(), ty.clone());
        assert_eq!(axiom_def.totality, Totality::Axiom);
        assert!(axiom_def.is_type_safe());
        assert!(axiom_def.value.is_none());
    }

    #[test]
    fn test_termination_non_recursive() {
        use crate::checker::check_termination;
        use crate::ast::BinderInfo;

        let env = Env::new();

        // Non-recursive function: id : A -> A = \x. x
        let ty = Term::pi(Term::sort(Level::Zero), Term::sort(Level::Zero), BinderInfo::Default);
        let body = Term::lam(Term::sort(Level::Zero), Term::var(0), BinderInfo::Default);

        // Should pass - no recursion
        let result = check_termination(&env, "id", &ty, &body);
        assert!(result.is_ok(), "Non-recursive function should pass: {:?}", result);
    }

    #[test]
    fn test_termination_with_recursor() {
        use crate::checker::check_termination;
        use crate::ast::BinderInfo;

        // Set up Nat
        let mut env = Env::new();
        let nat_ty = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let nat_ref = Term::ind("Nat".to_string());

        let nat_decl = InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: nat_ty,
            ctors: vec![
                Constructor { name: "zero".to_string(), ty: nat_ref.clone() },
                Constructor { name: "succ".to_string(), ty: Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default) },
            ],
            is_copy: true,
        };
        env.add_inductive(nat_decl).unwrap();

        // Function using recursor: pred : Nat -> Nat
        // This uses Rec which encodes structural recursion - should be allowed
        let ty = Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default);
        let body = Term::lam(
            nat_ref.clone(),
            // Use recursor: Nat.rec _ zero (\n. \ih. n) x
            Term::app(
                Term::app(
                    Term::app(
                        Term::app(
                            Term::rec("Nat".to_string()),
                            Term::lam(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default), // motive
                        ),
                        Term::ctor("Nat".to_string(), 0), // zero case
                    ),
                    Term::lam(nat_ref.clone(), Term::lam(nat_ref.clone(), Term::var(1), BinderInfo::Default), BinderInfo::Default), // succ case
                ),
                Term::var(0), // argument
            ),
            BinderInfo::Default
        );

        // Should pass - uses recursor which guarantees termination
        let result = check_termination(&env, "pred", &ty, &body);
        assert!(result.is_ok(), "Function using recursor should pass: {:?}", result);
    }

    #[test]
    fn test_env_type_safety() {
        use crate::ast::{Definition, Totality, BinderInfo};

        let mut env = Env::new();
        let ty = Term::pi(Term::sort(Level::Zero), Term::sort(Level::Zero), BinderInfo::Default);
        let val = Term::lam(Term::sort(Level::Zero), Term::var(0), BinderInfo::Default);

        // Add a total definition
        let total_def = Definition::total("total_fn".to_string(), ty.clone(), val.clone());
        env.add_definition(total_def).unwrap();
        assert!(env.is_type_safe("total_fn"));

        // Add an axiom (assumed, but can appear in types)
        env.add_axiom("my_axiom".to_string(), ty.clone());
        assert!(env.is_type_safe("my_axiom"));

        // Check that get_definition works
        let def = env.get_definition("total_fn").unwrap();
        assert_eq!(def.totality, Totality::Total);

        let ax = env.get_definition("my_axiom").unwrap();
        assert_eq!(ax.totality, Totality::Axiom);
    }

    #[test]
    fn test_partial_in_type_rejected() {
        use crate::ast::{Definition, Totality, BinderInfo};
        use crate::checker::TypeError;

        let mut env = Env::new();

        // First add a partial definition
        let partial_ty = Term::pi(Term::sort(Level::Zero), Term::sort(Level::Zero), BinderInfo::Default);
        let partial_val = Term::lam(Term::sort(Level::Zero), Term::var(0), BinderInfo::Default);
        let partial_def = Definition::partial("partial_fn".to_string(), partial_ty.clone(), partial_val);
        env.add_definition(partial_def).unwrap();

        // Verify it's not type-safe
        assert!(!env.is_type_safe("partial_fn"));

        // Now try to create a definition whose TYPE references the partial function
        // This should be rejected
        let bad_type = Term::app(
            Rc::new(Term::Const("partial_fn".to_string(), vec![])),
            Term::sort(Level::Zero)
        );
        let good_val = Term::sort(Level::Zero);

        let bad_def = Definition::total("bad_def".to_string(), bad_type, good_val);
        let result = env.add_definition(bad_def);

        assert!(result.is_err());
        match result {
            Err(TypeError::PartialInType(name)) => {
                assert_eq!(name, "partial_fn");
            }
            other => panic!("Expected PartialInType error, got {:?}", other),
        }
    }

    #[test]
    fn test_wellfounded_definition() {
        use crate::ast::{Definition, Totality, WellFoundedInfo, BinderInfo};

        let ty = Term::pi(Term::sort(Level::Zero), Term::sort(Level::Zero), BinderInfo::Default);
        let val = Term::lam(Term::sort(Level::Zero), Term::var(0), BinderInfo::Default);

        // Create a well-founded definition
        let wf_info = WellFoundedInfo {
            relation: "lt".to_string(),
            decreasing_arg: 0,
        };
        let wf_def = Definition::wellfounded("wf_fn".to_string(), ty, val, wf_info);

        assert_eq!(wf_def.totality, Totality::WellFounded);
        assert!(wf_def.is_type_safe());
        assert!(wf_def.is_total());
        assert_eq!(wf_def.rec_arg, Some(0));
        assert!(wf_def.wf_info.is_some());
    }

    #[test]
    fn test_recursion_with_recursor() {
        use crate::ast::{Definition, Constructor, InductiveDecl, BinderInfo};
        use crate::checker::Env; // checker is now public or we use crate::checker

        // Set up Nat
        let mut env = Env::new();
        let nat_ty = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let nat_ref = Term::ind("Nat".to_string());

        let nat_decl = InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: nat_ty,
            ctors: vec![
                Constructor { name: "zero".to_string(), ty: nat_ref.clone() },
                Constructor { name: "succ".to_string(), ty: Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default) },
            ],
            is_copy: true,
        };
        env.add_inductive(nat_decl).unwrap();

        // Create a recursive function: pred : Nat -> Nat using recursor
        let ty = Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default);
        let body = Term::lam(
            nat_ref.clone(),
            // Use recursor: Nat.rec _ zero (\n. \ih. n) x
            Term::app(
                Term::app(
                    Term::app(
                        Term::app(
                            Term::rec("Nat".to_string()),
                            Term::lam(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default), // motive
                        ),
                        Term::ctor("Nat".to_string(), 0), // zero case
                    ),
                    Term::lam(nat_ref.clone(), Term::lam(nat_ref.clone(), Term::var(1), BinderInfo::Default), BinderInfo::Default), // succ case
                ),
                Term::var(0), // argument
            ),
            BinderInfo::Default
        );

        // Add definition without specifying rec_arg
        let def = Definition::total("pred".to_string(), ty, body);
        assert!(def.rec_arg.is_none()); // Initially not set

        env.add_definition(def).unwrap();

        // After adding, rec_arg should be automatically set to 0 (first arg is Nat)
        let stored_def = env.get_definition("pred").unwrap();
        assert_eq!(stored_def.rec_arg, Some(0), "rec_arg should be automatically set to 0");
    }

    #[test]
    fn test_termination_rejection_non_smaller_arg() {
        use crate::ast::{Definition, Constructor, InductiveDecl, BinderInfo};
        use crate::checker::{check_termination, TypeError, TerminationErrorDetails};

        // Set up Nat
        let mut env = Env::new();
        let nat_ty = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let nat_ref = Term::ind("Nat".to_string());

        let nat_decl = InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: nat_ty,
            ctors: vec![
                Constructor { name: "zero".to_string(), ty: nat_ref.clone() },
                Constructor { name: "succ".to_string(), ty: Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default) },
            ],
            is_copy: true,
        };
        env.add_inductive(nat_decl).unwrap();

        // Create a non-terminating function that calls itself with the SAME argument
        // infinite : Nat -> Nat
        // infinite n = infinite n  (non-terminating!)
        let ty = Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default);
        let body = Term::lam(
            nat_ref.clone(),
            // Direct recursive call: (infinite n) where n is Var(0)
            // Simulated as Const("infinite") applied to Var(0)
            Term::app(
                Rc::new(Term::Const("infinite".to_string(), vec![])),
                Term::var(0),
            ),
            BinderInfo::Default
        );

        // Termination check should fail because recursive call uses same argument
        let result = check_termination(&env, "infinite", &ty, &body);
        assert!(result.is_err(), "Non-terminating function should be rejected");

        if let Err(TypeError::TerminationError { def_name, details }) = result {
            assert_eq!(def_name, "infinite");
            // Verify we get detailed error info
            match details {
                TerminationErrorDetails::NonSmallerArgument { arg_position, .. } => {
                    assert_eq!(arg_position, 0, "Error should indicate argument position 0");
                }
                _ => panic!("Expected NonSmallerArgument error, got {:?}", details),
            }
        } else {
            panic!("Expected TerminationError, got {:?}", result);
        }
    }

    #[test]
    fn test_termination_rejection_no_decreasing_arg() {
        use crate::checker::{check_termination, TypeError, TerminationErrorDetails};
        use crate::ast::BinderInfo;

        let env = Env::new();

        // A function with no inductive arguments that tries to recurse
        // f : Type -> Type
        // f A = f A  (recursive but no inductive argument to decrease on)
        let sort0 = Term::sort(Level::Zero);
        let ty = Term::pi(sort0.clone(), sort0.clone(), BinderInfo::Default);
        let body = Term::lam(
            sort0.clone(),
            Term::app(
                Rc::new(Term::Const("f".to_string(), vec![])),
                Term::var(0),
            ),
            BinderInfo::Default
        );

        let result = check_termination(&env, "f", &ty, &body);
        assert!(result.is_err(), "Recursive function with no inductive arg should be rejected");

        if let Err(TypeError::TerminationError { def_name, details }) = result {
            assert_eq!(def_name, "f");
            match details {
                TerminationErrorDetails::NoDecreasingArgument => {
                    // Expected
                }
                _ => panic!("Expected NoDecreasingArgument error, got {:?}", details),
            }
        } else {
            panic!("Expected TerminationError, got {:?}", result);
        }
    }

    #[test]
    fn test_mutual_recursion_valid() {
        use crate::ast::{Constructor, InductiveDecl};
        use crate::checker::check_mutual_termination;

        // Set up Nat
        let mut env = Env::new();
        let nat_ty = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let nat_ref = Term::ind("Nat".to_string());

        let nat_decl = InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: nat_ty,
            ctors: vec![
                Constructor { name: "zero".to_string(), ty: nat_ref.clone() },
                Constructor { name: "succ".to_string(), ty: Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default) },
            ],
            is_copy: true,
        };
        env.add_inductive(nat_decl).unwrap();

        // Set up Bool
        let bool_ty = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let bool_ref = Term::ind("Bool".to_string());

        let bool_decl = InductiveDecl {
            name: "Bool".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: bool_ty,
            ctors: vec![
                Constructor { name: "true".to_string(), ty: bool_ref.clone() },
                Constructor { name: "false".to_string(), ty: bool_ref.clone() },
            ],
            is_copy: true,
        };
        env.add_inductive(bool_decl).unwrap();

        // Define mutually recursive even/odd functions
        // even : Nat -> Bool
        // odd : Nat -> Bool
        // even 0 = true
        // even (succ n) = odd n
        // odd 0 = false
        // odd (succ n) = even n

        let even_ty = Term::pi(nat_ref.clone(), bool_ref.clone(), BinderInfo::Default);
        let odd_ty = Term::pi(nat_ref.clone(), bool_ref.clone(), BinderInfo::Default);

        // even n = match n { zero => true, succ m => odd m }
        // Using recursor: Nat.rec (fun _ => Bool) true (fun m _ => odd m) n
        let even_body = Term::lam(
            nat_ref.clone(),
            Term::app(
                Term::app(
                    Term::app(
                        Term::app(
                            Term::rec("Nat".to_string()),
                            Term::lam(nat_ref.clone(), bool_ref.clone(), BinderInfo::Default), // motive
                        ),
                        Term::ctor("Bool".to_string(), 0), // true for zero case
                    ),
                    // succ case: \m. \ih. odd m
                    Term::lam(nat_ref.clone(), Term::lam(bool_ref.clone(),
                        Term::app(
                            Rc::new(Term::Const("odd".to_string(), vec![])),
                            Term::var(1), // m (smaller!)
                        ),
                        BinderInfo::Default
                    ), BinderInfo::Default),
                ),
                Term::var(0), // n
            ),
            BinderInfo::Default
        );

        // odd n = match n { zero => false, succ m => even m }
        let odd_body = Term::lam(
            nat_ref.clone(),
            Term::app(
                Term::app(
                    Term::app(
                        Term::app(
                            Term::rec("Nat".to_string()),
                            Term::lam(nat_ref.clone(), bool_ref.clone(), BinderInfo::Default), // motive
                        ),
                        Term::ctor("Bool".to_string(), 1), // false for zero case
                    ),
                    // succ case: \m. \ih. even m
                    Term::lam(nat_ref.clone(), Term::lam(bool_ref.clone(),
                        Term::app(
                            Rc::new(Term::Const("even".to_string(), vec![])),
                            Term::var(1), // m (smaller!)
                        ),
                        BinderInfo::Default
                    ), BinderInfo::Default),
                ),
                Term::var(0), // n
            ),
            BinderInfo::Default
        );

        let defs = vec![
            ("even".to_string(), even_ty, even_body),
            ("odd".to_string(), odd_ty, odd_body),
        ];

        // Should pass - both functions decrease on the same argument position
        let result = check_mutual_termination(&env, &defs);
        assert!(result.is_ok(), "Valid mutual recursion should pass: {:?}", result);

        let results = result.unwrap();
        assert_eq!(results.len(), 2);
        // Both should have rec_arg = Some(0)
        assert_eq!(results[0].1, Some(0), "even should have rec_arg 0");
        assert_eq!(results[1].1, Some(0), "odd should have rec_arg 0");
    }

    #[test]
    fn test_mutual_recursion_incompatible_args() {
        use crate::ast::{Constructor, InductiveDecl};
        use crate::checker::{check_mutual_termination, TypeError, TerminationErrorDetails};

        // Set up Nat and Bool
        let mut env = Env::new();
        let nat_ty = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let nat_ref = Term::ind("Nat".to_string());
        let bool_ty = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let bool_ref = Term::ind("Bool".to_string());

        env.add_inductive(InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: nat_ty,
            ctors: vec![
                Constructor { name: "zero".to_string(), ty: nat_ref.clone() },
                Constructor { name: "succ".to_string(), ty: Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default) },
            ],
            is_copy: true,
        }).unwrap();

        env.add_inductive(InductiveDecl {
            name: "Bool".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: bool_ty,
            ctors: vec![
                Constructor { name: "true".to_string(), ty: bool_ref.clone() },
                Constructor { name: "false".to_string(), ty: bool_ref.clone() },
            ],
            is_copy: true,
        }).unwrap();

        // Define functions with incompatible decreasing arguments
        // f : Nat -> Bool -> Nat  (decreases on arg 0)
        // g : Bool -> Nat -> Nat  (decreases on arg 0, but different type!)

        let f_ty = Term::pi(nat_ref.clone(), Term::pi(bool_ref.clone(), nat_ref.clone(), BinderInfo::Default), BinderInfo::Default);
        let g_ty = Term::pi(bool_ref.clone(), Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default), BinderInfo::Default);

        // f n b = g b n (calls g with different argument order)
        let f_body = Term::lam(
            nat_ref.clone(),
            Term::lam(
                bool_ref.clone(),
                Term::app(
                    Term::app(
                        Rc::new(Term::Const("g".to_string(), vec![])),
                        Term::var(0), // b
                    ),
                    Term::var(1), // n
                ),
                BinderInfo::Default
            ),
            BinderInfo::Default
        );

        // g b n = f n b
        let g_body = Term::lam(
            bool_ref.clone(),
            Term::lam(
                nat_ref.clone(),
                Term::app(
                    Term::app(
                        Rc::new(Term::Const("f".to_string(), vec![])),
                        Term::var(0), // n
                    ),
                    Term::var(1), // b
                ),
                BinderInfo::Default
            ),
            BinderInfo::Default
        );

        let defs = vec![
            ("f".to_string(), f_ty, f_body),
            ("g".to_string(), g_ty, g_body),
        ];

        // Should fail - incompatible decreasing arguments (Nat vs Bool at position 0)
        let result = check_mutual_termination(&env, &defs);
        assert!(result.is_err(), "Incompatible mutual recursion should fail");

        if let Err(TypeError::TerminationError { details, .. }) = result {
            match details {
                TerminationErrorDetails::MutualRecursionError { functions } => {
                    assert!(functions.contains(&"f".to_string()));
                    assert!(functions.contains(&"g".to_string()));
                }
                _ => panic!("Expected MutualRecursionError, got {:?}", details),
            }
        } else {
            panic!("Expected TerminationError, got {:?}", result);
        }
    }

    #[test]
    fn test_wellfounded_recursion_with_acc() {
        use crate::ast::{Constructor, InductiveDecl};
        use crate::checker::{WellFoundedSpec, check_wellfounded_termination};

        // Set up Nat
        let mut env = Env::new();
        let nat_ty = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let nat_ref = Term::ind("Nat".to_string());

        env.add_inductive(InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: nat_ty.clone(),
            ctors: vec![
                Constructor { name: "zero".to_string(), ty: nat_ref.clone() },
                Constructor { name: "succ".to_string(), ty: Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default) },
            ],
            is_copy: true,
        }).unwrap();

        // Set up Acc inductive type
        // Acc : (A : Type) -> (R : A -> A -> Prop) -> A -> Prop
        // ctor intro : forall x, (forall y, R y x -> Acc R y) -> Acc R x
        let prop = Term::sort(Level::Zero);
        let type1 = Term::sort(Level::Succ(Box::new(Level::Zero)));

        // Simplified Acc for testing - just the type structure
        // In reality, Acc is parameterized by type and relation
        // For this test, we create a specialized Acc for Nat with lt relation
        let acc_nat_ty = Term::pi(nat_ref.clone(), prop.clone(), BinderInfo::Default);

        env.add_inductive(InductiveDecl {
            name: "Acc".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: acc_nat_ty.clone(),
            ctors: vec![
                // intro : forall n, (forall m, lt m n -> Acc m) -> Acc n
                Constructor {
                    name: "intro".to_string(),
                    ty: Term::pi(
                        nat_ref.clone(),
                        Term::pi(
                            Term::pi(nat_ref.clone(), Term::pi(prop.clone(), Term::app(
                                Term::ind("Acc".to_string()),
                                Term::var(1),
                            ), BinderInfo::Default), BinderInfo::Default),
                            Term::app(Term::ind("Acc".to_string()), Term::var(1)),
                            BinderInfo::Default
                        ),
                        BinderInfo::Default
                    ),
                },
            ],
            is_copy: false, // Acc is a proof type, not Copy
        }).unwrap();

        // Define a well-founded recursive function
        // div : Nat -> Nat -> Nat (division by repeated subtraction)
        // This uses well-founded recursion on lt
        let div_ty = Term::pi(nat_ref.clone(), Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default), BinderInfo::Default);
        let div_body = Term::lam(
            nat_ref.clone(),
            Term::lam(
                nat_ref.clone(),
                // Simplified body - in practice would use Acc.rec
                Term::var(1),
                BinderInfo::Default
            ),
            BinderInfo::Default
        );

        let spec = WellFoundedSpec {
            relation: "lt".to_string(),
            value_type: nat_ref.clone(),
            wf_proof: None, // Trust annotation for this test
            decreasing_arg: 0,
        };

        // Should pass with Acc type present (trusts annotation)
        let result = check_wellfounded_termination(&env, "div", &div_ty, &div_body, &spec);
        assert!(result.is_ok(), "Well-founded recursion should pass with Acc: {:?}", result);
    }


    #[test]
    fn test_impredicative_prop() {
        use crate::ast::BinderInfo;

        let env = Env::new();
        let ctx = Context::new();

        let prop   = Term::sort(Level::Zero);
        let type0  = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let type1  = Term::sort(Level::Succ(Box::new(Level::Succ(Box::new(Level::Zero)))));

        // Test 1: (A : Type 0) -> Prop is NOT Prop, it is Type 1.
        // Domain Type 0 (u=2). Codomain Prop (v=1). max(2, 1) = 2.
        let pi_type0_prop = Term::pi(type0.clone(), prop.clone(), BinderInfo::Default);
        let inferred1 = infer(&env, &ctx, pi_type0_prop).expect("infer failed");
        assert!(checker::is_def_eq(&env, inferred1, type1.clone(), crate::Transparency::All), "Expected `(Type 0 -> Prop) : Type 1`");

        // Test 1b: Real impredicativity
        // (A : Type 0) -> ((p : Prop) -> p)
        // The body `(p : Prop) -> p` is a proposition (inhabits Prop).
        // Domain Type 0 (u=2). Codomain Prop (v=0). imax(2, 0) = 0.
        let prop_imp = Term::pi(prop.clone(), Term::var(0), BinderInfo::Default); // (p:Prop)->p
        let pi_type0_imp = Term::pi(type0.clone(), prop_imp, BinderInfo::Default);
        let inferred1b = infer(&env, &ctx, pi_type0_imp).expect("infer failed");
        assert!(checker::is_def_eq(&env, inferred1b, prop.clone(), crate::Transparency::All), "Expected `(Type 0 -> ((p:Prop)->p)) : Prop`");

        // Test 2: (p : Prop) → p is Prop
        // Domain Prop (u=1). Codomain p (v=0). imax(1, 0) = 0.
        let pi_prop_var = Term::pi(prop.clone(), Term::var(0), BinderInfo::Default);
        let inferred2 = infer(&env, &ctx, pi_prop_var).expect("infer failed");
        assert!(checker::is_def_eq(&env, inferred2, prop.clone(), crate::Transparency::All), "Expected `(Prop -> p) : Prop`");

        // Test 3: (A : Type 0) → A is Type 1 (predicative)
        // Domain Type 0 (u=2). Codomain A (v=1). max(2, 1) = 2.
        let pi_type0_var = Term::pi(type0.clone(), Term::var(0), BinderInfo::Default);
        let inferred3 = infer(&env, &ctx, pi_type0_var).expect("infer failed");
        assert!(checker::is_def_eq(&env, inferred3, type1.clone(), crate::Transparency::All), "Expected `(Type 0 -> A) : Type 1`");

        // Test 4: Mixed universe `Prop -> Type 0` is `Type 1`
        // Domain Prop (u=1). Codomain Type 0 (v=2). max(1, 2) = 2.
        let pi_prop_type0 = Term::pi(prop.clone(), type0.clone(), BinderInfo::Default);
        let inferred4 = infer(&env, &ctx, pi_prop_type0).expect("infer failed");
        assert!(checker::is_def_eq(&env, inferred4, type1.clone(), crate::Transparency::All), "Expected `(Prop -> Type 0) : Type 1`");
    }

    #[test]
    fn test_wellfounded_context() {
        use crate::checker::WellFoundedCtx;

        let nat_ref = Term::ind("Nat".to_string());
        let ctx = WellFoundedCtx::new("lt".to_string(), nat_ref, 2, 1);

        // Initial context should have the arg as accessible
        assert!(ctx.is_accessible(2));
        assert!(!ctx.is_accessible(0));

        // After shift, indices increase
        let shifted = ctx.shift();
        assert!(shifted.is_accessible(3)); // was 2
        assert!(!ctx.is_accessible(0));

        // Can add more accessible variables
        let extended = shifted.add_accessible(0, 5);
        assert!(extended.is_accessible(0));
        assert!(extended.is_accessible(3));
    }

}
