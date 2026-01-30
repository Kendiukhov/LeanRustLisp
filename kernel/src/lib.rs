pub mod ast;
pub mod parser;
pub mod checker;
pub mod ownership;

pub use ast::*;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{InductiveDecl, Constructor, Term, Level};
    use crate::parser::Parser;
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
        // Register Nat: Type 0
        // Nat.zero : Nat
        // Nat.succ : Nat -> Nat
        let mut env = Env::new();
        
        let nat_ty = Term::sort(Level::Succ(Box::new(Level::Zero))); // Type 0
        let nat_ref = Term::ind("Nat".to_string());
        
        let nat_decl = InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            ty: nat_ty.clone(),
            ctors: vec![
                Constructor {
                    name: "zero".to_string(),
                    ty: nat_ref.clone(), // zero : Nat
                },
                Constructor {
                    name: "succ".to_string(),
                    ty: Term::pi(nat_ref.clone(), nat_ref.clone()), // succ : Nat -> Nat
                },
            ],
        };
        
        env.add_inductive(nat_decl);
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
        assert!(matches!(&*succ_ty, Term::Pi(_, _)));
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
        
        // Set up Nat inductive
        let mut env = Env::new();
        let nat_ty = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let nat_ref = Term::ind("Nat".to_string());
        
        let nat_decl = InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            ty: nat_ty.clone(),
            ctors: vec![
                Constructor {
                    name: "zero".to_string(),
                    ty: nat_ref.clone(),
                },
                Constructor {
                    name: "succ".to_string(),
                    ty: Term::pi(nat_ref.clone(), nat_ref.clone()),
                },
            ],
        };
        
        env.add_inductive(nat_decl.clone());
        let ctx = Context::new();
        
        // Check that (rec Nat) has a Pi type (motive → ... → result)
        let rec_nat = Term::rec("Nat".to_string());
        let rec_ty = infer(&env, &ctx, rec_nat).expect("Failed to infer recursor type");
        println!("Nat.rec type: {:?}", rec_ty);
        
        // The computed type should be a Pi
        assert!(matches!(&*rec_ty, Term::Pi(_, _)));
        
        // Also test compute_recursor_type directly
        let computed = compute_recursor_type(&nat_decl);
        println!("Computed type: {:?}", computed);
        assert!(matches!(&*computed, Term::Pi(_, _)));
    }

    #[test]
    fn test_iota_reduction() {
        use crate::checker::whnf;
        
        // Set up Nat inductive with zero and succ
        let mut env = Env::new();
        let nat_ty = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let nat_ref = Term::ind("Nat".to_string());
        
        let nat_decl = InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            ty: nat_ty.clone(),
            ctors: vec![
                Constructor {
                    name: "zero".to_string(),
                    ty: nat_ref.clone(),
                },
                Constructor {
                    name: "succ".to_string(),
                    ty: Term::pi(nat_ref.clone(), nat_ref.clone()),
                },
            ],
        };
        
        env.add_inductive(nat_decl);
        
        // Build: Nat.rec motive base step zero
        // Where: motive = λ_. Nat, base = zero, step = λn. λih. succ ih
        let rec = Term::rec("Nat".to_string());
        let motive = Term::lam(nat_ref.clone(), nat_ref.clone()); // λ_. Nat (constant motive)
        let base = Term::ctor("Nat".to_string(), 0); // zero
        let step = Term::lam(
            nat_ref.clone(),
            Term::lam(nat_ref.clone(), Term::app(Term::ctor("Nat".to_string(), 1), Term::var(0)))
        ); // λn. λih. succ ih
        let major = Term::ctor("Nat".to_string(), 0); // zero
        
        // Apply: rec motive base step zero
        let app1 = Term::app(rec, motive);
        let app2 = Term::app(app1, base.clone());
        let app3 = Term::app(app2, step);
        let app4 = Term::app(app3, major);
        
        // After iota reduction, should reduce to base (zero)
        let result = whnf(&env, app4);
        println!("Iota reduction result: {:?}", result);
        
        // Result should be zero (ctor Nat 0)
        assert!(matches!(&*result, Term::Ctor(name, 0, _) if name == "Nat"));
    }

    #[test]
    fn test_universe_levels() {
        use crate::checker::{level_imax, level_max, reduce_level};
        
        let env = Env::new();
        let ctx = Context::new();
        
        // Test 1: Prop → Prop has type Type 0 
        // (Pi Prop Prop) : Type 0 (since imax(1, 1) = 1)
        // Note: Prop itself is Type 0. Prop -> Prop is the type of functions mapping props to props.
        let prop_to_prop = Term::pi(
            Term::sort(Level::Zero),
            Term::sort(Level::Zero),
        );
        let ty = infer(&env, &ctx, prop_to_prop).expect("Failed to infer Prop → Prop");
        println!("Prop → Prop : {:?}", ty);
        assert!(matches!(&*ty, Term::Sort(Level::Succ(_)))); // Type 0

        // Test 1b: Impredicativity check
        // (p : Prop) -> p has type Prop
        // u1 = level(Prop) = 1
        // u2 = level(p) = 0
        // imax(1, 0) = 0
        let impredicative = Term::pi(
            Term::sort(Level::Zero), // domain: Prop
            Term::var(0),            // codomain: p
        );
        let ty_impred = infer(&env, &ctx, impredicative).expect("Failed to infer (p:Prop) -> p");
        println!("(p:Prop) -> p : {:?}", ty_impred);
        assert!(matches!(&*ty_impred, Term::Sort(Level::Zero))); // Prop
        
        // Test 2: Type 0 → A should have type Type 0
        // (Pi (Type 0) (Type 0)) : Type 1 (since imax(1, 1) = 1, and Type 1 : Type 2)
        let type0 = Level::Succ(Box::new(Level::Zero));
        let type0_to_type0 = Term::pi(
            Term::sort(type0.clone()),
            Term::sort(type0.clone()),
        );
        let ty2 = infer(&env, &ctx, type0_to_type0).expect("Failed to infer Type 0 → Type 0");
        println!("Type 0 → Type 0 : {:?}", ty2);
        // Should be Sort(Type 0) = Sort(Succ(Zero))
        assert!(matches!(&*ty2, Term::Sort(Level::Succ(_))));
        
        // Test 3: Prop → Type 0 has type Type 0 (since imax(0, 1) = 1)
        let prop_to_type0 = Term::pi(
            Term::sort(Level::Zero),
            Term::sort(Level::Succ(Box::new(Level::Zero))),
        );
        let ty3 = infer(&env, &ctx, prop_to_type0).expect("Failed to infer Prop → Type 0");
        println!("Prop → Type 0 : {:?}", ty3);
        assert!(matches!(&*ty3, Term::Sort(Level::Succ(_))));
        
        // Test universe helper functions
        assert_eq!(reduce_level(level_imax(Level::Zero, Level::Zero)), Level::Zero);
        assert!(matches!(
            reduce_level(level_max(Level::Zero, Level::Succ(Box::new(Level::Zero)))),
            Level::Succ(_)
        ));
    }
}
