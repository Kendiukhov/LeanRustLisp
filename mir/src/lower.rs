use crate::*;
use kernel::ast::{Term, Level};
use kernel::checker::{Env, Context, infer};
use std::rc::Rc;

use std::cell::RefCell;

pub struct LoweringContext<'a> {
    pub body: Body,
    pub current_block: BasicBlock,
    pub debruijn_map: Vec<Local>,
    pub kernel_env: &'a Env,
    pub checker_ctx: Context, // For type inference
    pub derived_bodies: Rc<RefCell<Vec<Body>>>, // Store lowered lambda bodies
}

impl<'a> LoweringContext<'a> {
    pub fn new(args: Vec<(String, Rc<Term>)>, ret_ty: Rc<Term>, kernel_env: &'a kernel::checker::Env) -> Self {
        let mut body = Body::new(args.len());
        // Create entry block
        let entry_idx = body.basic_blocks.len();
        body.basic_blocks.push(BasicBlockData {
            statements: Vec::new(),
            terminator: None,
        });
        
        // Register arguments as locals
        let mut ctx = LoweringContext {
            body,
            current_block: BasicBlock(entry_idx as u32),
            debruijn_map: Vec::new(),
            kernel_env,
            checker_ctx: Context::new(), // Init empty
            derived_bodies: Rc::new(RefCell::new(Vec::new())),
        };

        // Push Return Place _0 with correct type
        ctx.push_local(ret_ty, Some("_0".to_string()));

        for (name, ty) in args {
            let local = ctx.push_local(ty, Some(name));
            ctx.debruijn_map.push(local);
        }

        ctx
    }

    pub fn push_local(&mut self, ty: Rc<Term>, name: Option<String>) -> Local {
        let idx = self.body.local_decls.len();

        // Determine if type is Prop (for Erasure)
        let sort_ty_res = infer(self.kernel_env, &self.checker_ctx, ty.clone());
        let is_prop = match &sort_ty_res {
            Ok(sort_ty) => matches!(**sort_ty, Term::Sort(Level::Zero)),
            Err(_) => false, // Default to false if inference fails (e.g. for temporaries)
        };
        
        // Determine if type has Copy semantics
        let is_copy = self.is_type_copy(&ty);

        // Update checker context
        self.checker_ctx = self.checker_ctx.push(ty.clone());

        self.body.local_decls.push(LocalDecl { ty, name, is_prop, is_copy });
        Local(idx as u32)
    }

    pub fn push_statement(&mut self, stmt: Statement) {
        self.body.basic_blocks[self.current_block.index()].statements.push(stmt);
    }
    
    pub fn terminate(&mut self, terminator: Terminator) {
        self.body.basic_blocks[self.current_block.index()].terminator = Some(terminator);
    }
    
    pub fn new_block(&mut self) -> BasicBlock {
        let idx = self.body.basic_blocks.len();
        self.body.basic_blocks.push(BasicBlockData {
            statements: Vec::new(),
            terminator: None,
        });
        BasicBlock(idx as u32)
    }
    
    pub fn set_block(&mut self, block: BasicBlock) {
        self.current_block = block;
    }

    pub fn finish(self) -> Body {
        self.body
    }
    
    // Core lowering logic
    pub fn lower_term(&mut self, term: &Rc<Term>, destination: Place, target: BasicBlock) {
        match &**term {
            Term::Var(idx) => {
                let env_idx = self.debruijn_map.len().checked_sub(1 + *idx).expect("De Bruijn index out of bounds in lowering");
                let local = self.debruijn_map[env_idx];
                // Look up type to decide Move vs Copy
                let decl = &self.body.local_decls[local.0 as usize];
                let is_copy = self.is_type_copy(&decl.ty);
                let operand = if is_copy {
                    Operand::Copy(Place::from(local))
                } else {
                    Operand::Move(Place::from(local))
                };
                
                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(operand) 
                ));
                self.terminate(Terminator::Goto { target });
            }
            Term::LetE(ty, val, body) => {
                 // 1. Create temp for val
                 // LetE doesn't have a name in kernel AST anymore
                 let temp = self.push_local(ty.clone(), None);
                 
                 // 2. StorageLive
                 self.push_statement(Statement::StorageLive(temp));
                 
                 // 3. Lower val into temp
                 // We need a block for after val is computed.
                 let next_block = self.new_block();
                 self.lower_term(val, Place::from(temp), next_block);
                 
                 // 4. Set current block to next_block (where val is ready)
                 self.current_block = next_block;
                 
                 // 5. Push temp to env (shadowing)
                 self.debruijn_map.push(temp);
                 
                 // 6. Lower body into destination
                 // We need a block for after body.
                 let after_body_block = self.new_block();
                 self.lower_term(body, destination.clone(), after_body_block);
                 
                 // 7. Pop env
                 self.debruijn_map.pop();
                 
                 // 8. StorageDead (in the block after body)
                 self.set_block(after_body_block);
                 self.push_statement(Statement::StorageDead(temp));
                 self.terminate(Terminator::Goto { target });
            }
            Term::App(_, _) => {
                let (head, args) = collect_app_spine(term);
                
                if let Term::Rec(ind_name, _) = &*head {
                    self.lower_rec(ind_name, &args, destination, target);
                    return;
                }
            
                // Standard App evaluation (strict left-to-right, unary currying)
                // Evaluate head
                let mut current_func = self.push_local(Rc::new(Term::Sort(kernel::ast::Level::Zero)), None);
                self.push_statement(Statement::StorageLive(current_func));
                
                let func_block = self.new_block();
                self.lower_term(&head, Place::from(current_func), func_block);
                self.set_block(func_block);
                
                // Apply arguments sequentially
                for (i, arg) in args.iter().enumerate() {
                    let is_last = i == args.len() - 1;
                    
                    // Lower Argument
                    let temp_arg = self.push_local(Rc::new(Term::Sort(kernel::ast::Level::Zero)), None);
                    self.push_statement(Statement::StorageLive(temp_arg));
                    let arg_block = self.new_block();
                    self.lower_term(arg, Place::from(temp_arg), arg_block);
                    self.set_block(arg_block);
                    
                    // Destination for this call
                    let call_dest = if is_last {
                        destination.clone()
                    } else {
                        // Intermediate result (closure)
                        let t = self.push_local(Rc::new(Term::Sort(kernel::ast::Level::Zero)), None);
                        self.push_statement(Statement::StorageLive(t));
                        Place::from(t)
                    };
                    
                    let next_block = self.new_block();
                    
                    self.terminate(Terminator::Call {
                        func: Operand::Move(Place::from(current_func)),
                        args: vec![Operand::Move(Place::from(temp_arg))], // Unary Call
                        destination: call_dest.clone(),
                        target: Some(next_block),
                    });
                    
                    self.set_block(next_block);
                    self.push_statement(Statement::StorageDead(temp_arg));
                    
                    // If not last, current_func consumes intermediate result.
                    // Previous func is dead (Moved).
                    // We don't explicit StorageDead prev func if it was temp? Move handles it? 
                    // No, local storage slot needs dead.
                    // But we reused current_func variable for the *next* iteration?
                    // No, `current_func` is a local index. We need to update it.
                    
                    if !is_last {
                         // The new function is the result of the call
                         // Clean up old func slot?
                         // storage_dead(current_func)? 
                         // Yes, if we are done with it.
                         // But we want to reuse the slot mechanism?
                         // Easier to just drop old and use new local.
                         self.push_statement(Statement::StorageDead(current_func));
                         current_func = call_dest.local; // call_dest is Place, extract local
                    } else {
                         self.push_statement(Statement::StorageDead(current_func));
                    }
                }
                
                self.terminate(Terminator::Goto { target });
            }

            Term::Sort(_) | Term::Const(_, _) => {
                // Assign constant
                let constant = self.make_constant(term.clone());
                 self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant))) 
                ));
                 self.terminate(Terminator::Goto { target });
            }
            Term::Lam(ty, body, _info) => {
                // Lambda Lowering with Closure Conversion:
                let arg_ty = ty.clone(); 
                
                // 1. Prepare captures (for the Literal)
                let mut captures = Vec::new();
                // Capture types order matches captures order
                let mut capture_types = Vec::new();
                
                for local in &self.debruijn_map {
                    captures.push(Operand::Copy(Place::from(*local)));
                     capture_types.push(self.body.local_decls[local.index()].ty.clone());
                }

                // 2. Create sub_ctx with strict 2 arguments (Env + Arg)
                // Arg1: Environment (Tuple of captures)
                // Arg2: Explicit Argument
                let mut mir_body = Body::new(2);
                mir_body.basic_blocks.push(BasicBlockData { statements: vec![], terminator: None }); // Entry
                
                let mut sub_ctx = LoweringContext {
                    body: mir_body,
                    current_block: BasicBlock(0),
                    debruijn_map: Vec::new(),
                    kernel_env: self.kernel_env,
                    checker_ctx: Context::new(), // Reset checker context for new body?
                    // Note: checker_ctx should ideally imply types of captures? 
                    // But lowering is handling scoping manually.
                    derived_bodies: self.derived_bodies.clone(),
                };
                
                // 3. Infer Return Type for _0
                let ret_ty = match infer(self.kernel_env, &self.checker_ctx, term.clone()) {
                     Ok(t) => {
                         if let Term::Pi(_, cod, _) = &*t {
                             cod.clone()
                         } else {
                             Rc::new(Term::Sort(kernel::ast::Level::Zero))
                         }
                     }
                     Err(_) => Rc::new(Term::Sort(kernel::ast::Level::Zero))
                };
                sub_ctx.push_local(ret_ty, Some("_0".to_string()));

                // 4. Register Arguments
                // _1: Environment
                // Type is ostensibly a Tuple of capture types. For now Sort(0) placeholder.
                let env_local = sub_ctx.push_local(Rc::new(Term::Sort(kernel::ast::Level::Zero)), Some("env".to_string()));
                // _2: Explicit Argument
                let arg_local = sub_ctx.push_local(arg_ty, Some("arg0".to_string()));

                // 5. Unpack Environment into Locals
                // These locals correspond to the captures.
                for (i, ty) in capture_types.into_iter().enumerate() {
                    let cap_local = sub_ctx.push_local(ty, None);
                    
                    // Assign cap_local = env.i
                    sub_ctx.push_statement(Statement::Assign(
                        Place::from(cap_local),
                        Rvalue::Use(Operand::Copy(Place {
                            local: env_local,
                            projection: vec![PlaceElem::Field(i)],
                        }))
                    ));
                    
                    // Add to DeBruijn map (order matches outer)
                    sub_ctx.debruijn_map.push(cap_local);
                }
                
                // 6. Push Explicit Argument to Map (last)
                sub_ctx.debruijn_map.push(arg_local);
                
                // 7. Lower body
                let return_block = sub_ctx.new_block();
                sub_ctx.body.basic_blocks[return_block.index()].terminator = Some(Terminator::Return);
                sub_ctx.lower_term(body, Place::from(Local(0)), return_block);
                
                // 8. Save derived body
                let body_obj = sub_ctx.body;
                let index = self.derived_bodies.borrow().len();
                self.derived_bodies.borrow_mut().push(body_obj);
                
                // 9. Create closure literal with captures
                let constant = Constant {
                    literal: Literal::Closure(index, captures),
                    ty: Rc::new(Term::Sort(kernel::ast::Level::Zero)) 
                };
                
                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant)))
                ));
                self.terminate(Terminator::Goto { target });
            }
            Term::Pi(_, _, _) | Term::Ind(_, _) | Term::Ctor(_, _, _) | Term::Rec(_, _) => {
                // These are constants/values in code.
                // Pi/Ind = Type values.
                // Ctor/Rec = Function values.
                let constant = self.make_constant(term.clone());
                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant))) 
                ));
                self.terminate(Terminator::Goto { target });
            }
            Term::Meta(id) => {
                // Meta variables should be resolved during elaboration.
                // If they reach MIR lowering, emit erased Unit value as safe fallback.
                // This mirrors the behavior in direct codegen.
                let constant = Constant {
                    literal: Literal::Term(Rc::new(Term::Sort(kernel::ast::Level::Zero))),
                    ty: Rc::new(Term::Sort(kernel::ast::Level::Succ(Box::new(kernel::ast::Level::Zero))))
                };
                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant)))
                ));
                self.terminate(Terminator::Goto { target });
            }
        }
    }



    fn make_constant(&mut self, term: Rc<Term>) -> Constant {
        Constant {
            literal: Literal::Term(term.clone()),
            ty: Rc::new(Term::Sort(kernel::ast::Level::Zero))
        }
    }

    fn lower_rec(&mut self, ind_name: &str, args: &[Rc<Term>], destination: Place, target: BasicBlock) {
        let decl = self.kernel_env.inductives.get(ind_name).expect("Unknown inductive in Rec");
        let n_params = decl.num_params;
        let n_motives = 1;
        let n_minors = decl.ctors.len();
        // Major premise is the last argument.
        // Args layout: params... motive... minors... major
        let expected_args = n_params + n_motives + n_minors + 1;
        
        if args.len() < expected_args {
            // Partial application: Fall back to generating the Rec term as a constant.
            // The runtime codegen will handle it as nested closure applications.
            // Build the partial application term: (App (App (Rec ind) arg0) arg1) ...
            let mut partial_term: Rc<Term> = Rc::new(Term::Rec(ind_name.to_string(), vec![]));
            for arg in args.iter() {
                partial_term = Rc::new(Term::App(partial_term, arg.clone()));
            }
            let constant = self.make_constant(partial_term);
            self.push_statement(Statement::Assign(
                destination,
                Rvalue::Use(Operand::Constant(Box::new(constant)))
            ));
            self.terminate(Terminator::Goto { target });
            return;
        }
        
        // Indices in args slice
        let major_idx = args.len() - 1;
        let major_premise = &args[major_idx];
        
        // Minor premises start after params and motive
        let minors_start = n_params + n_motives;
        let minor_premises = &args[minors_start .. minors_start + n_minors];
        
        // 1. Lower major premise
        let temp_major = self.push_local(decl.ty.clone(), None); 
        self.push_statement(Statement::StorageLive(temp_major));
        let major_block = self.new_block();
        self.lower_term(major_premise, Place::from(temp_major), major_block);
        self.set_block(major_block);
        
        // 2. Discriminant
        let discr_temp = self.push_local(Rc::new(Term::Sort(kernel::ast::Level::Zero)), None); 
        self.push_statement(Statement::StorageLive(discr_temp));
        self.push_statement(Statement::Assign(
            Place::from(discr_temp),
            Rvalue::Discriminant(Place::from(temp_major))
        ));
        
        // 3. Switch targets
        let mut target_blocks = Vec::new();
        let mut values = Vec::new();
        
        for (ctor_idx, _) in decl.ctors.iter().enumerate() {
             let arm_block = self.new_block();
             target_blocks.push(arm_block);
             values.push(ctor_idx as u128);
        }
        
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Move(Place::from(discr_temp)),
            targets: SwitchTargets {
                values,
                targets: target_blocks.clone(),
            }
        });
        
        // 4. Lower arms
        for (i, arm_block) in target_blocks.iter().enumerate() {
            self.set_block(*arm_block);
            let minor_premise = &minor_premises[i];
            let ctor = &decl.ctors[i];
            
            // Generate args for minor premise (fields + IHs)
            let mut args_for_minor = Vec::new();
            
            // Iterate constructor fields
            let mut ctor_ty = ctor.ty.clone();
            let mut field_idx = 0;
            
            // We need to peel Pi types of ctor to find fields
            while let Term::Pi(dom, cod, _) = &*ctor_ty {
                 // Field access
                 let field_place = Place {
                     local: temp_major,
                     projection: vec![PlaceElem::Downcast(i), PlaceElem::Field(field_idx)],
                 };
                 let field_op = Operand::Copy(field_place); 
                 args_for_minor.push(field_op.clone());
                 
                 // Check for recursion (IH)
                 // Simple name check for now
                 if let Term::Ind(n, _) = &**dom {
                     if n == ind_name {
                         // Recursive field!
                         // Hack for now: Pass `field` again as executing "identity" recursion.
                         args_for_minor.push(field_op.clone()); 
                     }
                 }
                 
                 ctor_ty = cod.clone();
                 field_idx += 1;
            }
            
            // Call minor premise
            let temp_minor = self.push_local(Rc::new(Term::Sort(kernel::ast::Level::Zero)), None);
            self.push_statement(Statement::StorageLive(temp_minor));
            let minor_eval_block = self.new_block();
            self.lower_term(minor_premise, Place::from(temp_minor), minor_eval_block);
            self.set_block(minor_eval_block);
            
            if args_for_minor.is_empty() {
                 // No arguments: Assign directly (e.g. Bool case)
                 self.push_statement(Statement::Assign(
                     destination.clone(),
                     Rvalue::Use(Operand::Move(Place::from(temp_minor)))
                 ));
                 self.push_statement(Statement::StorageDead(temp_minor));
                 self.terminate(Terminator::Goto { target });
            } else {
                 // Apply arguments sequentially
                 let mut current_func = temp_minor;
                 
                 for (j, arg_op) in args_for_minor.iter().enumerate() {
                     let is_last = j == args_for_minor.len() - 1;
                     let call_dest = if is_last {
                         destination.clone()
                     } else {
                         let t = self.push_local(Rc::new(Term::Sort(kernel::ast::Level::Zero)), None);
                         self.push_statement(Statement::StorageLive(t));
                         Place::from(t)
                     };
                     
                     let next_blk = self.new_block();
                     
                     self.terminate(Terminator::Call {
                         func: Operand::Move(Place::from(current_func)),
                         args: vec![arg_op.clone()],
                         destination: call_dest.clone(),
                         target: Some(next_blk), // Always jump to next block for cleanup sequence
                     });
                     self.set_block(next_blk);
                     
                     // Helper to kill intermediate closures
                     if j > 0 { 
                         self.push_statement(Statement::StorageDead(current_func));
                     }
                     
                     if !is_last {
                          current_func = call_dest.local;
                     }
                 }
                 
                 // Cleanup temp_minor after chain
                 self.push_statement(Statement::StorageDead(temp_minor));
                 self.terminate(Terminator::Goto { target });
            }
        }
        
        self.push_statement(Statement::StorageDead(discr_temp));
        self.push_statement(Statement::StorageDead(temp_major));
    }
    fn is_type_copy(&self, ty: &Rc<Term>) -> bool {
        match &**ty {
            Term::Sort(_) => true,
            Term::Pi(_, _, _) => true,
            Term::Ind(name, _) => {
                // Look up the inductive in the environment to check is_copy
                self.kernel_env.inductives
                    .get(name)
                    .map(|decl| decl.is_copy)
                    .unwrap_or(false) // Default to not Copy if unknown
            },
            _ => false
        }
    }
}

fn collect_app_spine(term: &Rc<Term>) -> (Rc<Term>, Vec<Rc<Term>>) {
    let mut args = Vec::new();
    let mut current = term.clone();
    
    // Peel apps
    // Loop until not an App
    loop {
        // We need to clone inner to break borrow
        let next = if let Term::App(f, a) = &*current {
            Some((f.clone(), a.clone()))
        } else {
            None
        };
        
        if let Some((f, a)) = next {
            args.push(a);
            current = f;
        } else {
            break;
        }
    }
    args.reverse();
    (current, args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use kernel::ast::*;
    use kernel::checker::Env; // Import Env

    #[test]
    fn test_lower_app() {
        let f = Rc::new(Term::Const("f".to_string(), vec![]));
        let a = Rc::new(Term::Const("a".to_string(), vec![]));
        let term = Rc::new(Term::App(f, a));

        let env = Env::new(); // Create dummy env
        let ret_ty = Rc::new(Term::Sort(Level::Zero)); // Dummy return type
        let mut ctx = LoweringContext::new(vec![], ret_ty, &env);
        let dest = Place::from(Local(0));
        let target = ctx.new_block();

        ctx.lower_term(&term, dest, target);

        let body = ctx.finish();

        println!("{:?}", body);
        assert!(body.basic_blocks.len() > 1);
    }

    #[test]
    fn test_lower_rec() {
        let mut env = Env::new();
        let nat_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let nat_ref = Rc::new(Term::Ind("Nat".to_string(), vec![]));
        
        let decl = InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: nat_ty.clone(),
            ctors: vec![
                Constructor { name: "zero".to_string(), ty: nat_ref.clone() },
                Constructor { name: "succ".to_string(), ty: Rc::new(Term::Pi(nat_ref.clone(), nat_ref.clone(), kernel::ast::BinderInfo::Default)) },
            ],
            is_copy: true, // Nat has Copy semantics
        };
        env.add_inductive(decl).unwrap();
        
        let rec = Rc::new(Term::Rec("Nat".to_string(), vec![]));
        let motive = Rc::new(Term::Const("motive".to_string(), vec![]));
        let zero_case = Rc::new(Term::Const("zero_case".to_string(), vec![]));
        let succ_case = Rc::new(Term::Const("succ_case".to_string(), vec![]));
        let major = Rc::new(Term::Const("major".to_string(), vec![]));
        
        // Build App chain
        let t1 = Rc::new(Term::App(rec, motive));
        let t2 = Rc::new(Term::App(t1, zero_case));
        let t3 = Rc::new(Term::App(t2, succ_case));
        let term = Rc::new(Term::App(t3, major));
        
        let ret_ty = Rc::new(Term::Sort(Level::Zero)); // Dummy return type
        let mut ctx = LoweringContext::new(vec![], ret_ty, &env);
        let dest = Place::from(Local(0));
        let target = ctx.new_block();

        ctx.lower_term(&term, dest, target);

        let body = ctx.finish();
        println!("{:?}", body);

        let has_switch = body.basic_blocks.iter().any(|bb| {
            matches!(bb.terminator, Some(Terminator::SwitchInt { .. }))
        });
        assert!(has_switch, "Body should contain a SwitchInt terminator");
    }

    #[test]
    fn test_lower_lam() {
        // Lower: \x:Type. x
        let ty = Rc::new(Term::Sort(kernel::ast::Level::Zero));
        let body_term = Rc::new(Term::Var(0));
        let lam = Rc::new(Term::Lam(ty.clone(), body_term, kernel::ast::BinderInfo::Default));

        let env = Env::new(); // Dummy env
        let ret_ty = Rc::new(Term::Sort(kernel::ast::Level::Zero)); // Dummy return type
        let mut ctx = LoweringContext::new(vec![], ret_ty, &env);

        let dest = Place::from(Local(0)); // Dummy dest
        let target = BasicBlock(1);
        ctx.body.basic_blocks.push(BasicBlockData { statements: vec![], terminator: Some(Terminator::Return) }); // Target BB

        ctx.lower_term(&lam, dest, target);

        // check derived bodies
        assert_eq!(ctx.derived_bodies.borrow().len(), 1, "Should have 1 derived body for lambda");
        
        // check main body statement
        let entry_block = &ctx.body.basic_blocks[0];
        assert!(!entry_block.statements.is_empty());
        match &entry_block.statements[0] {
            Statement::Assign(_, Rvalue::Use(Operand::Constant(c))) => {
                match &c.literal {
                    crate::Literal::Closure(idx, _) => assert_eq!(*idx, 0),
                    _ => panic!("Expected Closure literal"),
                }
            }
            _ => panic!("Expected Assignment of Constant Closure"),
        }
    }
}
