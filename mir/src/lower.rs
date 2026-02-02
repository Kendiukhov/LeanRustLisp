use crate::*;
use crate::types::{MirType, Region, AdtId};
use kernel::ast::{Term, Level};
use kernel::checker::{Env, Context, infer, whnf, extract_level};
use kernel::Transparency;
use std::rc::Rc;
use std::cell::RefCell;
use std::fmt;

#[derive(Debug, Clone)]
pub struct LoweringError {
    message: String,
}

impl LoweringError {
    fn new(message: impl Into<String>) -> Self {
        Self { message: message.into() }
    }
}

impl fmt::Display for LoweringError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for LoweringError {}

type LoweringResult<T> = Result<T, LoweringError>;

pub struct LoweringContext<'a> {
    pub body: Body,
    pub current_block: BasicBlock,
    pub debruijn_map: Vec<Local>,
    pub kernel_env: &'a Env,
    pub checker_ctx: Context, // For type inference
    pub derived_bodies: Rc<RefCell<Vec<Body>>>, // Store lowered lambda bodies
    next_region: usize,
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
        
        let mut ctx = LoweringContext {
            body,
            current_block: BasicBlock(entry_idx as u32),
            debruijn_map: Vec::new(),
            kernel_env,
            checker_ctx: Context::new(), // Init empty
            derived_bodies: Rc::new(RefCell::new(Vec::new())),
            next_region: 1,
        };

        // Push Return Place _0 with correct type
        ctx.push_local(ret_ty, Some("_0".to_string()));

        for (name, ty) in args {
            let local = ctx.push_local(ty, Some(name));
            ctx.debruijn_map.push(local);
        }

        ctx
    }

    pub fn lower_type(&mut self, term: &Rc<Term>) -> MirType {
        match &**term {
             Term::Sort(_) => MirType::Unit, // Types are erased
             Term::Ind(name, _) => {
                 if name == "Nat" { MirType::Nat }
                 else if name == "Bool" { MirType::Bool }
                 else { MirType::Adt(AdtId(name.clone()), vec![]) }
             },
             Term::App(f, a) => {
                 if let Some((kind, inner)) = self.parse_ref_type(term) {
                      let inner_ty = self.lower_type(&inner);
                      MirType::Ref(self.fresh_region(), Box::new(inner_ty), kind.into())
                 } else if let Term::Ind(name, _) = &**f {
                     if name == "List" {
                          // Special case for List T
                          let arg_ty = self.lower_type(a);
                          MirType::Adt(AdtId("List".to_string()), vec![arg_ty])
                     } else {
                         MirType::Adt(AdtId(name.clone()), vec![])
                     }
                 } else {
                     // Generic application or dependent type -> Unit/Erased
                     MirType::Unit
                 }
             },
             Term::Pi(dom, cod, _) => {
                 let arg = self.lower_type(dom);
                 let ret = self.lower_type(cod);
                 MirType::Fn(vec![arg], Box::new(ret))
             },
             _ => MirType::Unit,
        }
    }

    fn fresh_region(&mut self) -> Region {
        let region = Region(self.next_region);
        self.next_region += 1;
        region
    }

    fn parse_ref_type(&self, ty: &Rc<Term>) -> Option<(BorrowKind, Rc<Term>)> {
        // pattern: (App (App (Const "Ref") (Const "Mut"/"Shared")) T)
        if let Term::App(f1, inner_ty) = &**ty {
             if let Term::App(ref_const, kind_node) = &**f1 {
                 if let Term::Const(name, _) = &**ref_const {
                     if name == "Ref" {
                         if let Term::Const(k, _) = &**kind_node {
                             if k == "Mut" { return Some((BorrowKind::Mut, inner_ty.clone())); }
                             if k == "Shared" { return Some((BorrowKind::Shared, inner_ty.clone())); }
                         }
                     }
                 }
             }
        }
        None
    }

    pub fn push_local(&mut self, ty: Rc<Term>, name: Option<String>) -> Local {
        let idx = self.body.local_decls.len();

        // Determine if type is Prop (for Erasure)
        let sort_ty_res = infer(self.kernel_env, &self.checker_ctx, ty.clone());
        let is_prop = match &sort_ty_res {
            Ok(sort_ty) => {
                match whnf(self.kernel_env, sort_ty.clone(), Transparency::Reducible) {
                    Ok(sort_norm) => matches!(extract_level(&sort_norm), Some(Level::Zero)),
                    Err(_) => false,
                }
            }
            Err(_) => false, // Default to false if inference fails (e.g. for temporaries)
        };
        
        // Determine if type has Copy semantics
        let is_copy = self.is_type_copy(&ty);
        
        // Lower to MIR Type
        let mir_ty = self.lower_type(&ty);

        // Update checker context
        self.checker_ctx = self.checker_ctx.push(ty.clone());

        self.body.local_decls.push(LocalDecl { ty: mir_ty, name, is_prop, is_copy });
        Local(idx as u32)
    }

    fn push_temp_local(&mut self, ty: Rc<Term>, name: Option<String>) -> Local {
        let idx = self.body.local_decls.len();

        // Determine if type is Prop (for Erasure)
        let sort_ty_res = infer(self.kernel_env, &self.checker_ctx, ty.clone());
        let is_prop = match &sort_ty_res {
            Ok(sort_ty) => {
                match whnf(self.kernel_env, sort_ty.clone(), Transparency::Reducible) {
                    Ok(sort_norm) => matches!(extract_level(&sort_norm), Some(Level::Zero)),
                    Err(_) => false,
                }
            }
            Err(_) => false,
        };

        let is_copy = self.is_type_copy(&ty);
        let mir_ty = self.lower_type(&ty);

        self.body.local_decls.push(LocalDecl { ty: mir_ty, name, is_prop, is_copy });
        Local(idx as u32)
    }

    fn push_mir_local(&mut self, ty: MirType, name: Option<String>) -> Local {
        let idx = self.body.local_decls.len();
        let is_copy = ty.is_copy();
        self.body.local_decls.push(LocalDecl { ty, name, is_prop: false, is_copy });
        Local(idx as u32)
    }

    pub fn push_statement(&mut self, stmt: Statement) {
        self.body.basic_blocks[self.current_block.index()].statements.push(stmt);
    }
    
    pub fn terminate(&mut self, terminator: Terminator) {
        self.body.basic_blocks[self.current_block.index()].terminator = Some(terminator);
    }

    fn infer_term_type(&self, term: &Rc<Term>) -> LoweringResult<Rc<Term>> {
        infer(self.kernel_env, &self.checker_ctx, term.clone()).map_err(|e| {
            LoweringError::new(format!("Type inference failed for {:?}: {}", term, e))
        })
    }

    fn lower_term_to_local(&mut self, term: &Rc<Term>) -> LoweringResult<Local> {
        let ty = self.infer_term_type(term)?;
        let temp = self.push_temp_local(ty, None);
        self.push_statement(Statement::StorageLive(temp));
        let next_block = self.new_block();
        self.lower_term(term, Place::from(temp), next_block)?;
        self.set_block(next_block);
        Ok(temp)
    }

    fn eval_term_with_locals(
        &mut self,
        term: &Rc<Term>,
        locals: &[Local],
        local_types: &[Rc<Term>],
    ) -> LoweringResult<Local> {
        let saved_len = self.debruijn_map.len();
        let saved_ctx = self.checker_ctx.clone();
        self.debruijn_map.extend_from_slice(locals);
        for ty in local_types {
            self.checker_ctx = self.checker_ctx.push(ty.clone());
        }
        let temp = self.lower_term_to_local(term)?;
        self.debruijn_map.truncate(saved_len);
        self.checker_ctx = saved_ctx;
        Ok(temp)
    }

    fn local_operand(&self, local: Local) -> Operand {
        if self.body.local_decls[local.index()].is_copy {
            Operand::Copy(Place::from(local))
        } else {
            Operand::Move(Place::from(local))
        }
    }

    fn apply_function_type(&self, func_ty: &MirType) -> LoweringResult<MirType> {
        match func_ty {
            MirType::Fn(args, ret) => {
                if args.is_empty() {
                    Err(LoweringError::new("Function type has no arguments".to_string()))
                } else if args.len() == 1 {
                    Ok((**ret).clone())
                } else {
                    Ok(MirType::Fn(args[1..].to_vec(), ret.clone()))
                }
            }
            _ => Err(LoweringError::new(format!(
                "Expected function type in MIR, got {:?}",
                func_ty
            ))),
        }
    }

    fn call_with_args(
        &mut self,
        func_local: Local,
        args: &[Operand],
        final_place: Option<Place>,
    ) -> LoweringResult<Local> {
        if args.is_empty() {
            return Ok(func_local);
        }

        let mut current_func = func_local;
        let mut current_func_ty = self.body.local_decls[current_func.index()].ty.clone();
        let mut last_local = func_local;

        for (i, arg_op) in args.iter().enumerate() {
            let is_last = i == args.len() - 1;
            let result_ty = self.apply_function_type(&current_func_ty)?;
            let dest_place = if is_last {
                if let Some(place) = final_place.clone() {
                    place
                } else {
                    let t = self.push_mir_local(result_ty.clone(), None);
                    self.push_statement(Statement::StorageLive(t));
                    Place::from(t)
                }
            } else {
                let t = self.push_mir_local(result_ty.clone(), None);
                self.push_statement(Statement::StorageLive(t));
                Place::from(t)
            };

            last_local = dest_place.local;
            let next_block = self.new_block();

            self.terminate(Terminator::Call {
                func: Operand::Move(Place::from(current_func)),
                args: vec![arg_op.clone()],
                destination: dest_place.clone(),
                target: Some(next_block),
            });
            self.set_block(next_block);

            if i > 0 {
                self.push_statement(Statement::StorageDead(current_func));
            }

            if !is_last {
                current_func = dest_place.local;
                current_func_ty = result_ty;
            }
        }

        Ok(last_local)
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
    pub fn lower_term(
        &mut self,
        term: &Rc<Term>,
        destination: Place,
        target: BasicBlock,
    ) -> LoweringResult<()> {
        match &**term {
            Term::Var(idx) => {
                let env_idx = self.debruijn_map.len().checked_sub(1 + *idx).ok_or_else(|| {
                    LoweringError::new(format!(
                        "De Bruijn index out of bounds: {} (context size {})",
                        idx,
                        self.debruijn_map.len()
                    ))
                })?;
                let local = self.debruijn_map[env_idx];
                // Look up type to decide Move vs Copy
                let decl = &self.body.local_decls[local.0 as usize];
                let operand = if decl.is_copy {
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
                 let temp = self.push_temp_local(ty.clone(), None);
                 self.push_statement(Statement::StorageLive(temp));
                 let next_block = self.new_block();
                 self.lower_term(val, Place::from(temp), next_block)?;
                 self.current_block = next_block;
                 let saved_ctx = self.checker_ctx.clone();
                 self.checker_ctx = self.checker_ctx.push(ty.clone());
                 self.debruijn_map.push(temp);
                 let after_body_block = self.new_block();
                 self.lower_term(body, destination.clone(), after_body_block)?;
                 self.debruijn_map.pop();
                 self.checker_ctx = saved_ctx;
                 self.set_block(after_body_block);
                 self.push_statement(Statement::StorageDead(temp));
                 self.terminate(Terminator::Goto { target });
            }
            Term::App(_, _) => {
                let (head, args) = collect_app_spine(term);
                
                if let Term::Rec(ind_name, levels) = &*head {
                    self.lower_rec(ind_name, levels, &args, destination, target)?;
                    return Ok(());
                }

                let mut current_func = self.lower_term_to_local(&head)?;
                let mut current_func_ty = self.body.local_decls[current_func.index()].ty.clone();

                for (i, arg) in args.iter().enumerate() {
                    let is_last = i == args.len() - 1;
                    let temp_arg = self.lower_term_to_local(arg)?;
                    let result_ty = self.apply_function_type(&current_func_ty)?;
                    let call_dest = if is_last {
                        destination.clone()
                    } else {
                        let t = self.push_mir_local(result_ty.clone(), None);
                        self.push_statement(Statement::StorageLive(t));
                        Place::from(t)
                    };
                    
                    let next_block = self.new_block();
                    
                    self.terminate(Terminator::Call {
                        func: Operand::Move(Place::from(current_func)),
                        args: vec![self.local_operand(temp_arg)],
                        destination: call_dest.clone(),
                        target: Some(next_block),
                    });
                    
                    self.set_block(next_block);
                    self.push_statement(Statement::StorageDead(temp_arg));
                    
                    if !is_last {
                         self.push_statement(Statement::StorageDead(current_func));
                         current_func = call_dest.local;
                         current_func_ty = result_ty;
                    } else {
                         self.push_statement(Statement::StorageDead(current_func));
                    }
                }
                
                self.terminate(Terminator::Goto { target });
            }

            Term::Sort(_) | Term::Const(_, _) => {
                let constant = self.make_constant(term.clone());
                 self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant))) 
                ));
                 self.terminate(Terminator::Goto { target });
            }
            Term::Lam(ty, body, _info) => {
                let arg_ty = ty.clone(); 
                
                let mut captures = Vec::new();
                let mut capture_term_types = Vec::new();
                
                for (pos, local) in self.debruijn_map.iter().enumerate() {
                    captures.push(Operand::Copy(Place::from(*local)));
                    let idx = self.debruijn_map.len().saturating_sub(1 + pos);
                    if let Some(ty) = self.checker_ctx.get(idx) {
                        capture_term_types.push(ty);
                    } else {
                        return Err(LoweringError::new("Capture type lookup failed".to_string()));
                    }
                }

                let mut mir_body = Body::new(2);
                mir_body.basic_blocks.push(BasicBlockData { statements: vec![], terminator: None });
                
                let mut sub_ctx = LoweringContext {
                    body: mir_body,
                    current_block: BasicBlock(0),
                    debruijn_map: Vec::new(),
                    kernel_env: self.kernel_env,
                    checker_ctx: Context::new(),
                    derived_bodies: self.derived_bodies.clone(),
                    next_region: 1,
                };
                
                let ret_ty_term = self.infer_term_type(term)?;
                let ret_ty = match &*ret_ty_term {
                    Term::Pi(_, cod, _) => cod.clone(),
                    other => {
                        return Err(LoweringError::new(format!(
                            "Expected lambda type to be Pi, got {:?}",
                            other
                        )));
                    }
                };
                sub_ctx.push_temp_local(ret_ty, Some("_0".to_string()));

                let env_local = sub_ctx.push_temp_local(Rc::new(Term::Sort(kernel::ast::Level::Zero)), Some("env".to_string()));
                let arg_local = sub_ctx.push_temp_local(arg_ty.clone(), Some("arg0".to_string()));

                for (i, ty) in capture_term_types.into_iter().enumerate() {
                    let mir_ty = sub_ctx.lower_type(&ty);
                    let cap_local_idx = sub_ctx.body.local_decls.len();
                    sub_ctx.body.local_decls.push(LocalDecl {
                        ty: mir_ty.clone(),
                        name: None,
                        is_prop: false,
                        is_copy: mir_ty.is_copy(),
                    });
                    let cap_local = Local(cap_local_idx as u32);
                    
                    sub_ctx.push_statement(Statement::Assign(
                        Place::from(cap_local),
                        Rvalue::Use(Operand::Copy(Place {
                            local: env_local,
                            projection: vec![PlaceElem::Field(i)],
                        }))
                    ));
                    sub_ctx.debruijn_map.push(cap_local);
                    sub_ctx.checker_ctx = sub_ctx.checker_ctx.push(ty);
                }
                
                sub_ctx.debruijn_map.push(arg_local);
                sub_ctx.checker_ctx = sub_ctx.checker_ctx.push(arg_ty);
                
                let return_block = sub_ctx.new_block();
                sub_ctx.body.basic_blocks[return_block.index()].terminator = Some(Terminator::Return);
                sub_ctx.lower_term(body, Place::from(Local(0)), return_block)?;
                
                let body_obj = sub_ctx.body;
                let index = self.derived_bodies.borrow().len();
                self.derived_bodies.borrow_mut().push(body_obj);
                
                let constant = Constant {
                    literal: Literal::Closure(index, captures),
                    ty: MirType::Unit // Closures erased to Unit in Constant for now
                };
                
                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant)))
                ));
                self.terminate(Terminator::Goto { target });
            }
            Term::Ctor(name, idx, _) => {
                let arity = self.get_ctor_arity(name, *idx).unwrap_or(0);
                let constant = Constant {
                    literal: Literal::InductiveCtor(name.clone(), *idx, arity),
                    ty: MirType::Unit
                };
                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant))) 
                ));
                self.terminate(Terminator::Goto { target });
            }
            Term::Pi(_, _, _) | Term::Ind(_, _) | Term::Rec(_, _) => {
                let constant = self.make_constant(term.clone());
                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant))) 
                ));
                self.terminate(Terminator::Goto { target });
            }
            Term::Meta(id) => {
                return Err(LoweringError::new(format!(
                    "Unresolved metavariable ?{} in lowering",
                    id
                )));
            }
            Term::Fix(ty, body) => {
                let arg_ty = match &**ty {
                    Term::Pi(dom, _, _) => dom.clone(),
                    _ => {
                        return Err(LoweringError::new(format!(
                            "Expected Pi type for fix, got {:?}",
                            ty
                        )));
                    }
                };

                let mut captures = Vec::new();
                let mut capture_term_types = Vec::new();

                for (pos, local) in self.debruijn_map.iter().enumerate() {
                    captures.push(Operand::Copy(Place::from(*local)));
                    let idx = self.debruijn_map.len().saturating_sub(1 + pos);
                    if let Some(ty) = self.checker_ctx.get(idx) {
                        capture_term_types.push(ty);
                    } else {
                        return Err(LoweringError::new("Capture type lookup failed".to_string()));
                    }
                }

                let mut mir_body = Body::new(2);
                mir_body.basic_blocks.push(BasicBlockData { statements: vec![], terminator: None });

                let mut sub_ctx = LoweringContext {
                    body: mir_body,
                    current_block: BasicBlock(0),
                    debruijn_map: Vec::new(),
                    kernel_env: self.kernel_env,
                    checker_ctx: Context::new(),
                    derived_bodies: self.derived_bodies.clone(),
                    next_region: 1,
                };

                let ret_ty = match &**ty {
                    Term::Pi(_, cod, _) => cod.clone(),
                    _ => {
                        return Err(LoweringError::new(format!(
                            "Expected Pi return type for fix, got {:?}",
                            ty
                        )));
                    }
                };
                sub_ctx.push_temp_local(ret_ty, Some("_0".to_string()));

                let env_local = sub_ctx.push_temp_local(Rc::new(Term::Sort(kernel::ast::Level::Zero)), Some("env".to_string()));
                let arg_local = sub_ctx.push_temp_local(arg_ty.clone(), Some("arg0".to_string()));

                // Unpack captures from env fields starting at 1 (env[0] is self)
                for (i, ty) in capture_term_types.into_iter().enumerate() {
                    let mir_ty = sub_ctx.lower_type(&ty);
                    let cap_local_idx = sub_ctx.body.local_decls.len();
                    sub_ctx.body.local_decls.push(LocalDecl {
                        ty: mir_ty.clone(),
                        name: None,
                        is_prop: false,
                        is_copy: mir_ty.is_copy(),
                    });
                    let cap_local = Local(cap_local_idx as u32);

                    sub_ctx.push_statement(Statement::Assign(
                        Place::from(cap_local),
                        Rvalue::Use(Operand::Copy(Place {
                            local: env_local,
                            projection: vec![PlaceElem::Field(i + 1)],
                        }))
                    ));
                    sub_ctx.debruijn_map.push(cap_local);
                    sub_ctx.checker_ctx = sub_ctx.checker_ctx.push(ty);
                }

                // Bind self from env[0]
                let self_local = sub_ctx.push_temp_local(ty.clone(), Some("self".to_string()));
                sub_ctx.push_statement(Statement::Assign(
                    Place::from(self_local),
                    Rvalue::Use(Operand::Copy(Place {
                        local: env_local,
                        projection: vec![PlaceElem::Field(0)],
                    }))
                ));
                sub_ctx.debruijn_map.push(self_local);
                sub_ctx.checker_ctx = sub_ctx.checker_ctx.push(ty.clone());

                // Argument is last
                sub_ctx.debruijn_map.push(arg_local);
                sub_ctx.checker_ctx = sub_ctx.checker_ctx.push(arg_ty);

                let return_block = sub_ctx.new_block();
                sub_ctx.body.basic_blocks[return_block.index()].terminator = Some(Terminator::Return);

                let shifted_body = body.shift(0, 1);
                let body_app = Rc::new(Term::App(shifted_body, Rc::new(Term::Var(0))));
                sub_ctx.lower_term(&body_app, Place::from(Local(0)), return_block)?;

                let body_obj = sub_ctx.body;
                let index = self.derived_bodies.borrow().len();
                self.derived_bodies.borrow_mut().push(body_obj);

                let constant = Constant {
                    literal: Literal::Fix(index, captures),
                    ty: MirType::Unit,
                };

                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant)))
                ));
                self.terminate(Terminator::Goto { target });
            }
        }

        Ok(())
    }

    fn make_constant(&mut self, term: Rc<Term>) -> Constant {
        Constant {
            literal: Literal::Term(term.clone()),
            ty: MirType::Unit
        }
    }

    fn lower_rec(
        &mut self,
        ind_name: &str,
        levels: &[Level],
        args: &[Rc<Term>],
        destination: Place,
        target: BasicBlock,
    ) -> LoweringResult<()> {
        let decl = self.kernel_env.inductives.get(ind_name).expect("Unknown inductive in Rec");
        let n_params = decl.num_params;
        let n_motives = 1;
        let n_minors = decl.ctors.len();
        let n_indices = count_indices(&decl.ty, n_params);
        let expected_args = n_params + n_motives + n_minors + n_indices + 1;
        
        if args.len() < expected_args {
            let mut partial_term: Rc<Term> = Rc::new(Term::Rec(ind_name.to_string(), levels.to_vec()));
            for arg in args.iter() {
                partial_term = Rc::new(Term::App(partial_term, arg.clone()));
            }
            let constant = self.make_constant(partial_term);
            self.push_statement(Statement::Assign(
                destination,
                Rvalue::Use(Operand::Constant(Box::new(constant)))
            ));
            self.terminate(Terminator::Goto { target });
            return Ok(());
        }

        let major_premise = &args[args.len() - 1];

        let params = &args[..n_params];
        let motive_term = &args[n_params];
        let minors_start = n_params + n_motives;
        let minor_terms = &args[minors_start .. minors_start + n_minors];
        let indices_start = minors_start + n_minors;
        let index_terms = &args[indices_start .. indices_start + n_indices];

        let mut param_locals = Vec::new();
        for param in params {
            param_locals.push(self.lower_term_to_local(param)?);
        }
        let motive_local = self.lower_term_to_local(motive_term)?;
        let mut minor_locals = Vec::new();
        for minor in minor_terms {
            minor_locals.push(self.lower_term_to_local(minor)?);
        }
        let mut index_locals = Vec::new();
        for idx in index_terms {
            index_locals.push(self.lower_term_to_local(idx)?);
        }

        let major_ty = self.infer_term_type(major_premise)?;
        let temp_major = self.push_temp_local(major_ty, None);
        self.push_statement(Statement::StorageLive(temp_major));
        let major_block = self.new_block();
        self.lower_term(major_premise, Place::from(temp_major), major_block)?;
        self.set_block(major_block);
        
        let discr_temp = self.push_mir_local(MirType::Nat, None); 
        self.push_statement(Statement::StorageLive(discr_temp));
        self.push_statement(Statement::Assign(
            Place::from(discr_temp),
            Rvalue::Discriminant(Place::from(temp_major))
        ));
        
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
        
        let base_ctx = self.checker_ctx.clone();

        for (i, arm_block) in target_blocks.iter().enumerate() {
            self.set_block(*arm_block);
            let ctor = &decl.ctors[i];
            
            let mut args_for_minor = Vec::new();
            self.checker_ctx = base_ctx.clone();

            let minor_local = minor_locals[i];
            let ctor_inst = instantiate_params(ctor.ty.clone(), params);
            let field_types = peel_pi_binders(&ctor_inst).0;
            let mut field_locals = Vec::new();

            for (field_pos, field_ty) in field_types.iter().enumerate() {
                let field_place = Place {
                    local: temp_major,
                    projection: vec![PlaceElem::Downcast(i), PlaceElem::Field(n_params + field_pos)],
                };
                let field_local = self.push_temp_local(field_ty.clone(), None);
                self.push_statement(Statement::StorageLive(field_local));
                self.push_statement(Statement::Assign(
                    Place::from(field_local),
                    Rvalue::Use(Operand::Copy(field_place)),
                ));

                let prev_len = field_locals.len();
                field_locals.push(field_local);

                args_for_minor.push(Operand::Copy(Place::from(field_local)));

                if is_recursive_head(field_ty, ind_name) {
                    let rec_index_terms = extract_inductive_indices(field_ty, ind_name, n_params);
                    let mut rec_index_locals = Vec::new();
                    if let Some(terms) = rec_index_terms {
                        if terms.len() == n_indices {
                            let prev_locals = &field_locals[..prev_len];
                            let prev_types = &field_types[..prev_len];
                            for term in terms {
                                let idx_local = self.eval_term_with_locals(&term, prev_locals, prev_types)?;
                                rec_index_locals.push(idx_local);
                            }
                        }
                    }

                    if rec_index_locals.len() != n_indices {
                        rec_index_locals = index_locals.clone();
                    }

                    let rec_term = Rc::new(Term::Rec(ind_name.to_string(), levels.to_vec()));
                    let rec_local = self.lower_term_to_local(&rec_term)?;
                    let mut ih_args = Vec::new();
                    for &p in &param_locals {
                        ih_args.push(Operand::Copy(Place::from(p)));
                    }
                    ih_args.push(Operand::Copy(Place::from(motive_local)));
                    for &m in &minor_locals {
                        ih_args.push(Operand::Copy(Place::from(m)));
                    }
                    for &idx_local in &rec_index_locals {
                        ih_args.push(Operand::Copy(Place::from(idx_local)));
                    }
                    ih_args.push(Operand::Copy(Place::from(field_local)));

                    let ih_local = self.call_with_args(rec_local, &ih_args, None)?;
                    args_for_minor.push(Operand::Copy(Place::from(ih_local)));
                }
            }

            if args_for_minor.is_empty() {
                self.push_statement(Statement::Assign(
                    destination.clone(),
                    Rvalue::Use(self.local_operand(minor_local)),
                ));
                self.terminate(Terminator::Goto { target });
            } else {
                self.call_with_args(minor_local, &args_for_minor, Some(destination.clone()))?;
                self.terminate(Terminator::Goto { target });
            }
        }
        
        self.push_statement(Statement::StorageDead(discr_temp));
        self.push_statement(Statement::StorageDead(temp_major));

        Ok(())
    }
    
    fn get_ctor_arity(&self, ind_name: &str, ctor_idx: usize) -> Option<usize> {
        let decl = self.kernel_env.inductives.get(ind_name)?;
        if ctor_idx >= decl.ctors.len() { return None; }
        
        let ctor = &decl.ctors[ctor_idx];
        let mut ty = &ctor.ty;
        let mut pi_count = 0;
        while let Term::Pi(_, body, _) = &**ty {
            pi_count += 1;
            ty = body;
        }
        
        Some(pi_count)
    }

    fn is_type_copy(&self, ty: &Rc<Term>) -> bool {
        match &**ty {
            Term::Sort(_) => true,
            Term::Pi(_, _, _) => true,
            Term::Ind(name, _) => {
                self.kernel_env.inductives
                    .get(name)
                    .map(|decl| decl.is_copy)
                    .unwrap_or(false)
            },
            _ => false
        }
    }
}

fn collect_app_spine(term: &Rc<Term>) -> (Rc<Term>, Vec<Rc<Term>>) {
    let mut args = Vec::new();
    let mut current = term.clone();
    
    loop {
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

fn instantiate_params(mut ty: Rc<Term>, params: &[Rc<Term>]) -> Rc<Term> {
    for param in params {
        if let Term::Pi(_, body, _) = &*ty {
            ty = body.subst(0, param);
        } else {
            break;
        }
    }
    ty
}

fn peel_pi_binders(ty: &Rc<Term>) -> (Vec<Rc<Term>>, Rc<Term>) {
    let mut binders = Vec::new();
    let mut current = ty.clone();
    loop {
        match &*current {
            Term::Pi(dom, body, _) => {
                binders.push(dom.clone());
                current = body.clone();
            }
            _ => break,
        }
    }
    (binders, current)
}

fn extract_inductive_args(term: &Rc<Term>, ind_name: &str) -> Option<Vec<Rc<Term>>> {
    fn go(t: &Rc<Term>, acc: &mut Vec<Rc<Term>>) -> Option<String> {
        match &**t {
            Term::App(f, a) => {
                acc.push(a.clone());
                go(f, acc)
            }
            Term::Ind(name, _) => Some(name.clone()),
            _ => None,
        }
    }

    let mut rev_args = Vec::new();
    let head = go(term, &mut rev_args)?;
    if head != ind_name {
        return None;
    }
    rev_args.reverse();
    Some(rev_args)
}

fn extract_inductive_indices(term: &Rc<Term>, ind_name: &str, num_params: usize) -> Option<Vec<Rc<Term>>> {
    let args = extract_inductive_args(term, ind_name)?;
    if args.len() < num_params {
        return None;
    }
    Some(args[num_params..].to_vec())
}

fn is_recursive_head(t: &Rc<Term>, name: &str) -> bool {
    match &**t {
        Term::Ind(n, _) => n == name,
        Term::App(f, _) => is_recursive_head(f, name),
        Term::Pi(_, _, _) => false,
        _ => false,
    }
}

fn count_indices(ty: &Rc<Term>, num_params: usize) -> usize {
    let mut current = ty;
    let mut count = 0;
    while let Term::Pi(_, body, _) = &**current {
        count += 1;
        current = body;
    }
    if count >= num_params {
        count - num_params
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kernel::ast::BinderInfo;
    use kernel::checker::Env; 

    #[test]
    fn test_lower_app() {
        let arg_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let f = Rc::new(Term::Lam(arg_ty.clone(), Rc::new(Term::Var(0)), BinderInfo::Default));
        let a = Rc::new(Term::Sort(Level::Zero));
        let term = Rc::new(Term::App(f, a));

        let env = Env::new(); 
        let ret_ty = Rc::new(Term::Sort(Level::Zero)); 
        let mut ctx = LoweringContext::new(vec![], ret_ty, &env);
        let dest = Place::from(Local(0));
        let target = ctx.new_block();

        ctx.lower_term(&term, dest, target).unwrap();

        let body = ctx.finish();

        println!("{:?}", body);
        assert!(body.basic_blocks.len() > 1);
    }
}
