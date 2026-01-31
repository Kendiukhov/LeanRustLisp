use crate::{Body, Local, BasicBlock, Statement, Terminator, Operand, Rvalue, Place};
use crate::errors::{OwnershipError, MirSpan};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use kernel::ast::Term;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LocalState {
    Uninitialized,
    Initialized,
    Moved,
}

#[derive(Debug, Clone)]
pub struct OwnershipState {
    pub locals: Vec<LocalState>,
}

impl OwnershipState {
    pub fn get(&self, local: Local) -> LocalState {
        self.locals[local.0 as usize]
    }
}

impl OwnershipState {
    pub fn new(num_locals: usize) -> Self {
        OwnershipState {
            locals: vec![LocalState::Uninitialized; num_locals],
        }
    }

    pub fn join(&mut self, other: &OwnershipState) -> bool {
        let mut changed = false;
        for (i, state) in self.locals.iter_mut().enumerate() {
            let other_state = other.locals[i];
            let new_state = match (*state, other_state) {
                (LocalState::Uninitialized, LocalState::Uninitialized) => LocalState::Uninitialized,
                (LocalState::Initialized, LocalState::Initialized) => LocalState::Initialized,
                // If it's Moved in either path, it's potentially Moved (conservative for safety)
                (LocalState::Moved, _) | (_, LocalState::Moved) => LocalState::Moved,
                // If Uninit on one path and Init on other -> Uninit (must be init on all paths)
                (LocalState::Uninitialized, LocalState::Initialized) => LocalState::Uninitialized,
                (LocalState::Initialized, LocalState::Uninitialized) => LocalState::Uninitialized,
            };
            
            if *state != new_state {
                *state = new_state;
                changed = true;
            }
        }
        changed
    }
}

pub struct OwnershipAnalysis<'a> {
    body: &'a Body,
    block_entry_states: HashMap<BasicBlock, OwnershipState>,
}

impl<'a> OwnershipAnalysis<'a> {
    pub fn new(body: &'a Body) -> Self {
        OwnershipAnalysis {
            body,
            block_entry_states: HashMap::new(),
        }
    }

    /// Check if a local's type is linear (not Copy).
    /// Linear types require explicit drop/use and cannot be duplicated.
    fn is_local_linear(&self, local: Local) -> bool {
        let decl = &self.body.local_decls[local.index()];
        // A type is linear if it's NOT Copy
        !decl.is_copy
    }

    /// Backward-compatible helper that checks type directly (for tests)
    fn is_type_linear(&self, ty: &Rc<Term>) -> bool {
        match &**ty {
            Term::Sort(_) => false, // Type values are always Copy
            // For inductives, we'd need the env to look up is_copy
            // Without env access, fall back to conservative check
            Term::Ind(name, _) => {
                // Known Copy types - this is a fallback for tests without proper LocalDecl setup
                name != "Nat" && name != "Bool" && name != "Option" && name != "List"
            },
            _ => true, // Conservatively assume linear
        }
    }

    pub fn analyze(&mut self) {
        // Init entry block with args initialized, locals uninitialized
        let mut entry_state = OwnershipState::new(self.body.local_decls.len());
        // Args (assuming they come first) are initialized?
        // TODO: Map args to locals specifically. 
        // For now, let's assume all locals start Uninitialized except maybe those set by args 
        // if we had that info handy.
        // In LRL lowering, args are locals pushed first.
        // Let's assume args are 0..arg_count (which we can get from body arg count if we stored it, 
        // but currently Body::new takes num_args but doesn't store it explicitly as a field?
        // Actually Body has `arg_count` field from our layout previously? 
        // Let's check Body struct definition if needed.
        // Assuming args are init at entry.
        // Local(0) is Return Place (Uninit)
        // Args start at Local(1)
        for i in 0..self.body.arg_count {
            if i + 1 < entry_state.locals.len() {
                entry_state.locals[i + 1] = LocalState::Initialized;
            }
        }

        self.block_entry_states.insert(BasicBlock(0), entry_state);
        
        let mut worklist: Vec<BasicBlock> = vec![BasicBlock(0)];
        let mut visited = HashSet::new();
        visited.insert(BasicBlock(0));

        while let Some(bb) = worklist.pop() {
            let mut state = self.block_entry_states[&bb].clone();
            
            // Process statements
            if let Some(data) = self.body.basic_blocks.get(bb.0 as usize) {
                for stmt in &data.statements {
                    self.apply_statement(stmt, &mut state);
                }
                
                // Process terminator and specific per-target changes
                if let Some(terminator) = &data.terminator {
                    // We need to apply terminator effect (like moves in args)
                    self.apply_terminator(terminator, &mut state);
                    
                    // Propagate to successors
                    let successors = self.successors(terminator);
                    for target in successors {
                        if !self.block_entry_states.contains_key(&target) {
                             self.block_entry_states.insert(target, state.clone());
                             worklist.push(target);
                        } else {
                             let entry = self.block_entry_states.get_mut(&target).unwrap();
                             if entry.join(&state) {
                                 worklist.push(target);
                             }
                        }
                    }
                }
            }
        }
    }

    /// Check for ownership errors and return structured error types
    pub fn check_structured(&self) -> Vec<OwnershipError> {
        let mut errors = Vec::new();
        let mut bbs: Vec<_> = self.block_entry_states.keys().collect();
        bbs.sort_by_key(|b| b.0);

        for bb in bbs {
            let mut state = self.block_entry_states[bb].clone();
            if let Some(data) = self.body.basic_blocks.get(bb.0 as usize) {
                for (stmt_idx, stmt) in data.statements.iter().enumerate() {
                    let location = Some(MirSpan { block: *bb, statement_index: stmt_idx });
                    self.check_statement_structured(stmt, &mut state, location, &mut errors);
                    self.apply_statement(stmt, &mut state);
                }
                if let Some(term) = &data.terminator {
                    let location = Some(MirSpan { block: *bb, statement_index: data.statements.len() });
                    self.check_terminator_structured(term, &mut state, location, &mut errors);
                    self.apply_terminator(term, &mut state);
                }
            }
        }
        errors
    }

    /// Legacy check method that returns string errors (for backward compatibility)
    pub fn check(&self) -> Vec<String> {
        self.check_structured()
            .into_iter()
            .map(|e| e.to_string())
            .collect()
    }
    
    fn check_statement(&self, stmt: &Statement, state: &mut OwnershipState) -> Result<(), String> {
        match stmt {
            Statement::Assign(place, rvalue) => {
                self.check_rvalue_verifier(rvalue, state)?;

                // Drop Check: Overwriting
                if place.projection.is_empty() {
                    let local_state = state.get(place.local);
                    if local_state == LocalState::Initialized {
                        if self.is_local_linear(place.local) {
                            return Err(format!("Overwriting initialized linear variable {:?} without use/drop", place.local));
                        }
                    }
                }
            }
            Statement::StorageDead(local) => {
                let local_state = state.get(*local);
                if local_state == LocalState::Initialized {
                    if self.is_local_linear(*local) {
                        return Err(format!("Linear variable {:?} dropped without use/drop", local));
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn check_terminator(&self, term: &Terminator, state: &mut OwnershipState) -> Result<(), String> {
        match term {
            Terminator::Call { func, args, .. } => {
                // Verify sequential execution effects (e.g. double moves)
                // Use a temporary state to simulate execution order checking
                let mut temp_state = state.clone();
                
                self.check_operand_verifier(func, &temp_state)?;
                self.check_operand_moves(func, &mut temp_state);
                
                for arg in args {
                    self.check_operand_verifier(arg, &temp_state)?;
                    // Apply move effect to detect subsequent failures
                    self.check_operand_moves(arg, &mut temp_state);
                }
            }
            Terminator::SwitchInt { discr, .. } => {
                self.check_operand_verifier(discr, state)?;
            }
            Terminator::Return => {
                let s = state.get(Local(0));
                if s != LocalState::Initialized {
                    return Err(format!("Return value (Local(0)) uninitialized at return. State: {:?}", s));
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn check_rvalue_verifier(&self, rvalue: &Rvalue, state: &OwnershipState) -> Result<(), String> {
        match rvalue {
            Rvalue::Use(op) => self.check_operand_verifier(op, state),
            _ => Ok(())
        }
    }

    fn check_operand_verifier(&self, operand: &Operand, state: &OwnershipState) -> Result<(), String> {
        match operand {
            Operand::Move(place) => {
                // Must be Initialized
                let s = state.get(place.local);
                if s != LocalState::Initialized {
                    return Err(format!("Use of moved/uninitialized variable {:?} (State: {:?})", place.local, s));
                }
            }
            Operand::Copy(place) => {
                let s = state.get(place.local);
                if s != LocalState::Initialized {
                    return Err(format!("Use of uninitialized variable {:?} (State: {:?})", place.local, s));
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn apply_statement(&self, stmt: &Statement, state: &mut OwnershipState) {
        match stmt {
            Statement::Assign(place, rvalue) => {
                // 1. Consume Rvalue (check for moves)
                self.check_rvalue_moves(rvalue, state);
                // 2. Init Place
                if place.projection.is_empty() {
                    state.locals[place.local.0 as usize] = LocalState::Initialized;
                }
            }
            Statement::StorageLive(local) => {
                state.locals[local.0 as usize] = LocalState::Uninitialized;
            }
            Statement::StorageDead(local) => {
                 state.locals[local.0 as usize] = LocalState::Uninitialized; 
            }
            Statement::Nop => {}
        }
    }

    fn apply_terminator(&self, term: &Terminator, state: &mut OwnershipState) {
        match term {
            Terminator::Return => {},
            Terminator::Goto { .. } => {},
            Terminator::Call { func, args, destination, .. } => {
                self.check_operand_moves(func, state);
                for arg in args {
                    self.check_operand_moves(arg, state);
                }
                if destination.projection.is_empty() {
                    state.locals[destination.local.0 as usize] = LocalState::Initialized;
                }
            },
            Terminator::SwitchInt { discr, .. } => {
                self.check_operand_moves(discr, state);
            },
            Terminator::Unreachable => {},
        }
    }

    
    fn check_rvalue_moves(&self, rvalue: &Rvalue, state: &mut OwnershipState) {
        match rvalue {
            Rvalue::Use(op) => self.check_operand_moves(op, state),
            Rvalue::Ref(_, _) => {}, // Borrows - check validity but don't move
            Rvalue::Discriminant(_) => {}, // Reads discriminant, no move
        }
    }

    fn check_operand_moves(&self, operand: &Operand, state: &mut OwnershipState) {
        match operand {
            Operand::Move(place) => {
                // Mark as Moved.
                // Partial Move conservative handling:
                // Regardless of projection (e.g. p.x), we mark the root local 'p' as Moved.
                // This prevents leaks (forgetting to drop p.y) and double moves.
                state.locals[place.local.0 as usize] = LocalState::Moved;
            }
            Operand::Copy(_place) => {
                // Check if initialized and not moved -> Error if not!
            }
            Operand::Constant(_) => {},
        }
    }

    fn successors(&self, term: &Terminator) -> Vec<BasicBlock> {
        match term {
            Terminator::Goto { target } => vec![*target],
            Terminator::Call { target, .. } => {
                if let Some(t) = target { vec![*t] } else { vec![] }
            },
            Terminator::SwitchInt { targets, .. } => targets.targets.clone(),
            _ => vec![],
        }
    }

    // =========================================================================
    // Structured error checking methods
    // =========================================================================

    fn check_statement_structured(
        &self,
        stmt: &Statement,
        state: &mut OwnershipState,
        location: Option<MirSpan>,
        errors: &mut Vec<OwnershipError>,
    ) {
        match stmt {
            Statement::Assign(place, rvalue) => {
                self.check_rvalue_structured(rvalue, state, location, errors);

                // Drop Check: Overwriting
                if place.projection.is_empty() {
                    let local_state = state.get(place.local);
                    if local_state == LocalState::Initialized {
                        if self.is_local_linear(place.local) {
                            errors.push(OwnershipError::OverwriteWithoutDrop {
                                local: place.local,
                                location,
                            });
                        }
                    }
                }
            }
            Statement::StorageDead(local) => {
                let local_state = state.get(*local);
                if local_state == LocalState::Initialized {
                    if self.is_local_linear(*local) {
                        errors.push(OwnershipError::LinearNotConsumed {
                            local: *local,
                            location,
                        });
                    }
                }
            }
            _ => {}
        }
    }

    fn check_terminator_structured(
        &self,
        term: &Terminator,
        state: &mut OwnershipState,
        location: Option<MirSpan>,
        errors: &mut Vec<OwnershipError>,
    ) {
        match term {
            Terminator::Call { func, args, .. } => {
                let mut temp_state = state.clone();

                self.check_operand_structured(func, &temp_state, location, errors);
                self.check_operand_moves(func, &mut temp_state);

                for arg in args {
                    // Check for double move
                    if let Operand::Move(place) = arg {
                        if temp_state.get(place.local) == LocalState::Moved {
                            errors.push(OwnershipError::DoubleMoveInArgs {
                                local: place.local,
                                location,
                            });
                        }
                    }
                    self.check_operand_structured(arg, &temp_state, location, errors);
                    self.check_operand_moves(arg, &mut temp_state);
                }
            }
            Terminator::SwitchInt { discr, .. } => {
                self.check_operand_structured(discr, state, location, errors);
            }
            Terminator::Return => {
                let s = state.get(Local(0));
                if s != LocalState::Initialized {
                    errors.push(OwnershipError::UninitializedReturn { location });
                }
            }
            _ => {}
        }
    }

    fn check_rvalue_structured(
        &self,
        rvalue: &Rvalue,
        state: &OwnershipState,
        location: Option<MirSpan>,
        errors: &mut Vec<OwnershipError>,
    ) {
        match rvalue {
            Rvalue::Use(op) => self.check_operand_structured(op, state, location, errors),
            _ => {}
        }
    }

    fn check_operand_structured(
        &self,
        operand: &Operand,
        state: &OwnershipState,
        location: Option<MirSpan>,
        errors: &mut Vec<OwnershipError>,
    ) {
        match operand {
            Operand::Move(place) => {
                let s = state.get(place.local);
                if s == LocalState::Moved {
                    errors.push(OwnershipError::UseAfterMove {
                        local: place.local,
                        location,
                    });
                } else if s == LocalState::Uninitialized {
                    errors.push(OwnershipError::UseUninitialized {
                        local: place.local,
                        location,
                    });
                }
            }
            Operand::Copy(place) => {
                let s = state.get(place.local);
                if s != LocalState::Initialized {
                    errors.push(OwnershipError::UseUninitialized {
                        local: place.local,
                        location,
                    });
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    #[test]
    fn test_linear_initialization() {
        let mut body = Body::new(0);
        // _0: Return place
        body.local_decls.push(LocalDecl::new(Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero)), None)); 
        // _1: Var
        body.local_decls.push(LocalDecl::new(Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero)), None));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)), 
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Term(Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero))), 
                        ty: Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero))
                    })))
                )
            ],
            terminator: Some(Terminator::Goto { target: BasicBlock(1) }),
        });
        body.basic_blocks.push(BasicBlockData { statements: vec![], terminator: Some(Terminator::Return) });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        
        let bb1_state = &analysis.block_entry_states[&BasicBlock(1)];
        assert_eq!(bb1_state.locals[1], LocalState::Initialized, "Local _1 should be Initialized after assignment");
    }
    
    #[test]
    fn test_move_semantics() {
        let mut body = Body::new(0);
        // _0
        body.local_decls.push(LocalDecl::new(Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero)), None));
        // _1
        body.local_decls.push(LocalDecl::new(Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero)), None)); 
        // _2
        body.local_decls.push(LocalDecl::new(Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero)), None)); 
        
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                // Init _1
                Statement::Assign(
                    Place::from(Local(1)), 
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Term(Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero))), 
                        ty: Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero))
                    })))
                ),
                // Move _1 to _2
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Use(Operand::Move(Place::from(Local(1))))
                )
            ],
            terminator: Some(Terminator::Goto { target: BasicBlock(1) })
        });
        body.basic_blocks.push(BasicBlockData { statements: vec![], terminator: Some(Terminator::Return) });
        
        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        
        let bb1_state = &analysis.block_entry_states[&BasicBlock(1)];
        assert_eq!(bb1_state.locals[1], LocalState::Moved, "Local _1 should be Moved after move");
        assert_eq!(bb1_state.locals[2], LocalState::Initialized, "Local _2 should be Initialized after assignment");
    }

    #[test]
    fn test_branching_join() {
        // BB0:
        //   branch -> BB1, BB2
        // BB1:
        //   _1 = Init
        //   goto BB3
        // BB2:
        //   _1 = Uninit (or stays uninit)
        //   goto BB3
        // BB3:
        //   Join: _1 should be Uninitialized (because only init on one path)
        
        let mut body = Body::new(0);
        // _0
        body.local_decls.push(LocalDecl::new(Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero)), None));
        // _1
        body.local_decls.push(LocalDecl::new(Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero)), None)); 
        
        // BB0: Entry
        body.basic_blocks.push(BasicBlockData {
             statements: vec![],
             terminator: Some(Terminator::SwitchInt { 
                 discr: Operand::Constant(Box::new(Constant { 
                     literal: Literal::Term(Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero))), 
                     ty: Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero)) 
                 })),
                 targets: SwitchTargets {
                     values: vec![0],
                     targets: vec![BasicBlock(1), BasicBlock(2)]
                 }
             })
        });
        
        // BB1: Init _1
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)), 
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Term(Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero))), 
                        ty: Rc::new(kernel::ast::Term::Sort(kernel::ast::Level::Zero))
                    })))
                )
            ],
            terminator: Some(Terminator::Goto { target: BasicBlock(3) })
        });
        
        // BB2: Do nothing (stays Uninit)
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Goto { target: BasicBlock(3) })
        });
        
        // BB3: Join
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return)
        });
        
        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        
        let bb3_state = &analysis.block_entry_states[&BasicBlock(3)];
        assert_eq!(bb3_state.locals[1], LocalState::Uninitialized, "Local _1 should be Uninitialized at join if distinct paths differ");
    }

    #[test]
    fn test_linear_drop_error() {
        // _1: Linear Type (Token)
        // BB0:
        //   _1 = Init
        //   StorageDead(_1) -> Error
        let mut body = Body::new(0);
        // _0
        body.local_decls.push(LocalDecl::new(Rc::new(Term::Sort(kernel::ast::Level::Zero)), None));
        // _1 : Token (Linear)
        body.local_decls.push(LocalDecl::new(Rc::new(Term::Ind("Token".to_string(), vec![])), Some("token".to_string())));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0), // Dummy value
                        ty: Rc::new(Term::Ind("Token".to_string(), vec![]))
                    })))
                ),
                Statement::StorageDead(Local(1))
            ],
             terminator: Some(Terminator::Return)
        });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check();
        
        assert!(!errors.is_empty(), "Should detect linear drop error");
        // We match substring because format might vary - check for either old or new format
        assert!(errors[0].contains("not consumed") || errors[0].contains("without use"),
            "Error message should mention linear value not consumed: {}", errors[0]);
    }

    #[test]
    fn test_uninitialized_return() {
        let mut body = Body::new(0);
        // _0: Return place
        body.local_decls.push(LocalDecl::new(Rc::new(Term::Sort(kernel::ast::Level::Zero)), None));
        
        // BB0: Return immediately (without assigning _0)
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return)
        });
        
        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check();
        
        assert!(!errors.is_empty(), "Should detect uninitialized return");
        assert!(errors[0].contains("return value") || errors[0].contains("Return value"),
            "Error should mention return value: {}", errors[0]);
    }

    #[test]
    fn test_double_move_in_args() {
        // call(_1, _1) where _1 is moved.
        // Should error on 2nd arg.
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(Rc::new(Term::Sort(kernel::ast::Level::Zero)), None)); // _0
        body.local_decls.push(LocalDecl::new(Rc::new(Term::Sort(kernel::ast::Level::Zero)), None)); // _1
        
        body.basic_blocks.push(BasicBlockData {
             statements: vec![
                 Statement::Assign(Place::from(Local(1)), Rvalue::Use(Operand::Constant(Box::new(Constant{literal: Literal::Nat(0), ty: Rc::new(Term::Sort(kernel::ast::Level::Zero))}))))
             ],
             terminator: Some(Terminator::Call {
                 func: Operand::Constant(Box::new(Constant{literal: Literal::Nat(0), ty: Rc::new(Term::Sort(kernel::ast::Level::Zero))})),
                 args: vec![Operand::Move(Place::from(Local(1))), Operand::Move(Place::from(Local(1)))],
                 destination: Place::from(Local(0)),
                 target: None
             })
        });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check();
        
        assert!(!errors.is_empty(), "Should detect double move in arguments");
    }

    #[test]
    fn test_partial_move_safety() {
        // _1: Pair(Linear, Linear)
        // move _1.0
        // use _1 (or move _1.0 again) -> Error
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(Rc::new(Term::Sort(kernel::ast::Level::Zero)), None)); // _0
        body.local_decls.push(LocalDecl::new(Rc::new(Term::Sort(kernel::ast::Level::Zero)), None)); // _1
        
        let p_field = Place { local: Local(1), projection: vec![PlaceElem::Field(0)] };
        
        body.basic_blocks.push(BasicBlockData {
             statements: vec![
                 Statement::Assign(Place::from(Local(1)), Rvalue::Use(Operand::Constant(Box::new(Constant{literal: Literal::Nat(0), ty: Rc::new(Term::Sort(kernel::ast::Level::Zero))}))))
             ],
             terminator: Some(Terminator::Call {
                 func: Operand::Constant(Box::new(Constant{literal: Literal::Nat(0), ty: Rc::new(Term::Sort(kernel::ast::Level::Zero))})),
                 args: vec![Operand::Move(p_field.clone()), Operand::Move(p_field)],
                 destination: Place::from(Local(0)),
                 target: None
             })
        });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check();
        
        assert!(!errors.is_empty(), "Should detect double move via partial moves");
    }
}
