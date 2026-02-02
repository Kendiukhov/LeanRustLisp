use crate::{Body, Local, BasicBlock, Statement, Terminator, Operand, Rvalue, RuntimeCheckKind, Place};
use crate::errors::{OwnershipError, MirSpan};
use std::collections::{HashMap, HashSet};

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
                (LocalState::Moved, _) | (_, LocalState::Moved) => LocalState::Moved,
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

    fn is_local_linear(&self, local: Local) -> bool {
        let decl = &self.body.local_decls[local.index()];
        !decl.is_copy
    }

    pub fn analyze(&mut self) {
        let mut entry_state = OwnershipState::new(self.body.local_decls.len());
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
            
            if let Some(data) = self.body.basic_blocks.get(bb.0 as usize) {
                for stmt in &data.statements {
                    self.apply_statement(stmt, &mut state);
                }
                
                if let Some(terminator) = &data.terminator {
                    self.apply_terminator(terminator, &mut state);
                    
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

    pub fn check(&self) -> Vec<String> {
        self.check_structured()
            .into_iter()
            .map(|e| e.to_string())
            .collect()
    }
    
    fn apply_statement(&self, stmt: &Statement, state: &mut OwnershipState) {
        match stmt {
            Statement::Assign(place, rvalue) => {
                self.check_rvalue_moves(rvalue, state);
                if place.projection.is_empty() {
                    state.locals[place.local.0 as usize] = LocalState::Initialized;
                }
            }
            Statement::RuntimeCheck(_) => {}
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
            Rvalue::Ref(_, _) => {}, 
            Rvalue::Discriminant(_) => {}, 
        }
    }

    fn check_operand_moves(&self, operand: &Operand, state: &mut OwnershipState) {
        match operand {
            Operand::Move(place) => {
                state.locals[place.local.0 as usize] = LocalState::Moved;
            }
            Operand::Copy(_place) => {},
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
            Statement::RuntimeCheck(check) => {
                self.check_runtime_check(check, state, location, errors);
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

    fn check_runtime_check(
        &self,
        check: &RuntimeCheckKind,
        state: &OwnershipState,
        location: Option<MirSpan>,
        errors: &mut Vec<OwnershipError>,
    ) {
        match check {
            RuntimeCheckKind::RefCellBorrow { local } | RuntimeCheckKind::MutexLock { local } => {
                let operand = Operand::Copy(Place::from(*local));
                self.check_operand_structured(&operand, state, location, errors);
            }
            RuntimeCheckKind::BoundsCheck { local, index } => {
                let operand = Operand::Copy(Place::from(*local));
                self.check_operand_structured(&operand, state, location, errors);
                let index_operand = Operand::Copy(Place::from(*index));
                self.check_operand_structured(&index_operand, state, location, errors);
            }
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
    use crate::types::*;

    #[test]
    fn test_linear_initialization() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None)); 
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)), 
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Unit, 
                        ty: MirType::Unit
                    })))
                )
            ],
            terminator: Some(Terminator::Goto { target: BasicBlock(1) }),
        });
        body.basic_blocks.push(BasicBlockData { statements: vec![], terminator: Some(Terminator::Return) });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        
        let bb1_state = &analysis.block_entry_states[&BasicBlock(1)];
        assert_eq!(bb1_state.locals[1], LocalState::Initialized);
    }
    
    #[test]
    fn test_move_semantics() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));
        body.local_decls.push(LocalDecl::new(MirType::Unit, None)); 
        body.local_decls.push(LocalDecl::new(MirType::Unit, None)); 
        
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)), 
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Unit, 
                        ty: MirType::Unit
                    })))
                ),
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
        assert_eq!(bb1_state.locals[1], LocalState::Moved);
        assert_eq!(bb1_state.locals[2], LocalState::Initialized);
    }

    #[test]
    fn test_branching_join() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));
        body.local_decls.push(LocalDecl::new(MirType::Unit, None)); 
        
        body.basic_blocks.push(BasicBlockData {
             statements: vec![],
             terminator: Some(Terminator::SwitchInt { 
                 discr: Operand::Constant(Box::new(Constant { 
                     literal: Literal::Nat(0), 
                     ty: MirType::Nat 
                 })),
                 targets: SwitchTargets {
                     values: vec![0],
                     targets: vec![BasicBlock(1), BasicBlock(2)]
                 }
             })
        });
        
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)), 
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Unit, 
                        ty: MirType::Unit
                    })))
                )
            ],
            terminator: Some(Terminator::Goto { target: BasicBlock(3) })
        });
        
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Goto { target: BasicBlock(3) })
        });
        
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return)
        });
        
        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        
        let bb3_state = &analysis.block_entry_states[&BasicBlock(3)];
        assert_eq!(bb3_state.locals[1], LocalState::Uninitialized);
    }

    #[test]
    fn test_linear_drop_error() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));
        // _1 : Token (Linear) -> !is_copy.
        // MirType::Adt is !Copy by default.
        body.local_decls.push(LocalDecl::new(MirType::Adt(AdtId("Token".to_string()), vec![]), Some("token".to_string())));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Unit, 
                        ty: MirType::Unit // Simplified
                    })))
                ),
                Statement::StorageDead(Local(1))
            ],
             terminator: Some(Terminator::Return)
        });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check();
        
        assert!(!errors.is_empty());
        assert!(errors[0].contains("not consumed") || errors[0].contains("without use"));
    }

    #[test]
    fn test_uninitialized_return() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));
        
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return)
        });
        
        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check();
        
        assert!(!errors.is_empty());
        assert!(errors[0].contains("return value") || errors[0].contains("Return value"));
    }

    #[test]
    fn test_double_move_in_args() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None)); 
        body.local_decls.push(LocalDecl::new(MirType::Unit, None)); 
        
        body.basic_blocks.push(BasicBlockData {
             statements: vec![
                 Statement::Assign(Place::from(Local(1)), Rvalue::Use(Operand::Constant(Box::new(Constant{literal: Literal::Unit, ty: MirType::Unit}))))
             ],
             terminator: Some(Terminator::Call {
                 func: Operand::Constant(Box::new(Constant{literal: Literal::Unit, ty: MirType::Unit})),
                 args: vec![Operand::Move(Place::from(Local(1))), Operand::Move(Place::from(Local(1)))],
                 destination: Place::from(Local(0)),
                 target: None
             })
        });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check();
        
        assert!(!errors.is_empty());
    }

    #[test]
    fn test_partial_move_safety() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));
        
        let p_field = Place { local: Local(1), projection: vec![PlaceElem::Field(0)] };
        
        body.basic_blocks.push(BasicBlockData {
             statements: vec![
                 Statement::Assign(Place::from(Local(1)), Rvalue::Use(Operand::Constant(Box::new(Constant{literal: Literal::Unit, ty: MirType::Unit}))))
             ],
             terminator: Some(Terminator::Call {
                 func: Operand::Constant(Box::new(Constant{literal: Literal::Unit, ty: MirType::Unit})),
                 args: vec![Operand::Move(p_field.clone()), Operand::Move(p_field)],
                 destination: Place::from(Local(0)),
                 target: None
             })
        });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check();
        
        assert!(!errors.is_empty());
    }
}
