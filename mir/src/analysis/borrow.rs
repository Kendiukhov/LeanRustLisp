use crate::{Body, Local, BasicBlock, Statement, Terminator, Operand, Rvalue, Place, BorrowKind, PlaceElem};
use crate::types::{MirType, Mutability};
use crate::errors::{BorrowError, MirSpan};

use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Loan {
    pub place: Place,
    pub kind: BorrowKind,
    pub holder: Local, 
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BorrowState {
    pub holders: HashMap<Local, HashSet<Loan>>, 
}

impl BorrowState {
    pub fn new() -> Self {
        BorrowState {
            holders: HashMap::new(),
        }
    }

    pub fn active_loans(&self) -> HashSet<Loan> {
        let mut set = HashSet::new();
        for loans in self.holders.values() {
            for loan in loans {
                set.insert(loan.clone());
            }
        }
        set
    }

    pub fn join(&mut self, other: &BorrowState) -> bool {
        let mut changed = false;
        for (local, loans) in &other.holders {
            let entry = self.holders.entry(*local).or_default();
            let len_before = entry.len();
            for loan in loans {
                entry.insert(loan.clone());
            }
            if entry.len() != len_before {
                changed = true;
            }
        }
        changed
    }
    
    pub fn add_loan(&mut self, holder: Local, loan: Loan) {
        self.holders.entry(holder).or_default().insert(loan);
    }
    
    pub fn kill_loans_held_by(&mut self, holder: Local) {
        self.holders.remove(&holder);
    }
    
    pub fn check_access(&self, place: &Place, is_mut: bool) -> Result<(), String> {
        let active = self.active_loans();
        let access_places = expand_place(place, &self.holders);

        for loan in &active {
            let loan_places = expand_place(&loan.place, &self.holders);
            if !places_conflict_with_expansions(&access_places, &loan_places, loan) {
                continue;
            }

            if !is_mut && loan.kind == BorrowKind::Shared {
                continue;
            }

            if is_mut {
                return Err(format!("Cannot mutate {:?} because it is borrowed as {:?}", place, loan.kind));
            }
            if loan.kind == BorrowKind::Mut {
                return Err(format!("Cannot read {:?} because it is mutably borrowed", place));
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ResolvedPlace {
    place: Place,
    origin_chain: Vec<Local>,
}

fn expand_place(
    place: &Place,
    holders: &HashMap<Local, HashSet<Loan>>,
) -> Vec<ResolvedPlace> {
    let mut results = Vec::new();
    let mut stack = vec![(place.clone(), Vec::new())];
    let mut seen: HashSet<(Place, Vec<Local>)> = HashSet::new();

    while let Some((current, origin_chain)) = stack.pop() {
        if !seen.insert((current.clone(), origin_chain.clone())) {
            continue;
        }

        if let Some((PlaceElem::Deref, tail)) = current.projection.split_first() {
            if let Some(loans) = holders.get(&current.local) {
                let mut expanded = false;
                for loan in loans {
                    let mut new_proj = loan.place.projection.clone();
                    new_proj.extend_from_slice(tail);
                    let new_place = Place { local: loan.place.local, projection: new_proj };
                    let mut new_chain = origin_chain.clone();
                    if !new_chain.contains(&current.local) {
                        new_chain.push(current.local);
                    }
                    stack.push((new_place, new_chain));
                    expanded = true;
                }
                if expanded {
                    continue;
                }
            }
        }

        results.push(ResolvedPlace { place: current, origin_chain });
    }

    results
}

fn places_conflict_with_expansions(
    access_places: &[ResolvedPlace],
    loan_places: &[ResolvedPlace],
    loan: &Loan,
) -> bool {
    for access in access_places {
        for loan_place in loan_places {
            if !places_conflict_base(&access.place, &loan_place.place) {
                continue;
            }
            if loan.kind == BorrowKind::Mut && access.origin_chain.contains(&loan.holder) {
                    // Allow access through the holder's own mutable reference (reborrow or direct use).
                    continue;
            }
            return true;
        }
    }
    false
}

fn places_conflict_base(p1: &Place, p2: &Place) -> bool {
    if p1.local != p2.local {
        return false;
    }
    for (e1, e2) in p1.projection.iter().zip(p2.projection.iter()) {
        if e1 != e2 {
            if let (PlaceElem::Field(i), PlaceElem::Field(j)) = (e1, e2) {
                 if i != j { return false; }
            }
            if let (PlaceElem::Downcast(i), PlaceElem::Downcast(j)) = (e1, e2) {
                 if i != j { return false; }
            }
            return true;
        }
    }
    true
}

pub struct BorrowChecker<'a> {
    body: &'a Body,
    block_entry_states: HashMap<BasicBlock, BorrowState>,
    pub errors: Vec<String>,
    pub structured_errors: Vec<BorrowError>,
}

impl<'a> BorrowChecker<'a> {
    pub fn new(body: &'a Body) -> Self {
        BorrowChecker {
            body,
            block_entry_states: HashMap::new(),
            errors: Vec::new(),
            structured_errors: Vec::new(),
        }
    }

    pub fn check(&mut self) {
        let mut worklist: Vec<BasicBlock> = vec![BasicBlock(0)];
        let initial_state = BorrowState::new();
        self.block_entry_states.insert(BasicBlock(0), initial_state);

        while let Some(bb) = worklist.pop() {
            let mut state = self.block_entry_states[&bb].clone();

            if let Some(data) = self.body.basic_blocks.get(bb.0 as usize) {
                for (stmt_idx, stmt) in data.statements.iter().enumerate() {
                    let location = Some(MirSpan { block: bb, statement_index: stmt_idx });
                    if let Err(e) = self.process_statement(stmt, &mut state) {
                        self.errors.push(e);
                    }
                    self.process_statement_structured(stmt, &mut state, location);
                }

                if let Some(terminator) = &data.terminator {
                    let location = Some(MirSpan { block: bb, statement_index: data.statements.len() });
                    if let Err(e) = self.process_terminator(terminator, &mut state) {
                        self.errors.push(e);
                    }
                    self.process_terminator_structured(terminator, &mut state, location);

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
    
    fn process_statement(&self, stmt: &Statement, state: &mut BorrowState) -> Result<(), String> {
        match stmt {
            Statement::Assign(dest, rvalue) => {
                self.check_rvalue(rvalue, state)?;
                if dest.projection.is_empty() {
                    state.kill_loans_held_by(dest.local);
                }
                self.check_mutability(dest)?;
                state.check_access(dest, true)?;
                
                if let Rvalue::Ref(kind, src_place) = rvalue {
                     if dest.projection.is_empty() {
                         let loan = Loan {
                             place: src_place.clone(),
                             kind: *kind,
                             holder: dest.local
                         };
                         state.check_access(src_place, *kind == BorrowKind::Mut)?;
                         if *kind == BorrowKind::Mut {
                             self.check_mutability(src_place)?;
                         }
                         state.add_loan(dest.local, loan);
                     }
                } else if let Rvalue::Use(op) = rvalue {
                    if dest.projection.is_empty() {
                        if let Operand::Copy(src) | Operand::Move(src) = op {
                            if src.projection.is_empty() {
                                if let Some(held) = state.holders.get(&src.local).cloned() {
                                    for loan in held {
                                        state.add_loan(dest.local, loan);
                                    }
                                }
                            }
                        }
                    }
                }
            },
            Statement::RuntimeCheck(_) => {},
            Statement::StorageDead(local) => {
                let active = state.active_loans();
                for loan in &active {
                    if loan.place.local == *local {
                        return Err(format!("Dangling reference: {:?} is dropped while still borrowed (Loan: {:?})", local, loan));
                    }
                }
                state.kill_loans_held_by(*local);
            },
            _ => {}
        }
        Ok(())
    }
    
    fn process_terminator(&self, term: &Terminator, state: &mut BorrowState) -> Result<(), String> {
        match term {
            Terminator::Call { func, args, destination, .. } => {
                self.check_operand(func, state)?;
                for arg in args {
                    self.check_operand(arg, state)?;
                }
                if destination.projection.is_empty() {
                     state.kill_loans_held_by(destination.local);
                }
            },
            Terminator::Return => {
                if let Some(held) = state.holders.get(&Local(0)) {
                    for loan in held {
                        return Err(format!("Escaping reference: Returning a reference to local variable {:?}", loan.place));
                    }
                }
            },
            Terminator::SwitchInt { discr, .. } => {
                self.check_operand(discr, state)?;
            },
            _ => {}
        }
        Ok(())
    }

    fn check_rvalue(&self, rvalue: &Rvalue, state: &BorrowState) -> Result<(), String> {
        match rvalue {
            Rvalue::Use(op) => self.check_operand(op, state),
            Rvalue::Ref(_, _) => Ok(()),
            _ => Ok(())
        }
    }
    
    fn check_operand(&self, op: &Operand, state: &BorrowState) -> Result<(), String> {
        match op {
            Operand::Move(place) => {
                for elem in &place.projection {
                    if let PlaceElem::Deref = elem {
                         return Err(format!("Cannot move out of reference: {:?}", place));
                    }
                }
                state.check_access(place, true)
            },
            Operand::Copy(place) => {
                state.check_access(place, false)
            },
             _ => Ok(())
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

    fn check_mutability(&self, place: &Place) -> Result<(), String> {
        let mut current_ty = self.body.local_decls[place.local.index()].ty.clone();
        
        for elem in &place.projection {
            match elem {
                PlaceElem::Deref => {
                    if let MirType::Ref(_, inner, mutability) = current_ty {
                        if mutability == Mutability::Not {
                            return Err(format!("Cannot mutate immutable reference content in {:?}", place));
                        }
                        current_ty = *inner;
                    } else {
                         // Deref of non-ref?
                         // Maybe RawPtr?
                    }
                },
                PlaceElem::Field(_) => {
                    // For now assume field preserves mutability
                    // If we had ADT defs, we could look up field type.
                    // But we erase field types in ADT for now?
                    // MirType::Adt(id, args).
                    // We can't know the field type easily without context.
                    // Assume Any.
                },
                _ => {}
            }
        }
        Ok(())
    }

    fn process_statement_structured(
        &mut self,
        stmt: &Statement,
        state: &mut BorrowState,
        location: Option<MirSpan>,
    ) {
        match stmt {
            Statement::Assign(dest, rvalue) => {
                if let Rvalue::Use(Operand::Move(place)) = rvalue {
                    for elem in &place.projection {
                        if let PlaceElem::Deref = elem {
                            self.structured_errors.push(BorrowError::MoveOutOfRef {
                                place: place.clone(),
                                location,
                            });
                            return;
                        }
                    }
                }

                if dest.projection.is_empty() {
                    if let Err(_) = state.check_access(dest, true) {
                        self.structured_errors.push(BorrowError::AssignWhileBorrowed {
                            place: dest.clone(),
                            location,
                        });
                    }
                }

                if let Rvalue::Ref(kind, src_place) = rvalue {
                    if *kind == BorrowKind::Mut {
                        if let Err(_) = self.check_mutability(src_place) {
                            self.structured_errors.push(BorrowError::MutateSharedRef {
                                place: src_place.clone(),
                                location,
                            });
                        }
                    }
                }
            }
            Statement::RuntimeCheck(_) => {}
            Statement::StorageDead(local) => {
                let active = state.active_loans();
                for loan in &active {
                    if loan.place.local == *local {
                        self.structured_errors.push(BorrowError::DanglingReference {
                            borrowed_local: *local,
                            location,
                        });
                        break;
                    }
                }
            }
            _ => {}
        }
    }

    fn process_terminator_structured(
        &mut self,
        term: &Terminator,
        state: &mut BorrowState,
        location: Option<MirSpan>,
    ) {
        match term {
            Terminator::Call { func, args, .. } => {
                if let Operand::Move(place) = func {
                    for elem in &place.projection {
                        if let PlaceElem::Deref = elem {
                            self.structured_errors.push(BorrowError::MoveOutOfRef {
                                place: place.clone(),
                                location,
                            });
                        }
                    }
                }
                for arg in args {
                    if let Operand::Move(place) = arg {
                        for elem in &place.projection {
                            if let PlaceElem::Deref = elem {
                                self.structured_errors.push(BorrowError::MoveOutOfRef {
                                    place: place.clone(),
                                    location,
                                });
                            }
                        }
                    }
                }
            }
            Terminator::Return => {
                if let Some(held) = state.holders.get(&Local(0)) {
                    for loan in held {
                        self.structured_errors.push(BorrowError::EscapingReference {
                            place: loan.place.clone(),
                            location,
                        });
                    }
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

    fn create_dummy_body(locals: usize) -> Body {
        let mut body = Body::new(0);
        for _ in 0..=locals {
             body.local_decls.push(LocalDecl::new(MirType::Unit, None));
        }
        body
    }

    #[test]
    fn test_loan_creation_and_kill() {
        let mut body = create_dummy_body(2);
        
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1)))
                )
            ],
            terminator: Some(Terminator::Goto { target: BasicBlock(1) })
        });
        
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat
                    })))
                )
            ],
            terminator: Some(Terminator::Return)
        });
        
        let mut checker = BorrowChecker::new(&body);
        checker.check();
        assert!(checker.errors.is_empty());
    }

    // ... other tests need updating with MirType ...
    // I'll update them later if needed, they are mostly structural so create_dummy_body update covers them.
    // Except tests that manually construct Ref types.
    
    #[test]
    fn test_mutate_shared_ref() {
        let mut body = create_dummy_body(2);
        
        // Ref Shared Nat
        let ref_shared_nat = MirType::Ref(Region::STATIC, Box::new(MirType::Nat), Mutability::Not);
        
        body.local_decls[1].ty = ref_shared_nat;
        
        let p_deref = Place { local: Local(1), projection: vec![PlaceElem::Deref] };
        
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    p_deref, 
                    Rvalue::Use(Operand::Constant(Box::new(Constant{literal: Literal::Nat(5), ty: MirType::Nat })))
                )
            ],
            terminator: Some(Terminator::Return)
        });
        
        let mut checker = BorrowChecker::new(&body);
        checker.check();
        
        assert!(!checker.errors.is_empty());
        assert!(checker.errors[0].contains("Cannot mutate immutable reference"));
    }

    #[test]
    fn test_shared_loan_conflicts_with_deref_write() {
        let mut body = create_dummy_body(2);

        // x: Nat
        body.local_decls[1].ty = MirType::Nat;
        // r: &mut Nat (type chosen to avoid mutability error; borrow kind is Shared)
        body.local_decls[2].ty = MirType::Ref(Region::STATIC, Box::new(MirType::Nat), Mutability::Mut);

        let r_deref = Place { local: Local(2), projection: vec![PlaceElem::Deref] };

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::Assign(
                    r_deref,
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(1),
                        ty: MirType::Nat,
                    }))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = BorrowChecker::new(&body);
        checker.check();

        assert!(!checker.errors.is_empty(), "Shared loan should block deref write");
        assert!(checker.errors[0].contains("borrowed as Shared"));
    }

    #[test]
    fn test_disjoint_field_borrow_allowed() {
        let mut body = create_dummy_body(2);

        let pair_ty = MirType::Adt(crate::types::AdtId("Pair".to_string()), vec![]);
        body.local_decls[1].ty = pair_ty.clone();
        body.local_decls[2].ty = MirType::Ref(Region::STATIC, Box::new(pair_ty.clone()), Mutability::Not);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
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
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = BorrowChecker::new(&body);
        checker.check();

        assert!(checker.errors.is_empty(), "Disjoint field write should be allowed");
    }

    #[test]
    fn test_disjoint_downcast_borrow_allowed() {
        let mut body = create_dummy_body(2);

        let enum_ty = MirType::Adt(crate::types::AdtId("Enum".to_string()), vec![]);
        body.local_decls[1].ty = enum_ty.clone();
        body.local_decls[2].ty = MirType::Ref(Region::STATIC, Box::new(MirType::Nat), Mutability::Not);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Ref(
                        BorrowKind::Shared,
                        Place {
                            local: Local(1),
                            projection: vec![PlaceElem::Downcast(0), PlaceElem::Field(0)],
                        },
                    ),
                ),
                Statement::Assign(
                    Place {
                        local: Local(1),
                        projection: vec![PlaceElem::Downcast(1), PlaceElem::Field(0)],
                    },
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::Nat,
                    }))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = BorrowChecker::new(&body);
        checker.check();

        assert!(checker.errors.is_empty(), "Disjoint downcast field write should be allowed");
    }
}
