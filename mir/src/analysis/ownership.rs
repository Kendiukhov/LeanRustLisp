use crate::errors::{MirSpan, OwnershipError};
use crate::types::MirType;
use crate::{
    BasicBlock, Body, CallOperand, Local, Operand, Place, PlaceElem, RuntimeCheckKind, Rvalue,
    Statement, Terminator,
};
use kernel::ast::FunctionKind;
use std::collections::{hash_map::Entry, HashMap, HashSet};

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
                        match self.block_entry_states.entry(target) {
                            Entry::Vacant(entry) => {
                                entry.insert(state.clone());
                                worklist.push(target);
                            }
                            Entry::Occupied(mut entry) => {
                                if entry.get_mut().join(&state) {
                                    worklist.push(target);
                                }
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
                    let location = Some(MirSpan {
                        block: *bb,
                        statement_index: stmt_idx,
                    });
                    self.check_statement_structured(stmt, &mut state, location, &mut errors);
                    self.apply_statement(stmt, &mut state);
                }
                if let Some(term) = &data.terminator {
                    let location = Some(MirSpan {
                        block: *bb,
                        statement_index: data.statements.len(),
                    });
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
            Terminator::Return => {}
            Terminator::Goto { .. } => {}
            Terminator::Call {
                func,
                args,
                destination,
                ..
            } => {
                if self.call_consumes_func(func) {
                    if let CallOperand::Operand(op) = func {
                        self.check_operand_moves(op, state);
                    }
                }
                for arg in args {
                    self.check_operand_moves(arg, state);
                }
                if destination.projection.is_empty() {
                    state.locals[destination.local.0 as usize] = LocalState::Initialized;
                }
            }
            Terminator::SwitchInt { discr, .. } => {
                self.check_operand_moves(discr, state);
            }
            Terminator::Unreachable => {}
        }
    }

    fn call_consumes_func(&self, func: &CallOperand) -> bool {
        match func {
            CallOperand::Borrow(_, _) => false,
            CallOperand::Operand(op) => match op {
                Operand::Copy(_) => false,
                Operand::Move(place) => {
                    let decl = &self.body.local_decls[place.local.index()];
                    if decl.is_copy {
                        return false;
                    }
                    match &decl.ty {
                        MirType::Fn(kind, _, _, _)
                        | MirType::FnItem(_, kind, _, _, _)
                        | MirType::Closure(kind, _, _, _, _) => {
                            matches!(kind, FunctionKind::FnOnce)
                        }
                        _ => true,
                    }
                }
                Operand::Constant(_) => false,
            },
        }
    }

    fn check_rvalue_moves(&self, rvalue: &Rvalue, state: &mut OwnershipState) {
        match rvalue {
            Rvalue::Use(op) => self.check_operand_moves(op, state),
            Rvalue::Ref(_, _) => {}
            Rvalue::Discriminant(_) => {}
        }
    }

    fn check_operand_moves(&self, operand: &Operand, state: &mut OwnershipState) {
        match operand {
            Operand::Move(place) => {
                if !place.projection.is_empty() {
                    // Allow partial moves from projections (e.g., destructuring ADTs).
                    // MIR ownership tracking is local-granular, so we avoid marking the
                    // entire base local as moved when only a field is moved out.
                    return;
                }
                let decl = &self.body.local_decls[place.local.index()];
                if let MirType::Fn(kind, _, _, _) | MirType::Closure(kind, _, _, _, _) = &decl.ty {
                    if matches!(kind, FunctionKind::Fn | FunctionKind::FnMut) {
                        // Function values are duplicable in the source semantics; do not
                        // treat moves as consuming the local for ownership tracking.
                        return;
                    }
                }
                if matches!(decl.ty, MirType::FnItem(_, _, _, _, _)) {
                    return;
                }
                state.locals[place.local.0 as usize] = LocalState::Moved;
            }
            Operand::Copy(_place) => {}
            Operand::Constant(c) => {
                if let Some(captures) = c.literal.capture_operands() {
                    for cap in captures {
                        self.check_operand_moves(cap, state);
                    }
                }
            }
        }
    }

    fn successors(&self, term: &Terminator) -> Vec<BasicBlock> {
        match term {
            Terminator::Goto { target } => vec![*target],
            Terminator::Call { target, .. } => {
                if let Some(t) = target {
                    vec![*t]
                } else {
                    vec![]
                }
            }
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
            Statement::Assign(_place, rvalue) => {
                self.check_rvalue_structured(rvalue, state, location, errors);
            }
            Statement::RuntimeCheck(check) => {
                self.check_runtime_check(check, state, location, errors);
            }
            Statement::StorageDead(_local) => {}
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
                let place = Place::from(*local);
                self.check_place_read(&place, state, location, errors);
            }
            RuntimeCheckKind::BoundsCheck { local, index } => {
                let place = Place::from(*local);
                self.check_place_read(&place, state, location, errors);
                let index_place = Place::from(*index);
                self.check_place_read(&index_place, state, location, errors);
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
                let mut moved_in_args: HashSet<Local> = HashSet::new();

                self.check_call_operand_structured(func, &temp_state, location, errors);
                if self.call_consumes_func(func) {
                    if let CallOperand::Operand(op) = func {
                        if let Operand::Move(place) = op {
                            moved_in_args.insert(place.local);
                        }
                        self.check_operand_moves(op, &mut temp_state);
                    }
                }

                for arg in args {
                    if let Operand::Move(place) = arg {
                        if moved_in_args.contains(&place.local) {
                            errors.push(OwnershipError::DoubleMoveInArgs {
                                local: place.local,
                                location,
                            });
                        } else {
                            moved_in_args.insert(place.local);
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
        if let Rvalue::Use(op) = rvalue {
            self.check_operand_structured(op, state, location, errors);
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
                self.check_place_read(place, state, location, errors);
                if matches!(place.projection.first(), Some(PlaceElem::Deref)) {
                    let base_ty = &self.body.local_decls[place.local.index()].ty;
                    if matches!(base_ty, MirType::Ref(_, _, _) | MirType::RawPtr(_, _)) {
                        return;
                    }
                }
                let base_is_copy = self.body.local_decls[place.local.index()].is_copy;
                let is_copy = if place.projection.is_empty() {
                    base_is_copy
                } else if base_is_copy {
                    true
                } else {
                    let place_ty = self.place_type(place);
                    place_ty.is_copy()
                };
                if !is_copy {
                    errors.push(OwnershipError::CopyOfNonCopy {
                        place: place.clone(),
                        location,
                    });
                }
            }
            Operand::Constant(c) => {
                if let Some(captures) = c.literal.capture_operands() {
                    for cap in captures {
                        self.check_operand_structured(cap, state, location, errors);
                    }
                }
            }
        }
    }

    fn check_call_operand_structured(
        &self,
        operand: &CallOperand,
        state: &OwnershipState,
        location: Option<MirSpan>,
        errors: &mut Vec<OwnershipError>,
    ) {
        match operand {
            CallOperand::Borrow(_, place) => {
                self.check_place_read(place, state, location, errors);
            }
            CallOperand::Operand(op) => {
                self.check_operand_structured(op, state, location, errors);
            }
        }
    }

    fn check_place_read(
        &self,
        place: &Place,
        state: &OwnershipState,
        location: Option<MirSpan>,
        errors: &mut Vec<OwnershipError>,
    ) {
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

    fn place_type(&self, place: &Place) -> MirType {
        let decl = &self.body.local_decls[place.local.index()];
        let mut ty = decl.ty.clone();
        let mut active_variant: Option<usize> = None;
        let mut projections = place.projection.iter().peekable();

        if let Some(PlaceElem::Field(idx)) = projections.peek() {
            if !decl.closure_captures.is_empty() {
                if let Some(field_ty) = decl.closure_captures.get(*idx) {
                    ty = field_ty.clone();
                    projections.next();
                }
            }
        }

        for elem in projections {
            match elem {
                PlaceElem::Downcast(idx) => {
                    active_variant = Some(*idx);
                }
                PlaceElem::Deref => {
                    ty = match ty {
                        MirType::Ref(_, inner, _) => *inner,
                        MirType::RawPtr(inner, _) => *inner,
                        other => other,
                    };
                    active_variant = None;
                }
                PlaceElem::Field(idx) => {
                    if let MirType::Adt(adt_id, args) = &ty {
                        if let Some(field_ty) =
                            self.body
                                .adt_layouts
                                .field_type(adt_id, active_variant, *idx, args)
                        {
                            ty = field_ty;
                        }
                    }
                    active_variant = None;
                }
                PlaceElem::Index(_) => {
                    if let MirType::Adt(_, args) = &ty {
                        if let Some(elem_ty) = args.first().cloned() {
                            ty = elem_ty;
                        }
                    }
                    active_variant = None;
                }
            }
        }
        ty
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::*;
    use crate::*;
    use kernel::ast::{BinderInfo, Constructor, FunctionKind, InductiveDecl, Level, Term};
    use kernel::checker::Env;

    #[test]
    fn test_linear_initialization() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            )],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(1),
            }),
        });
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

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
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Unit,
                        ty: MirType::Unit,
                    }))),
                ),
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Unit,
                        ty: MirType::Unit,
                    }))),
                ),
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Use(Operand::Move(Place::from(Local(1)))),
                ),
            ],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(1),
            }),
        });
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

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
                    ty: MirType::Nat,
                })),
                targets: SwitchTargets {
                    values: vec![0],
                    targets: vec![BasicBlock(1), BasicBlock(2)],
                },
            }),
        });

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            )],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(3),
            }),
        });

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(3),
            }),
        });

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();

        let bb3_state = &analysis.block_entry_states[&BasicBlock(3)];
        assert_eq!(bb3_state.locals[1], LocalState::Uninitialized);
    }

    #[test]
    fn test_affine_drop_ok() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));
        // _1 : Token (non-Copy). MirType::Adt is !Copy by default.
        body.local_decls.push(LocalDecl::new(
            MirType::Adt(AdtId::new("Token"), vec![]),
            Some("token".to_string()),
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Unit,
                        ty: MirType::Unit,
                    }))),
                ),
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Unit,
                        ty: MirType::Unit, // Simplified
                    }))),
                ),
                Statement::StorageDead(Local(1)),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check();

        assert!(
            errors.is_empty(),
            "Affine drop should be allowed, but got errors: {:?}",
            errors
        );
    }

    #[test]
    fn test_uninitialized_return() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
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
            statements: vec![Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            )],
            terminator: Some(Terminator::Call {
                func: CallOperand::from(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
                args: vec![
                    Operand::Move(Place::from(Local(1))),
                    Operand::Move(Place::from(Local(1))),
                ],
                destination: Place::from(Local(0)),
                target: None,
            }),
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

        let p_field = Place {
            local: Local(1),
            projection: vec![PlaceElem::Field(0)],
        };

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(1)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
            )],
            terminator: Some(Terminator::Call {
                func: CallOperand::from(Operand::Constant(Box::new(Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                }))),
                args: vec![Operand::Move(p_field.clone()), Operand::Move(p_field)],
                destination: Place::from(Local(0)),
                target: None,
            }),
        });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check();

        assert!(!errors.is_empty());
    }

    #[test]
    fn test_fn_call_does_not_consume() {
        let mut body = Body::new(0);
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("_0".to_string())));
        body.local_decls.push(LocalDecl::new(
            MirType::Fn(
                FunctionKind::Fn,
                Vec::new(),
                vec![MirType::Nat],
                Box::new(MirType::Nat),
            ),
            Some("f".to_string()),
        ));
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("x".to_string())));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Unit,
                        ty: MirType::Unit,
                    }))),
                ),
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(1),
                        ty: MirType::Nat,
                    }))),
                ),
            ],
            terminator: Some(Terminator::Call {
                func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(1))),
                args: vec![Operand::Copy(Place::from(Local(2)))],
                destination: Place::from(Local(0)),
                target: Some(BasicBlock(1)),
            }),
        });

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Call {
                func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(1))),
                args: vec![Operand::Copy(Place::from(Local(2)))],
                destination: Place::from(Local(0)),
                target: Some(BasicBlock(2)),
            }),
        });

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check();

        assert!(
            errors.is_empty(),
            "Fn calls should not consume the function value: {:?}",
            errors
        );
    }

    #[test]
    fn test_fnmut_call_does_not_consume() {
        let mut body = Body::new(0);
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("_0".to_string())));
        body.local_decls.push(LocalDecl::new(
            MirType::Fn(
                FunctionKind::FnMut,
                Vec::new(),
                vec![MirType::Nat],
                Box::new(MirType::Nat),
            ),
            Some("f".to_string()),
        ));
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("x".to_string())));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Unit,
                        ty: MirType::Unit,
                    }))),
                ),
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(1),
                        ty: MirType::Nat,
                    }))),
                ),
            ],
            terminator: Some(Terminator::Call {
                func: CallOperand::Borrow(BorrowKind::Mut, Place::from(Local(1))),
                args: vec![Operand::Copy(Place::from(Local(2)))],
                destination: Place::from(Local(0)),
                target: Some(BasicBlock(1)),
            }),
        });

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Call {
                func: CallOperand::Borrow(BorrowKind::Mut, Place::from(Local(1))),
                args: vec![Operand::Copy(Place::from(Local(2)))],
                destination: Place::from(Local(0)),
                target: Some(BasicBlock(2)),
            }),
        });

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check();

        assert!(
            errors.is_empty(),
            "FnMut calls should not consume the function value: {:?}",
            errors
        );
    }

    #[test]
    fn test_fnonce_call_consumes() {
        let mut body = Body::new(0);
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("_0".to_string())));
        body.local_decls.push(LocalDecl::new(
            MirType::Fn(
                FunctionKind::FnOnce,
                Vec::new(),
                vec![MirType::Nat],
                Box::new(MirType::Nat),
            ),
            Some("f".to_string()),
        ));
        body.local_decls
            .push(LocalDecl::new(MirType::Nat, Some("x".to_string())));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Unit,
                        ty: MirType::Unit,
                    }))),
                ),
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(1),
                        ty: MirType::Nat,
                    }))),
                ),
            ],
            terminator: Some(Terminator::Call {
                func: CallOperand::from(Operand::Move(Place::from(Local(1)))),
                args: vec![Operand::Copy(Place::from(Local(2)))],
                destination: Place::from(Local(0)),
                target: Some(BasicBlock(1)),
            }),
        });

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Call {
                func: CallOperand::from(Operand::Move(Place::from(Local(1)))),
                args: vec![Operand::Copy(Place::from(Local(2)))],
                destination: Place::from(Local(0)),
                target: Some(BasicBlock(2)),
            }),
        });

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check();

        assert!(
            !errors.is_empty(),
            "FnOnce calls should consume the function value"
        );
    }

    #[test]
    fn test_copy_of_noncopy_rejected() {
        let mut body = Body::new(0);
        let ref_mut = MirType::Ref(Region(1), Box::new(MirType::Nat), Mutability::Mut);

        body.local_decls.push(LocalDecl::new(ref_mut.clone(), None)); // _0 return
        body.local_decls.push(LocalDecl::new(MirType::Nat, None)); // _1 x
        body.local_decls.push(LocalDecl::new(ref_mut, None)); // _2 r

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
                    Rvalue::Ref(BorrowKind::Mut, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place::from(Local(2)))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check_structured();
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, OwnershipError::CopyOfNonCopy { .. })),
            "Expected CopyOfNonCopy error, got {:?}",
            errors
        );
    }

    #[test]
    fn test_copy_of_noncopy_param_field_rejected() {
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

        let mut body = Body::new(0);
        body.adt_layouts = ids.adt_layouts().clone();
        body.local_decls.push(LocalDecl::new(
            MirType::Adt(token_id.clone(), vec![]),
            Some("_return".to_string()),
        ));
        body.local_decls.push(LocalDecl::new(
            MirType::Adt(box_id, vec![MirType::Adt(token_id, vec![])]),
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

        let mut analysis = OwnershipAnalysis::new(&body);
        analysis.analyze();
        let errors = analysis.check_structured();
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, OwnershipError::CopyOfNonCopy { .. })),
            "Expected CopyOfNonCopy error for param field, got {:?}",
            errors
        );
    }
}
