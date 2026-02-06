use crate::errors::MirSpan;
use crate::types::{IMKind, MirType, Mutability, Region};
use crate::{
    BasicBlock, Body, BorrowKind, CallOperand, Operand, Place, PlaceElem, RuntimeCheckKind, Rvalue,
    Statement, SwitchTargets, Terminator,
};
use kernel::ast::FunctionKind;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, Clone)]
pub struct TypingError {
    message: String,
    location: Option<MirSpan>,
}

impl TypingError {
    fn new(message: impl Into<String>, location: Option<MirSpan>) -> Self {
        Self {
            message: message.into(),
            location,
        }
    }

    pub fn location(&self) -> Option<MirSpan> {
        self.location
    }

    pub fn diagnostic_code(&self) -> &'static str {
        "M300"
    }
}

impl fmt::Display for TypingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

pub struct TypingChecker<'a> {
    body: &'a Body,
    errors: Vec<TypingError>,
    next_region: usize,
}

impl<'a> TypingChecker<'a> {
    pub fn new(body: &'a Body) -> Self {
        let max_region = max_region_in_body(body);
        Self {
            body,
            errors: Vec::new(),
            next_region: max_region.saturating_add(1).max(1),
        }
    }

    pub fn check(&mut self) {
        self.errors.clear();
        for (bb_idx, bb) in self.body.basic_blocks.iter().enumerate() {
            let block = BasicBlock(bb_idx as u32);
            for (stmt_idx, stmt) in bb.statements.iter().enumerate() {
                let location = MirSpan {
                    block,
                    statement_index: stmt_idx,
                };
                self.check_statement(stmt, location);
            }
            if let Some(term) = &bb.terminator {
                let location = MirSpan {
                    block,
                    statement_index: bb.statements.len(),
                };
                self.check_terminator(term, location);
            }
        }
    }

    pub fn errors(&self) -> &[TypingError] {
        &self.errors
    }

    fn check_statement(&mut self, statement: &Statement, location: MirSpan) {
        match statement {
            Statement::Assign(place, rvalue) => self.check_assign(place, rvalue, location),
            Statement::RuntimeCheck(check) => self.check_runtime_check(check, location),
            Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => {}
        }
    }

    fn check_terminator(&mut self, terminator: &Terminator, location: MirSpan) {
        match terminator {
            Terminator::Call {
                func,
                args,
                destination,
                ..
            } => self.check_call(func, args, destination, location),
            Terminator::SwitchInt { discr, targets } => {
                self.check_switch_int(discr, targets, location);
            }
            _ => {}
        }
    }

    fn check_call(
        &mut self,
        func: &CallOperand,
        args: &[Operand],
        destination: &Place,
        location: MirSpan,
    ) {
        let func_ty = self.call_operand_type(func);
        if matches!(func_ty, MirType::Unit) {
            let dest_ty = self.place_type(destination);
            let all_args_unit = args
                .iter()
                .all(|arg| matches!(self.operand_type(arg), MirType::Unit));
            if matches!(dest_ty, MirType::Unit) && all_args_unit {
                return;
            }
        }
        let func_ty = self.normalize_callable_type(&func_ty);
        let func_ty = self.instantiate_call_regions(&func_ty);
        let kind = match &func_ty {
            MirType::Fn(kind, _, _, _) => *kind,
            _ => {
                self.errors.push(TypingError::new(
                    format!("Call operand is not a function: {:?}", func_ty),
                    Some(location),
                ));
                return;
            }
        };

        self.check_call_operand_kind(kind, func, location);

        if let CallOperand::Operand(op) = func {
            self.check_operand_copy(op, location);
        }
        let mut current_ty = func_ty.clone();
        let mut param_subst: HashMap<usize, MirType> = HashMap::new();
        for arg in args {
            self.check_operand_copy(arg, location);
            current_ty = self.substitute_type_params(&current_ty, &param_subst);
            let (kind, region_params, param_tys, ret_ty) = match &current_ty {
                MirType::Fn(kind, region_params, param_tys, ret_ty) => {
                    (kind, region_params, param_tys, ret_ty)
                }
                other => {
                    self.errors.push(TypingError::new(
                        format!("Call operand is not a function: {:?}", other),
                        Some(location),
                    ));
                    return;
                }
            };

            if param_tys.is_empty() {
                self.errors.push(TypingError::new(
                    "Call target expects no arguments".to_string(),
                    Some(location),
                ));
                return;
            }

            let param_ty = &param_tys[0];
            let arg_ty = self.operand_type(arg);
            if !self.types_compatible_call(param_ty, &arg_ty, &mut param_subst) {
                self.errors.push(TypingError::new(
                    format!(
                        "Call argument type mismatch: expected {:?}, got {:?}",
                        param_ty, arg_ty
                    ),
                    Some(location),
                ));
            }

            current_ty = if param_tys.len() == 1 {
                (**ret_ty).clone()
            } else {
                MirType::Fn(
                    *kind,
                    region_params.clone(),
                    param_tys[1..].to_vec(),
                    ret_ty.clone(),
                )
            };
        }

        let expected_ret = self.substitute_type_params(&current_ty, &param_subst);
        let dest_ty = self.place_type(destination);
        if !self.types_compatible_call(&expected_ret, &dest_ty, &mut param_subst) {
            let arg_types: Vec<MirType> = args.iter().map(|arg| self.operand_type(arg)).collect();
            let has_erased_arg = arg_types.iter().any(|ty| matches!(ty, MirType::Unit));
            if has_erased_arg && matches!(expected_ret, MirType::Fn(_, _, _, _)) {
                return;
            }
            self.errors.push(TypingError::new(
                format!(
                    "Call destination type mismatch: expected {:?}, got {:?} (callee: {:?}, args: {:?})",
                    expected_ret, dest_ty, func_ty, arg_types
                ),
                Some(location),
            ));
        }
    }

    fn check_switch_int(&mut self, discr: &Operand, targets: &SwitchTargets, location: MirSpan) {
        self.check_operand_copy(discr, location);
        let discr_ty = self.operand_type(discr);
        if !matches!(discr_ty, MirType::Nat | MirType::Unit) {
            self.errors.push(TypingError::new(
                format!("SwitchInt discriminant must be Nat, got {:?}", discr_ty),
                Some(location),
            ));
        }

        let values_len = targets.values.len();
        let targets_len = targets.targets.len();
        if targets_len < values_len || targets_len > values_len + 1 {
            self.errors.push(TypingError::new(
                format!(
                    "SwitchInt targets length mismatch: values={}, targets={}",
                    values_len, targets_len
                ),
                Some(location),
            ));
        }

        let mut seen = HashSet::new();
        for value in &targets.values {
            if !seen.insert(*value) {
                self.errors.push(TypingError::new(
                    format!("SwitchInt has duplicate value {}", value),
                    Some(location),
                ));
                break;
            }
        }
    }

    fn check_call_operand_kind(
        &mut self,
        kind: FunctionKind,
        func: &CallOperand,
        location: MirSpan,
    ) {
        let ok = match (kind, func) {
            (FunctionKind::Fn, CallOperand::Borrow(BorrowKind::Shared, _)) => true,
            (FunctionKind::FnMut, CallOperand::Borrow(BorrowKind::Mut, _)) => true,
            (FunctionKind::FnOnce, CallOperand::Operand(Operand::Move(_))) => true,
            _ => false,
        };

        if !ok {
            self.errors.push(TypingError::new(
                format!(
                    "Call operand does not match function kind {:?}: {:?}",
                    kind, func
                ),
                Some(location),
            ));
        }
    }

    fn check_assign(&mut self, destination: &Place, rvalue: &Rvalue, location: MirSpan) {
        let dest_ty = self.place_type(destination);
        match rvalue {
            Rvalue::Use(op) => {
                self.check_operand_copy(op, location);
                let rhs_ty = self.operand_type(op);
                if !self.types_compatible(&dest_ty, &rhs_ty) {
                    self.errors.push(TypingError::new(
                        format!(
                            "Assignment type mismatch: expected {:?}, got {:?}",
                            dest_ty, rhs_ty
                        ),
                        Some(location),
                    ));
                }
            }
            Rvalue::Ref(kind, place) => {
                if matches!(dest_ty, MirType::Unit) {
                    return;
                }
                let expected_mutability = match kind {
                    BorrowKind::Shared => Mutability::Not,
                    BorrowKind::Mut => Mutability::Mut,
                };
                match dest_ty {
                    MirType::Ref(_, inner, mutability) => {
                        if mutability != expected_mutability {
                            self.errors.push(TypingError::new(
                                format!(
                                    "Reference assignment mutability mismatch: expected {:?}, got {:?}",
                                    expected_mutability, mutability
                                ),
                                Some(location),
                            ));
                        }
                        let place_ty = self.place_type(place);
                        if !self.types_compatible(&inner, &place_ty) {
                            self.errors.push(TypingError::new(
                                format!(
                                    "Reference assignment type mismatch: expected {:?}, got {:?}",
                                    inner, place_ty
                                ),
                                Some(location),
                            ));
                        }
                    }
                    other => {
                        self.errors.push(TypingError::new(
                            format!(
                                "Reference assignment destination is not a reference: {:?}",
                                other
                            ),
                            Some(location),
                        ));
                    }
                }
            }
            Rvalue::Discriminant(place) => {
                if matches!(dest_ty, MirType::Unit) {
                    return;
                }
                if !self.types_compatible(&MirType::Nat, &dest_ty) {
                    self.errors.push(TypingError::new(
                        format!(
                            "Discriminant type mismatch: expected {:?}, got {:?}",
                            MirType::Nat,
                            dest_ty
                        ),
                        Some(location),
                    ));
                }
                let place_ty = self.place_type(place);
                if !self.discriminant_source_ok(&place_ty) {
                    self.errors.push(TypingError::new(
                        format!("Discriminant source type is invalid: {:?}", place_ty),
                        Some(location),
                    ));
                }
            }
        }
    }

    fn check_operand_copy(&mut self, operand: &Operand, location: MirSpan) {
        let Operand::Copy(place) = operand else {
            return;
        };
        if matches!(place.projection.first(), Some(PlaceElem::Deref)) {
            let base_ty = &self.body.local_decls[place.local.index()].ty;
            if matches!(base_ty, MirType::Ref(_, _, _) | MirType::RawPtr(_, _)) {
                return;
            }
        }
        let place_ty = self.place_type(place);
        let base_is_copy = self.body.local_decls[place.local.index()].is_copy;
        let is_copy = if place.projection.is_empty() {
            base_is_copy
        } else if base_is_copy {
            true
        } else {
            place_ty.is_copy()
        };
        if !is_copy {
            self.errors.push(TypingError::new(
                format!(
                    "Copy of non-Copy place: {:?} has type {:?}",
                    place, place_ty
                ),
                Some(location),
            ));
        }
    }

    fn check_runtime_check(&mut self, check: &RuntimeCheckKind, location: MirSpan) {
        match check {
            RuntimeCheckKind::RefCellBorrow { local } => {
                let local_ty = &self.body.local_decls[local.index()].ty;
                if !matches!(local_ty, MirType::Unit)
                    && !self.contains_interior_mutability(local_ty, IMKind::RefCell)
                {
                    self.errors.push(TypingError::new(
                        format!(
                            "Runtime check expects RefCell interior mutability, got {:?}",
                            local_ty
                        ),
                        Some(location),
                    ));
                }
            }
            RuntimeCheckKind::MutexLock { local } => {
                let local_ty = &self.body.local_decls[local.index()].ty;
                if !matches!(local_ty, MirType::Unit)
                    && !self.contains_interior_mutability(local_ty, IMKind::Mutex)
                {
                    self.errors.push(TypingError::new(
                        format!(
                            "Runtime check expects Mutex interior mutability, got {:?}",
                            local_ty
                        ),
                        Some(location),
                    ));
                }
            }
            RuntimeCheckKind::BoundsCheck { local, index } => {
                let container_ty = &self.body.local_decls[local.index()].ty;
                if !matches!(container_ty, MirType::Unit)
                    && !matches!(container_ty, MirType::Adt(_, _))
                {
                    self.errors.push(TypingError::new(
                        format!("Bounds check expects ADT container, got {:?}", container_ty),
                        Some(location),
                    ));
                }
                let index_ty = &self.body.local_decls[index.index()].ty;
                if !self.types_compatible(&MirType::Nat, index_ty) {
                    self.errors.push(TypingError::new(
                        format!(
                            "Bounds check index type mismatch: expected {:?}, got {:?}",
                            MirType::Nat,
                            index_ty
                        ),
                        Some(location),
                    ));
                }
            }
        }
    }

    fn discriminant_source_ok(&self, ty: &MirType) -> bool {
        matches!(
            ty,
            MirType::Unit | MirType::Bool | MirType::Nat | MirType::Adt(_, _)
        )
    }

    fn contains_interior_mutability(&self, ty: &MirType, kind: IMKind) -> bool {
        match ty {
            MirType::InteriorMutable(inner, inner_kind) => {
                *inner_kind == kind || self.contains_interior_mutability(inner, kind)
            }
            MirType::Ref(_, inner, _) => self.contains_interior_mutability(inner, kind),
            MirType::Adt(_, args) => args
                .iter()
                .any(|arg| self.contains_interior_mutability(arg, kind)),
            _ => false,
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
                        if let Some(elem_ty) = args.get(0).cloned() {
                            ty = elem_ty;
                        }
                    }
                    active_variant = None;
                }
            }
        }
        ty
    }

    fn operand_type(&self, op: &Operand) -> MirType {
        match op {
            Operand::Copy(p) | Operand::Move(p) => self.place_type(p),
            Operand::Constant(c) => c.ty.clone(),
        }
    }

    fn call_operand_type(&self, op: &CallOperand) -> MirType {
        match op {
            CallOperand::Operand(op) => self.operand_type(op),
            CallOperand::Borrow(_, place) => self.place_type(place),
        }
    }

    fn next_region(&mut self) -> Region {
        let region = Region(self.next_region);
        self.next_region += 1;
        region
    }

    fn instantiate_call_regions(&mut self, ty: &MirType) -> MirType {
        let MirType::Fn(_, region_params, _, _) = ty else {
            return ty.clone();
        };
        if region_params.is_empty() {
            return ty.clone();
        }
        let subst = self.instantiate_region_params(region_params);
        self.substitute_regions(ty, &subst)
    }

    fn instantiate_region_params(&mut self, region_params: &[Region]) -> HashMap<Region, Region> {
        let mut map = HashMap::new();
        for region in region_params {
            if *region == Region::STATIC {
                continue;
            }
            map.entry(*region).or_insert_with(|| self.next_region());
        }
        map
    }

    fn substitute_regions(&self, ty: &MirType, map: &HashMap<Region, Region>) -> MirType {
        match ty {
            MirType::Ref(region, inner, mutability) => {
                let region = map.get(region).copied().unwrap_or(*region);
                let inner_renumbered = self.substitute_regions(inner, map);
                MirType::Ref(region, Box::new(inner_renumbered), *mutability)
            }
            MirType::Adt(id, args) => {
                let new_args = args
                    .iter()
                    .map(|a| self.substitute_regions(a, map))
                    .collect();
                MirType::Adt(id.clone(), new_args)
            }
            MirType::Fn(kind, region_params, args, ret) => {
                let new_region_params = region_params
                    .iter()
                    .filter(|region| !map.contains_key(region))
                    .copied()
                    .collect();
                let new_args = args
                    .iter()
                    .map(|a| self.substitute_regions(a, map))
                    .collect();
                let new_ret = self.substitute_regions(ret, map);
                MirType::Fn(*kind, new_region_params, new_args, Box::new(new_ret))
            }
            MirType::FnItem(def_id, kind, region_params, args, ret) => {
                let new_region_params = region_params
                    .iter()
                    .filter(|region| !map.contains_key(region))
                    .copied()
                    .collect();
                let new_args = args
                    .iter()
                    .map(|a| self.substitute_regions(a, map))
                    .collect();
                let new_ret = self.substitute_regions(ret, map);
                MirType::FnItem(
                    *def_id,
                    *kind,
                    new_region_params,
                    new_args,
                    Box::new(new_ret),
                )
            }
            MirType::Closure(kind, self_region, region_params, args, ret) => {
                let new_region_params = region_params
                    .iter()
                    .filter(|region| !map.contains_key(region))
                    .copied()
                    .collect();
                let new_args = args
                    .iter()
                    .map(|a| self.substitute_regions(a, map))
                    .collect();
                let new_ret = self.substitute_regions(ret, map);
                let new_self_region = map.get(self_region).copied().unwrap_or(*self_region);
                MirType::Closure(
                    *kind,
                    new_self_region,
                    new_region_params,
                    new_args,
                    Box::new(new_ret),
                )
            }
            MirType::RawPtr(inner, mutability) => {
                MirType::RawPtr(Box::new(self.substitute_regions(inner, map)), *mutability)
            }
            MirType::InteriorMutable(inner, kind) => {
                MirType::InteriorMutable(Box::new(self.substitute_regions(inner, map)), *kind)
            }
            MirType::IndexTerm(term) => MirType::IndexTerm(term.clone()),
            _ => ty.clone(),
        }
    }

    fn substitute_type_params(&self, ty: &MirType, map: &HashMap<usize, MirType>) -> MirType {
        match ty {
            MirType::Param(idx) => match map.get(idx) {
                Some(bound) if !matches!(bound, MirType::Param(bound_idx) if *bound_idx == *idx) => {
                    self.substitute_type_params(bound, map)
                }
                _ => MirType::Param(*idx),
            },
            MirType::Adt(id, args) => MirType::Adt(
                id.clone(),
                args.iter()
                    .map(|arg| self.substitute_type_params(arg, map))
                    .collect(),
            ),
            MirType::Ref(region, inner, mutability) => MirType::Ref(
                *region,
                Box::new(self.substitute_type_params(inner, map)),
                *mutability,
            ),
            MirType::Fn(kind, region_params, args, ret) => MirType::Fn(
                *kind,
                region_params.clone(),
                args.iter()
                    .map(|arg| self.substitute_type_params(arg, map))
                    .collect(),
                Box::new(self.substitute_type_params(ret, map)),
            ),
            MirType::FnItem(def_id, kind, region_params, args, ret) => MirType::FnItem(
                *def_id,
                *kind,
                region_params.clone(),
                args.iter()
                    .map(|arg| self.substitute_type_params(arg, map))
                    .collect(),
                Box::new(self.substitute_type_params(ret, map)),
            ),
            MirType::Closure(kind, self_region, region_params, args, ret) => MirType::Closure(
                *kind,
                *self_region,
                region_params.clone(),
                args.iter()
                    .map(|arg| self.substitute_type_params(arg, map))
                    .collect(),
                Box::new(self.substitute_type_params(ret, map)),
            ),
            MirType::RawPtr(inner, mutability) => MirType::RawPtr(
                Box::new(self.substitute_type_params(inner, map)),
                *mutability,
            ),
            MirType::InteriorMutable(inner, kind) => MirType::InteriorMutable(
                Box::new(self.substitute_type_params(inner, map)),
                *kind,
            ),
            MirType::IndexTerm(term) => MirType::IndexTerm(term.clone()),
            MirType::Opaque { reason } => MirType::Opaque {
                reason: reason.clone(),
            },
            other => other.clone(),
        }
    }

    fn types_compatible_call(
        &self,
        expected: &MirType,
        actual: &MirType,
        map: &mut HashMap<usize, MirType>,
    ) -> bool {
        let expected = self.substitute_type_params(expected, map);
        let actual = self.substitute_type_params(actual, map);

        if let MirType::Param(idx) = expected {
            if matches!(&actual, MirType::Param(other) if *other == idx) {
                return true;
            }
            if let Some(bound) = map.get(&idx).cloned() {
                if matches!(bound, MirType::Param(other) if other == idx) {
                    return true;
                }
                return self.types_compatible_call(&bound, &actual, map);
            }
            map.insert(idx, actual);
            return true;
        }

        if let MirType::Param(_) = actual {
            return true;
        }

        if matches!(expected, MirType::Unit) || matches!(actual, MirType::Unit) {
            if matches!(expected, MirType::IndexTerm(_)) || matches!(actual, MirType::IndexTerm(_))
            {
                return false;
            }
            return !matches!(expected, MirType::Opaque { .. })
                && !matches!(actual, MirType::Opaque { .. });
        }

        if matches!(expected, MirType::Opaque { .. }) || matches!(actual, MirType::Opaque { .. }) {
            return matches!(
                (&expected, &actual),
                (MirType::Opaque { reason: e }, MirType::Opaque { reason: a }) if e == a
            );
        }

        match (&expected, &actual) {
            (MirType::Bool, MirType::Bool) | (MirType::Nat, MirType::Nat) => true,
            (MirType::Ref(_, e_inner, e_mut), MirType::Ref(_, a_inner, a_mut)) => {
                e_mut == a_mut && self.types_compatible_call(e_inner, a_inner, map)
            }
            (MirType::RawPtr(e_inner, e_mut), MirType::RawPtr(a_inner, a_mut)) => {
                e_mut == a_mut && self.types_compatible_call(e_inner, a_inner, map)
            }
            (
                MirType::InteriorMutable(e_inner, e_kind),
                MirType::InteriorMutable(a_inner, a_kind),
            ) => e_kind == a_kind && self.types_compatible_call(e_inner, a_inner, map),
            (MirType::IndexTerm(e_term), MirType::IndexTerm(a_term)) => e_term == a_term,
            (MirType::IndexTerm(_), _) | (_, MirType::IndexTerm(_)) => false,
            (MirType::Adt(e_id, e_args), MirType::Adt(a_id, a_args)) => {
                e_id == a_id
                    && e_args.len() == a_args.len()
                    && e_args
                        .iter()
                        .zip(a_args.iter())
                        .all(|(e, a)| self.types_compatible_call(e, a, map))
            }
            _ => {
                if let (Some((e_kind, e_args, e_ret)), Some((a_kind, a_args, a_ret))) =
                    (self.fn_signature(&expected), self.fn_signature(&actual))
                {
                    e_kind == a_kind
                        && e_args.len() == a_args.len()
                        && e_args
                            .iter()
                            .zip(a_args.iter())
                            .all(|(e, a)| self.types_compatible_call(e, a, map))
                        && self.types_compatible_call(e_ret, a_ret, map)
                } else {
                    false
                }
            }
        }
    }

    fn types_compatible(&self, expected: &MirType, actual: &MirType) -> bool {
        self.types_compatible_inner(expected, actual, false)
    }

    fn types_compatible_inner(&self, expected: &MirType, actual: &MirType, _in_ref: bool) -> bool {
        if matches!(expected, MirType::Unit) || matches!(actual, MirType::Unit) {
            if matches!(expected, MirType::IndexTerm(_)) || matches!(actual, MirType::IndexTerm(_))
            {
                return false;
            }
            return !matches!(expected, MirType::Opaque { .. })
                && !matches!(actual, MirType::Opaque { .. });
        }
        if matches!(expected, MirType::Opaque { .. }) || matches!(actual, MirType::Opaque { .. }) {
            return matches!(
                (expected, actual),
                (MirType::Opaque { reason: e }, MirType::Opaque { reason: a }) if e == a
            );
        }
        match (expected, actual) {
            (MirType::Unit, MirType::Unit)
            | (MirType::Bool, MirType::Bool)
            | (MirType::Nat, MirType::Nat) => true,
            (MirType::Ref(_, e_inner, e_mut), MirType::Ref(_, a_inner, a_mut)) => {
                e_mut == a_mut && self.types_compatible_inner(e_inner, a_inner, true)
            }
            (MirType::RawPtr(e_inner, e_mut), MirType::RawPtr(a_inner, a_mut)) => {
                e_mut == a_mut && self.types_compatible_inner(e_inner, a_inner, false)
            }
            (
                MirType::InteriorMutable(e_inner, e_kind),
                MirType::InteriorMutable(a_inner, a_kind),
            ) => e_kind == a_kind && self.types_compatible_inner(e_inner, a_inner, false),
            (MirType::IndexTerm(e_term), MirType::IndexTerm(a_term)) => e_term == a_term,
            (MirType::IndexTerm(_), _) | (_, MirType::IndexTerm(_)) => false,
            (MirType::Adt(e_id, e_args), MirType::Adt(a_id, a_args)) => {
                e_id == a_id
                    && e_args.len() == a_args.len()
                    && e_args
                        .iter()
                        .zip(a_args.iter())
                        .all(|(e, a)| self.types_compatible_inner(e, a, false))
            }
            (MirType::Param(_), MirType::Param(_)) => true,
            _ => {
                if let (Some((e_kind, e_args, e_ret)), Some((a_kind, a_args, a_ret))) =
                    (self.fn_signature(expected), self.fn_signature(actual))
                {
                    e_kind == a_kind
                        && e_args.len() == a_args.len()
                        && e_args
                            .iter()
                            .zip(a_args.iter())
                            .all(|(e, a)| self.types_compatible_inner(e, a, false))
                        && self.types_compatible_inner(e_ret, a_ret, false)
                } else {
                    false
                }
            }
        }
    }

    fn fn_signature<'ty>(
        &self,
        ty: &'ty MirType,
    ) -> Option<(FunctionKind, &'ty Vec<MirType>, &'ty MirType)> {
        match ty {
            MirType::Fn(kind, _regions, args, ret) => Some((*kind, args, ret)),
            MirType::FnItem(_id, kind, _regions, args, ret) => Some((*kind, args, ret)),
            MirType::Closure(kind, _self_region, _regions, args, ret) => Some((*kind, args, ret)),
            _ => None,
        }
    }

    fn normalize_callable_type(&self, ty: &MirType) -> MirType {
        match ty {
            MirType::Fn(_, _, _, _) => ty.clone(),
            MirType::FnItem(_id, kind, regions, args, ret) => {
                MirType::Fn(*kind, regions.clone(), args.clone(), ret.clone())
            }
            MirType::Closure(kind, _self_region, regions, args, ret) => {
                MirType::Fn(*kind, regions.clone(), args.clone(), ret.clone())
            }
            _ => ty.clone(),
        }
    }
}

fn max_region_in_body(body: &Body) -> usize {
    let mut max_region = 0;
    for decl in &body.local_decls {
        max_region = max_region.max(max_region_in_type(&decl.ty));
        for capture in &decl.closure_captures {
            max_region = max_region.max(max_region_in_type(capture));
        }
    }
    max_region
}

fn max_region_in_type(ty: &MirType) -> usize {
    match ty {
        MirType::Ref(region, inner, _) => region.0.max(max_region_in_type(inner)),
        MirType::Adt(_, args) => args.iter().map(max_region_in_type).max().unwrap_or(0),
        MirType::IndexTerm(_) => 0,
        MirType::Fn(_, region_params, args, ret)
        | MirType::FnItem(_, _, region_params, args, ret) => {
            let mut max_region = region_params.iter().map(|r| r.0).max().unwrap_or(0);
            for arg in args {
                max_region = max_region.max(max_region_in_type(arg));
            }
            max_region.max(max_region_in_type(ret))
        }
        MirType::Closure(_, self_region, region_params, args, ret) => {
            let mut max_region = region_params.iter().map(|r| r.0).max().unwrap_or(0);
            max_region = max_region.max(self_region.0);
            for arg in args {
                max_region = max_region.max(max_region_in_type(arg));
            }
            max_region.max(max_region_in_type(ret))
        }
        MirType::RawPtr(inner, _) => max_region_in_type(inner),
        MirType::InteriorMutable(inner, _) => max_region_in_type(inner),
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{AdtId, IMKind, IdRegistry, MirType, Mutability, Region};
    use crate::{
        BasicBlock, BasicBlockData, Body, BorrowKind, CallOperand, Constant, Literal, Local,
        LocalDecl, Operand, Place, RuntimeCheckKind, Rvalue, Statement, SwitchTargets, Terminator,
    };
    use kernel::ast::FunctionKind;
    use kernel::ast::{BinderInfo, Constructor, InductiveDecl, Level, Term};
    use kernel::checker::Env;

    fn body_with_locals(local_types: Vec<MirType>) -> Body {
        let mut body = Body::new(0);
        for (i, ty) in local_types.into_iter().enumerate() {
            let name = if i == 0 {
                Some("_return".to_string())
            } else {
                None
            };
            body.local_decls.push(LocalDecl::new(ty, name));
        }
        body
    }

    fn nat_const(n: u64) -> Operand {
        Operand::Constant(Box::new(Constant {
            literal: Literal::Nat(n),
            ty: MirType::Nat,
        }))
    }

    #[test]
    fn typing_rejects_non_function_call() {
        let mut body = body_with_locals(vec![
            MirType::Nat, // _0
            MirType::Nat, // _1: non-function callee
            MirType::Nat, // _2: arg
        ]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Call {
                func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(1))),
                args: vec![Operand::Copy(Place::from(Local(2)))],
                destination: Place::from(Local(0)),
                target: Some(BasicBlock(1)),
            }),
        });
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker
                .errors()
                .iter()
                .any(|e| e.to_string().contains("not a function")),
            "Expected non-function call error, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_rejects_argument_mismatch() {
        let mut body = body_with_locals(vec![
            MirType::Nat, // _0
            MirType::Fn(
                FunctionKind::Fn,
                Vec::new(),
                vec![MirType::Bool],
                Box::new(MirType::Nat),
            ), // _1: fn(Bool) -> Nat
            MirType::Nat, // _2: arg
        ]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Use(nat_const(0)),
            )],
            terminator: Some(Terminator::Call {
                func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(1))),
                args: vec![Operand::Copy(Place::from(Local(2)))],
                destination: Place::from(Local(0)),
                target: Some(BasicBlock(1)),
            }),
        });
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker
                .errors()
                .iter()
                .any(|e| e.to_string().contains("Call argument type mismatch")),
            "Expected argument type mismatch error, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_rejects_return_mismatch() {
        let mut body = body_with_locals(vec![
            MirType::Nat, // _0: destination expects Nat
            MirType::Fn(
                FunctionKind::Fn,
                Vec::new(),
                vec![MirType::Nat],
                Box::new(MirType::Bool),
            ), // _1: fn(Nat) -> Bool
            MirType::Nat, // _2: arg
        ]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Use(nat_const(1)),
            )],
            terminator: Some(Terminator::Call {
                func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(1))),
                args: vec![Operand::Copy(Place::from(Local(2)))],
                destination: Place::from(Local(0)),
                target: Some(BasicBlock(1)),
            }),
        });
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker
                .errors()
                .iter()
                .any(|e| e.to_string().contains("Call destination type mismatch")),
            "Expected destination type mismatch error, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_accepts_region_param_call() {
        let shared_ref = MirType::Ref(Region(7), Box::new(MirType::Nat), Mutability::Not);
        let mut body = body_with_locals(vec![
            MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not), // _0: dest
            MirType::Fn(
                FunctionKind::Fn,
                vec![Region(7)],
                vec![shared_ref.clone()],
                Box::new(shared_ref),
            ), // _1: fn<'r>(&'r Nat) -> &'r Nat
            MirType::Ref(Region(3), Box::new(MirType::Nat), Mutability::Not), // _2: arg
        ]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Call {
                func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(1))),
                args: vec![Operand::Copy(Place::from(Local(2)))],
                destination: Place::from(Local(0)),
                target: Some(BasicBlock(1)),
            }),
        });
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker.errors().is_empty(),
            "Expected region-param call to type-check, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_accepts_type_param_specialized_call() {
        let mut body = body_with_locals(vec![
            MirType::Nat, // _0: destination
            MirType::Fn(
                FunctionKind::Fn,
                Vec::new(),
                vec![MirType::Param(0)],
                Box::new(MirType::Param(0)),
            ), // _1: fn(T) -> T
            MirType::Nat, // _2: argument
        ]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Use(nat_const(42)),
            )],
            terminator: Some(Terminator::Call {
                func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(1))),
                args: vec![Operand::Copy(Place::from(Local(2)))],
                destination: Place::from(Local(0)),
                target: Some(BasicBlock(1)),
            }),
        });
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker.errors().is_empty(),
            "Expected type-param call to type-check after specialization, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_rejects_assignment_mismatch() {
        let mut body = body_with_locals(vec![
            MirType::Nat,  // _0
            MirType::Bool, // _1
        ]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Move(Place::from(Local(1)))),
            )],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker
                .errors()
                .iter()
                .any(|e| e.to_string().contains("Assignment type mismatch")),
            "Expected assignment type mismatch error, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_rejects_index_mismatch() {
        let zero = Term::ctor("Nat".to_string(), 0);
        let succ_zero = Term::app(Term::ctor("Nat".to_string(), 1), zero.clone());
        let vec_id = AdtId::new("Vec");
        let vec_zero = MirType::Adt(vec_id.clone(), vec![MirType::Nat, MirType::IndexTerm(zero)]);
        let vec_succ = MirType::Adt(vec_id, vec![MirType::Nat, MirType::IndexTerm(succ_zero)]);

        let mut body = body_with_locals(vec![vec_zero, vec_succ]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
            )],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker
                .errors()
                .iter()
                .any(|e| e.to_string().contains("Assignment type mismatch")),
            "Expected index assignment mismatch error, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_rejects_assignment_opaque_reason_mismatch() {
        let opaque_a = MirType::Opaque {
            reason: "opaque_a".to_string(),
        };
        let opaque_b = MirType::Opaque {
            reason: "opaque_b".to_string(),
        };
        let mut body = body_with_locals(vec![opaque_a.clone(), opaque_b.clone()]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Move(Place::from(Local(1)))),
            )],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker
                .errors()
                .iter()
                .any(|e| e.to_string().contains("Assignment type mismatch")),
            "Expected opaque assignment mismatch error, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_rejects_call_argument_opaque_reason_mismatch() {
        let opaque_a = MirType::Opaque {
            reason: "opaque_a".to_string(),
        };
        let opaque_b = MirType::Opaque {
            reason: "opaque_b".to_string(),
        };
        let mut body = body_with_locals(vec![
            MirType::Unit, // _0
            MirType::Fn(
                FunctionKind::Fn,
                Vec::new(),
                vec![opaque_a.clone()],
                Box::new(MirType::Unit),
            ), // _1: fn(Opaque) -> Unit
            opaque_b.clone(), // _2: arg
        ]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Call {
                func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(1))),
                args: vec![Operand::Move(Place::from(Local(2)))],
                destination: Place::from(Local(0)),
                target: Some(BasicBlock(1)),
            }),
        });
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker
                .errors()
                .iter()
                .any(|e| e.to_string().contains("Call argument type mismatch")),
            "Expected opaque call argument mismatch error, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_rejects_copy_of_opaque() {
        let opaque = MirType::Opaque {
            reason: "opaque".to_string(),
        };
        let mut body = body_with_locals(vec![opaque.clone(), opaque.clone()]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
            )],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker
                .errors()
                .iter()
                .any(|e| e.to_string().contains("Copy of non-Copy")),
            "Expected copy-of-opaque error, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_rejects_copy_of_noncopy_field() {
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

        let box_ctor_ty = Term::pi(
            Term::ind("Token".to_string()),
            Term::ind("Box".to_string()),
            BinderInfo::Default,
        );
        let box_decl = InductiveDecl::new(
            "Box".to_string(),
            sort1,
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
            MirType::Adt(token_id, vec![]),
            Some("_return".to_string()),
        ));
        body.local_decls.push(LocalDecl::new(
            MirType::Adt(box_id, vec![]),
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

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker
                .errors()
                .iter()
                .any(|e| e.to_string().contains("Copy of non-Copy")),
            "Expected copy-of-noncopy-field error, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_rejects_reference_mutability_mismatch() {
        let mut body = body_with_locals(vec![
            MirType::Ref(Region(1), Box::new(MirType::Nat), Mutability::Mut), // _0
            MirType::Nat,                                                     // _1
        ]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            )],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker.errors().iter().any(|e| e
                .to_string()
                .contains("Reference assignment mutability mismatch")),
            "Expected reference mutability mismatch error, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_rejects_discriminant_dest_mismatch() {
        let mut body = body_with_locals(vec![
            MirType::Bool, // _0
            MirType::Nat,  // _1
        ]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Discriminant(Place::from(Local(1))),
            )],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker
                .errors()
                .iter()
                .any(|e| e.to_string().contains("Discriminant type mismatch")),
            "Expected discriminant type mismatch error, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_rejects_refcell_runtime_check_without_refcell() {
        let mut body = body_with_locals(vec![
            MirType::Unit, // _0
            MirType::Nat,  // _1
        ]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::RuntimeCheck(RuntimeCheckKind::RefCellBorrow {
                local: Local(1),
            })],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker
                .errors()
                .iter()
                .any(|e| e.to_string().contains("RefCell interior mutability")),
            "Expected refcell runtime check error, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_accepts_refcell_runtime_check() {
        let mut body = body_with_locals(vec![
            MirType::Unit,                                                     // _0
            MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell), // _1
        ]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::RuntimeCheck(RuntimeCheckKind::RefCellBorrow {
                local: Local(1),
            })],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker.errors().is_empty(),
            "Expected refcell runtime check to pass, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_rejects_switch_int_non_nat_discriminant() {
        let mut body = body_with_locals(vec![
            MirType::Unit, // _0
            MirType::Bool, // _1: discr
        ]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::SwitchInt {
                discr: Operand::Copy(Place::from(Local(1))),
                targets: SwitchTargets {
                    values: vec![0],
                    targets: vec![BasicBlock(1), BasicBlock(2)],
                },
            }),
        });
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker
                .errors()
                .iter()
                .any(|e| e.to_string().contains("SwitchInt discriminant")),
            "Expected SwitchInt discriminant error, got {:?}",
            checker.errors()
        );
    }

    #[test]
    fn typing_rejects_switch_int_target_mismatch() {
        let mut body = body_with_locals(vec![
            MirType::Unit, // _0
            MirType::Nat,  // _1: discr
        ]);

        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::SwitchInt {
                discr: Operand::Copy(Place::from(Local(1))),
                targets: SwitchTargets {
                    values: vec![0, 1],
                    targets: vec![BasicBlock(1)], // too few targets
                },
            }),
        });
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        let mut checker = TypingChecker::new(&body);
        checker.check();
        assert!(
            checker
                .errors()
                .iter()
                .any(|e| e.to_string().contains("SwitchInt targets length mismatch")),
            "Expected SwitchInt targets length error, got {:?}",
            checker.errors()
        );
    }
}
