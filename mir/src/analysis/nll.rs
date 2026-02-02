use crate::types::{Region, MirType, IMKind};
use crate::{Body, BasicBlock, Statement, Terminator, Place, Rvalue, Operand, Local, BorrowKind, PlaceElem, RuntimeCheckKind};
use crate::analysis::liveness::compute_liveness;
use std::collections::{HashMap, HashSet};

/// A location in the MIR (block + statement index)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Location {
    pub block: BasicBlock,
    pub statement_index: usize,
}

impl Location {
    pub fn new(block: BasicBlock, statement_index: usize) -> Self {
        Self { block, statement_index }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constraint {
    Outlives(Region, Region), // sup: sub (sup outlives sub) aka sup >= sub
}

/// A loan (borrow) in the MIR
#[derive(Debug, Clone)]
pub struct NllLoan {
    pub place: Place,
    pub region: Region,
    pub kind: BorrowKind,
    pub issued_at: Location,
    pub holder: Local,
}

/// Describes a loan's live range (where it's active)
#[derive(Debug, Clone)]
pub struct LoanWithLiveRange {
    pub loan: NllLoan,
    /// Set of locations where this loan is active
    pub live_at: HashSet<Location>,
}

/// Describes a runtime check that codegen must emit
#[derive(Debug, Clone)]
pub struct RuntimeCheck {
    pub kind: RuntimeCheckKind,
    pub location: Location,
}

/// Result of borrow checking - the contract output for codegen
///
/// This structure provides everything codegen needs to:
/// 1. Understand region lifetimes (for drop ordering, etc.)
/// 2. Know which loans are active at each point
/// 3. Emit appropriate runtime checks for interior mutability
#[derive(Debug)]
pub struct BorrowCheckResult {
    /// Region solution: maps each region to the set of locations where it's live
    pub region_solution: HashMap<Region, HashSet<Location>>,

    /// All loans with their computed live ranges
    pub loans_with_ranges: Vec<LoanWithLiveRange>,

    /// List of runtime checks that codegen must emit
    pub runtime_checks: Vec<RuntimeCheck>,

    /// Borrow check errors (empty if check passed)
    pub errors: Vec<String>,

    /// Whether the borrow check passed
    pub success: bool,
}

impl BorrowCheckResult {
    /// Returns true if the borrow check passed without errors
    pub fn is_ok(&self) -> bool {
        self.success && self.errors.is_empty()
    }

    /// Get all locations where a specific region is live
    pub fn region_live_at(&self, region: Region) -> Option<&HashSet<Location>> {
        self.region_solution.get(&region)
    }

    /// Check if a region is live at a specific location
    pub fn is_region_live_at(&self, region: Region, location: Location) -> bool {
        if region == Region::STATIC { return true; }
        self.region_solution.get(&region)
            .map(|locs| locs.contains(&location))
            .unwrap_or(false)
    }

    /// Get all active loans at a specific location
    pub fn active_loans_at(&self, location: Location) -> Vec<&NllLoan> {
        self.loans_with_ranges.iter()
            .filter(|lwr| lwr.live_at.contains(&location))
            .map(|lwr| &lwr.loan)
            .collect()
    }

    /// Insert runtime check statements into the MIR body.
    pub fn inject_runtime_checks(&self, body: &mut Body) {
        if self.runtime_checks.is_empty() {
            return;
        }

        let mut checks_by_block: HashMap<BasicBlock, Vec<(usize, RuntimeCheckKind)>> = HashMap::new();
        for check in &self.runtime_checks {
            checks_by_block
                .entry(check.location.block)
                .or_default()
                .push((check.location.statement_index, check.kind.clone()));
        }

        for (bb_idx, bb_data) in body.basic_blocks.iter_mut().enumerate() {
            let bb = BasicBlock(bb_idx as u32);
            let Some(mut checks) = checks_by_block.remove(&bb) else { continue; };
            checks.sort_by_key(|(idx, _)| *idx);

            let mut new_statements =
                Vec::with_capacity(bb_data.statements.len() + checks.len());
            let mut check_iter = checks.into_iter().peekable();

            for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
                while let Some((idx, _)) = check_iter.peek() {
                    if *idx <= stmt_idx {
                        let (_, kind) = check_iter.next().unwrap();
                        new_statements.push(Statement::RuntimeCheck(kind));
                    } else {
                        break;
                    }
                }
                new_statements.push(stmt.clone());
            }

            while let Some((_idx, kind)) = check_iter.next() {
                new_statements.push(Statement::RuntimeCheck(kind));
            }

            bb_data.statements = new_statements;
        }
    }
}

pub struct RegionInferenceContext {
    pub num_regions: usize,
    pub constraints: HashSet<Constraint>,
    /// Points where a region is required to be live
    pub liveness_constraints: HashMap<Region, HashSet<Location>>,
    pub region_values: HashMap<Region, HashSet<Location>>,
}

impl RegionInferenceContext {
    pub fn new() -> Self {
        Self {
            num_regions: 1, // 0 is STATIC
            constraints: HashSet::new(),
            liveness_constraints: HashMap::new(),
            region_values: HashMap::new(),
        }
    }

    pub fn add_constraint(&mut self, sup: Region, sub: Region) {
        if sup == sub { return; }
        if sup == Region::STATIC { return; } // Static outlives everything
        self.constraints.insert(Constraint::Outlives(sup, sub));
    }
    
    pub fn add_liveness(&mut self, region: Region, location: Location) {
        if region == Region::STATIC { return; }
        self.liveness_constraints.entry(region).or_default().insert(location);
    }
    
    pub fn solve(&mut self, _body: &Body) {
        // Initialize region values with liveness constraints
        for (r, locs) in &self.liveness_constraints {
            self.region_values.insert(*r, locs.clone());
        }
        
        // Propagate constraints: if 'a: 'b ('a >= 'b), then 'a must contain everything 'b contains.
        let mut changed = true;
        while changed {
            changed = false;
            let constraints: Vec<_> = self.constraints.iter().cloned().collect();
            for Constraint::Outlives(sup, sub) in constraints {
                let sub_locs = self.region_values.get(&sub).cloned().unwrap_or_default();
                let sup_locs = self.region_values.entry(sup).or_default();
                
                let len_before = sup_locs.len();
                sup_locs.extend(sub_locs);
                if sup_locs.len() != len_before {
                    changed = true;
                }
            }
        }
    }

    pub fn is_region_live_at(&self, region: Region, location: Location) -> bool {
        if region == Region::STATIC { return true; }
        if let Some(locs) = self.region_values.get(&region) {
            locs.contains(&location)
        } else {
            false
        }
    }
}

pub struct NllChecker<'a> {
    pub body: &'a Body,
    pub context: RegionInferenceContext,
    pub local_types: HashMap<Local, MirType>,
    pub loans: Vec<NllLoan>,
    pub errors: Vec<String>,
}

impl<'a> NllChecker<'a> {
    pub fn new(body: &'a Body) -> Self {
        let mut checker = NllChecker {
            body,
            context: RegionInferenceContext::new(),
            local_types: HashMap::new(),
            loans: Vec::new(),
            errors: Vec::new(),
        };
        checker.instantiate_local_types();
        checker
    }
    
    pub fn check(&mut self) {
        // 1. Compute Liveness (ignoring regions for now, just locals)
        let liveness = compute_liveness(self.body);
        let mut precise_liveness: HashMap<Location, HashSet<Local>> = HashMap::new();

        // 2. Compute Precise Liveness (Backward per block)
        for (bb_idx, bb_data) in self.body.basic_blocks.iter().enumerate() {
            let bb = BasicBlock(bb_idx as u32);
            let mut live = liveness.outs[&bb].clone();
            
            // Terminator
            let term_loc = Location { block: bb, statement_index: bb_data.statements.len() };
            // Live set at terminator entry
            // Note: liveness.outs is Live AFTER terminator.
            // We need Live BEFORE terminator.
            // But process_terminator updates live to "Before".
            // Actually, for NLL region liveness, we want to know if it's live *during* the instruction?
            // "A region R is live at P if a variable with type containing R is live at P".
            // If we use "Live Before", then at `x=1`, if `y` is dead before `x=1` (because it died at previous stmt), it's fine.
            // But what if `y` dies IN `x=1`? (e.g. `x = move y`).
            // Then `y` is live "at start" of `x=move y`.
            // So checking "Live Before" is correct for conflict at the statement.
            
            // However, process_terminator modifies `live`.
            // So we copy `live` (out set), process it, then store it?
            // No, we process backward.
            // Start with `out`.
            
            // Handle Terminator
            if let Some(term) = &bb_data.terminator {
                crate::analysis::liveness::process_terminator(term, &mut live);
            }
            precise_liveness.insert(term_loc, live.clone());
            
            // Handle Statements Backward
            for (stmt_idx, stmt) in bb_data.statements.iter().enumerate().rev() {
                let loc = Location { block: bb, statement_index: stmt_idx };
                crate::analysis::liveness::process_statement(stmt, &mut live);
                precise_liveness.insert(loc, live.clone());
            }
        }
        
        // 3. Record Region Liveness based on Precise Liveness
        for (loc, live_locals) in &precise_liveness {
            self.record_region_liveness(live_locals, *loc);
        }

        // 4. Generate Constraints & Loans
        for (bb_idx, bb_data) in self.body.basic_blocks.iter().enumerate() {
            let bb = BasicBlock(bb_idx as u32);
            for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
                 if let Statement::Assign(dest, rvalue) = stmt {
                     let dest_ty = self.place_type(dest);
                     
                     if let Rvalue::Ref(kind, place) = rvalue {
                         if let MirType::Ref(region, _, _) = dest_ty {
                             self.loans.push(NllLoan {
                                 place: place.clone(),
                                 region,
                                 kind: *kind,
                                 issued_at: Location { block: bb, statement_index: stmt_idx },
                                 holder: dest.local,
                             });
                         }
                     }
                     
                     let rvalue_ty = self.rvalue_type(rvalue);
                     self.relate_types(&dest_ty, &rvalue_ty);
                 }
            }
        }

        // 5. Solve
        self.context.solve(self.body);

        // 6. Check Conflicts
        self.check_conflicts();
    }
    
    fn check_conflicts(&mut self) {
        for (bb_idx, bb_data) in self.body.basic_blocks.iter().enumerate() {
            let bb = BasicBlock(bb_idx as u32);
            for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
                let loc = Location { block: bb, statement_index: stmt_idx };
                match stmt {
                    Statement::Assign(dest, rvalue) => {
                        // Check mutation of dest
                        self.check_access(dest, true, loc);
                        // Check read of rvalue
                        self.check_rvalue_access(rvalue, loc);
                    },
                    Statement::StorageDead(local) => {
                       // Check if *local is borrowed?
                       // If local is invalidated, loans of it must be dead.
                       // We check if any loan of `local` is active.
                       for loan in &self.loans {
                           if loan.place.local == *local {
                               if self.context.is_region_live_at(loan.region, loc) {
                                   self.errors.push(format!("StorageDead on {:?} while borrowed at {:?}", local, loc));
                               }
                           }
                       }
                    },
                    _ => {}
                }
            }
            if let Some(term) = &bb_data.terminator {
                let loc = Location { block: bb, statement_index: bb_data.statements.len() };
                 match term {
                     Terminator::Call { func, args, destination, .. } => {
                         self.check_operand_access(func, loc);
                         for arg in args { self.check_operand_access(arg, loc); }
                         self.check_access(destination, true, loc);
                     },
                     Terminator::SwitchInt { discr, .. } => self.check_operand_access(discr, loc),
                     Terminator::Return => {
                         // Check if return value (local 0) borrows locals that are dying?
                         // Handled by liveness: if return value has region 'r, 'r is live.
                         // If 'r points to local, local must outlive function -> impossible unless static.
                     },
                     _ => {}
                 }
            }
        }
    }
    
    fn check_access(&mut self, place: &Place, is_mut: bool, loc: Location) {
        for loan in &self.loans {
            // Is loan active?
            if self.context.is_region_live_at(loan.region, loc) {
                // Is place conflicting?
                if self.places_conflict_at(loan, place, loc) {
                    if !is_mut && loan.kind == BorrowKind::Shared { continue; }
                    
                    if is_mut {
                        self.errors.push(format!("Conflict: Mutating {:?} while borrowed ({:?}) at {:?}", place, loan.kind, loc));
                    } else if loan.kind == BorrowKind::Mut {
                         self.errors.push(format!("Conflict: Reading {:?} while mutably borrowed at {:?}", place, loc));
                    }
                }
            }
        }
    }
    
    fn check_rvalue_access(&mut self, rvalue: &Rvalue, loc: Location) {
        match rvalue {
            Rvalue::Use(op) => self.check_operand_access(op, loc),
            Rvalue::Ref(kind, p) => {
                 // Creating a ref borrows the place.
                 // &x requires Read access (is_mut = false).
                 // &mut x requires Write access (is_mut = true).
                 self.check_access(p, *kind == BorrowKind::Mut, loc);
            },
             _ => {}
        }
    }
    
    fn check_operand_access(&mut self, op: &Operand, loc: Location) {
        match op {
            Operand::Copy(p) | Operand::Move(p) => self.check_access(p, false, loc),
            _ => {}
        }
    }

    fn places_conflict_at(&self, loan: &NllLoan, place: &Place, loc: Location) -> bool {
        let access_places = self.resolve_place_at(place, loc);
        let loan_places = self.resolve_place_at(&loan.place, loc);

        for access in &access_places {
            for loan_place in &loan_places {
                if !places_conflict_base(&access.place, &loan_place.place) {
                    continue;
                }
                if loan.kind == BorrowKind::Mut && access.origin_chain.contains(&loan.holder) {
                    // Access through the holder's own mutable reference (including reborrow chains) is allowed.
                    continue;
                }
                return true;
            }
        }
        false
    }

    fn resolve_place_at(&self, place: &Place, loc: Location) -> Vec<ResolvedPlace> {
        let mut results = Vec::new();
        let mut stack = vec![(place.clone(), Vec::new())];
        let mut seen: HashSet<(Place, Vec<Local>)> = HashSet::new();

        while let Some((current, origin_chain)) = stack.pop() {
            if !seen.insert((current.clone(), origin_chain.clone())) {
                continue;
            }

            if let Some((PlaceElem::Deref, tail)) = current.projection.split_first() {
                let mut expanded = false;
                for loan in &self.loans {
                    if loan.holder == current.local && self.context.is_region_live_at(loan.region, loc) {
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
                }
                if expanded {
                    continue;
                }
            }

            results.push(ResolvedPlace { place: current, origin_chain });
        }

        results
    }

    fn record_region_liveness(&mut self, live_locals: &HashSet<Local>, loc: Location) {
        for local in live_locals {
            if let Some(ty) = self.local_types.get(local) {
                Self::add_type_regions_live(&mut self.context, ty, loc);
            }
        }
    }
    
    fn add_type_regions_live(context: &mut RegionInferenceContext, ty: &MirType, loc: Location) {
        match ty {
            MirType::Ref(r, inner, _) => {
                context.add_liveness(*r, loc);
                Self::add_type_regions_live(context, inner, loc);
            },
            MirType::Adt(_, args) => {
                for arg in args { Self::add_type_regions_live(context, arg, loc); }
            },
            MirType::InteriorMutable(inner, _) => Self::add_type_regions_live(context, inner, loc),
            _ => {}
        }
    }

    fn place_type(&self, place: &Place) -> MirType {
        let mut ty = self.local_types[&place.local].clone();
        for elem in &place.projection {
            match elem {
                PlaceElem::Deref => {
                    ty = match ty {
                        MirType::Ref(_, inner, _) => *inner,
                        MirType::RawPtr(inner, _) => *inner,
                        other => other,
                    };
                }
                PlaceElem::Field(_) | PlaceElem::Downcast(_) => {
                    // Field/variant types aren't tracked in MIR yet, so preserve the base type.
                }
            }
        }
        ty
    }
    
    fn rvalue_type(&self, rvalue: &Rvalue) -> MirType {
        match rvalue {
            Rvalue::Use(op) => self.operand_type(op),
            Rvalue::Ref(kind, place) => {
                 let place_ty = self.place_type(place);
                 MirType::Ref(Region(0), Box::new(place_ty), (*kind).into()) 
            },
            _ => MirType::Unit
        }
    }
    
    fn operand_type(&self, op: &Operand) -> MirType {
        match op {
            Operand::Copy(p) | Operand::Move(p) => self.place_type(p),
            Operand::Constant(c) => c.ty.clone(),
        }
    }

    fn relate_types(&mut self, dest: &MirType, src: &MirType) {
        match (dest, src) {
            (MirType::Ref(r1, t1, _), MirType::Ref(r2, t2, _)) => {
                // dest = src
                // &'r1 T = &'r2 T
                // We need 'r2: 'r1 (src must outlive dest)
                self.context.add_constraint(*r2, *r1);
                self.relate_types(t1, t2);
            },
            (MirType::Adt(_, args1), MirType::Adt(_, args2)) => {
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    self.relate_types(a1, a2);
                }
            },
            _ => {}
        }
    }

    fn instantiate_local_types(&mut self) {
        for (i, decl) in self.body.local_decls.iter().enumerate() {
            let ty = self.renumber_regions(&decl.ty);
            self.local_types.insert(Local(i as u32), ty);
        }
    }

    fn renumber_regions(&mut self, ty: &MirType) -> MirType {
        match ty {
            MirType::Ref(_, inner, mutability) => {
                let region = self.next_region();
                let inner_renumbered = self.renumber_regions(inner);
                MirType::Ref(region, Box::new(inner_renumbered), *mutability)
            },
            MirType::Adt(id, args) => {
                let new_args = args.iter().map(|a| self.renumber_regions(a)).collect();
                MirType::Adt(id.clone(), new_args)
            },
            MirType::Fn(args, ret) => {
                let new_args = args.iter().map(|a| self.renumber_regions(a)).collect();
                let new_ret = self.renumber_regions(ret);
                MirType::Fn(new_args, Box::new(new_ret))
            },
            MirType::RawPtr(inner, mutability) => {
                MirType::RawPtr(Box::new(self.renumber_regions(inner)), *mutability)
            },
            MirType::InteriorMutable(inner, kind) => {
                MirType::InteriorMutable(Box::new(self.renumber_regions(inner)), *kind)
            }
            _ => ty.clone(),
        }
    }

    fn next_region(&mut self) -> Region {
        let r = Region(self.context.num_regions);
        self.context.num_regions += 1;
        r
    }

    /// Collect runtime checks needed for interior mutability constructs
    fn collect_runtime_checks(&self) -> Vec<RuntimeCheck> {
        let mut checks = Vec::new();

        for (i, decl) in self.body.local_decls.iter().enumerate() {
            self.collect_runtime_checks_for_type(&decl.ty, Local(i as u32), &mut checks);
        }

        checks
    }

    fn collect_runtime_checks_for_type(&self, ty: &MirType, local: Local, checks: &mut Vec<RuntimeCheck>) {
        match ty {
            MirType::InteriorMutable(inner, kind) => {
                // Find all use sites of this local
                for (bb_idx, bb_data) in self.body.basic_blocks.iter().enumerate() {
                    for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
                        if self.statement_uses_local(stmt, local) {
                            let location = Location::new(BasicBlock(bb_idx as u32), stmt_idx);
                            match kind {
                                IMKind::RefCell => {
                                    checks.push(RuntimeCheck {
                                        kind: RuntimeCheckKind::RefCellBorrow { local },
                                        location,
                                    });
                                }
                                IMKind::Mutex => {
                                    checks.push(RuntimeCheck {
                                        kind: RuntimeCheckKind::MutexLock { local },
                                        location,
                                    });
                                }
                                IMKind::Atomic => {
                                    // Atomics don't need runtime checks, they use hardware guarantees
                                }
                            }
                        }
                    }
                    if let Some(term) = &bb_data.terminator {
                        if self.terminator_uses_local(term, local) {
                            let location = Location::new(
                                BasicBlock(bb_idx as u32),
                                bb_data.statements.len(),
                            );
                            match kind {
                                IMKind::RefCell => {
                                    checks.push(RuntimeCheck {
                                        kind: RuntimeCheckKind::RefCellBorrow { local },
                                        location,
                                    });
                                }
                                IMKind::Mutex => {
                                    checks.push(RuntimeCheck {
                                        kind: RuntimeCheckKind::MutexLock { local },
                                        location,
                                    });
                                }
                                IMKind::Atomic => {}
                            }
                        }
                    }
                }
                // Recurse into inner type
                self.collect_runtime_checks_for_type(inner, local, checks);
            }
            MirType::Ref(_, inner, _) => {
                self.collect_runtime_checks_for_type(inner, local, checks);
            }
            MirType::Adt(_, args) => {
                for arg in args {
                    self.collect_runtime_checks_for_type(arg, local, checks);
                }
            }
            _ => {}
        }
    }

    fn statement_uses_local(&self, stmt: &Statement, local: Local) -> bool {
        match stmt {
            Statement::Assign(dest, rvalue) => {
                if dest.local == local { return true; }
                match rvalue {
                    Rvalue::Use(op) => self.operand_uses_local(op, local),
                    Rvalue::Ref(_, place) => place.local == local,
                    Rvalue::Discriminant(place) => place.local == local,
                }
            }
            Statement::RuntimeCheck(_) => false,
            Statement::StorageLive(l) | Statement::StorageDead(l) => *l == local,
            Statement::Nop => false,
        }
    }

    fn terminator_uses_local(&self, term: &Terminator, local: Local) -> bool {
        match term {
            Terminator::Call { func, args, destination, .. } => {
                if self.operand_uses_local(func, local) {
                    return true;
                }
                if args.iter().any(|arg| self.operand_uses_local(arg, local)) {
                    return true;
                }
                destination.local == local
            }
            Terminator::SwitchInt { discr, .. } => self.operand_uses_local(discr, local),
            _ => false,
        }
    }

    fn operand_uses_local(&self, op: &Operand, local: Local) -> bool {
        match op {
            Operand::Copy(p) | Operand::Move(p) => p.local == local,
            Operand::Constant(_) => false,
        }
    }

    /// Convert the checker state into a structured result for codegen
    pub fn into_result(self) -> BorrowCheckResult {
        // Compute loans with live ranges
        let loans_with_ranges: Vec<LoanWithLiveRange> = self.loans.iter().map(|loan| {
            let live_at = self.context.region_values.get(&loan.region)
                .cloned()
                .unwrap_or_default();
            LoanWithLiveRange {
                loan: loan.clone(),
                live_at,
            }
        }).collect();

        // Collect runtime checks
        let runtime_checks = self.collect_runtime_checks();

        let success = self.errors.is_empty();

        BorrowCheckResult {
            region_solution: self.context.region_values,
            loans_with_ranges,
            runtime_checks,
            errors: self.errors,
            success,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ResolvedPlace {
    place: Place,
    origin_chain: Vec<Local>,
}

fn places_conflict_base(p1: &Place, p2: &Place) -> bool {
    if p1.local != p2.local {
        return false;
    }
    // Simplification: if local matches, they likely conflict unless disjoint fields.
    // E.g. x.0 vs x.1
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{LocalDecl, BasicBlockData, Constant, Literal};
    use crate::types::Mutability;

    #[test]
    fn test_renumber() {
        let mut body = Body::new(0);
        // Ref(Region(0), Nat)
        let ty = MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Not);
        body.local_decls.push(LocalDecl::new(ty, None));

        let checker = NllChecker::new(&body);

        let local_ty = &checker.local_types[&Local(0)];
        if let MirType::Ref(r, _, _) = local_ty {
            assert_eq!(r.0, 1, "Should be renumbered to 1 (0 is static)");
        } else {
            panic!("Expected Ref");
        }
        assert_eq!(checker.context.num_regions, 2);
    }

    #[test]
    fn test_borrow_check_result_success() {
        let mut body = Body::new(1);
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place::from(Local(1))))
                )
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        let result = checker.into_result();

        assert!(result.is_ok(), "Simple copy should pass borrow check");
        assert!(result.errors.is_empty());
        assert!(result.runtime_checks.is_empty(), "No interior mutability, no runtime checks");
    }

    #[test]
    fn test_borrow_check_result_with_loan() {
        let mut body = Body::new(1);
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        body.local_decls.push(LocalDecl::new(
            MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Not),
            None
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1)))
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: Local(2),
                        projection: vec![PlaceElem::Deref],
                    }))
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        let result = checker.into_result();

        assert!(result.is_ok(), "Borrow and deref should pass");
        assert_eq!(result.loans_with_ranges.len(), 1, "Should have one loan");
        assert!(!result.loans_with_ranges[0].live_at.is_empty(), "Loan should have live range");
    }

    #[test]
    fn test_borrow_check_result_with_refcell() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));
        body.local_decls.push(LocalDecl::new(
            MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell),
            None
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell),
                    })))
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        let result = checker.into_result();

        assert!(result.is_ok());
        // Should have runtime checks for RefCell usage
        assert!(!result.runtime_checks.is_empty(), "RefCell should generate runtime checks");
        assert!(matches!(result.runtime_checks[0].kind, RuntimeCheckKind::RefCellBorrow { .. }));
    }

    #[test]
    fn test_inject_runtime_checks() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));
        body.local_decls.push(LocalDecl::new(
            MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell),
            None
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell),
                    })))
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        let result = checker.into_result();
        let mut body_with_checks = body.clone();
        result.inject_runtime_checks(&mut body_with_checks);

        assert!(
            matches!(
                body_with_checks.basic_blocks[0].statements[0],
                Statement::RuntimeCheck(RuntimeCheckKind::RefCellBorrow { .. })
            ),
            "Expected runtime check to be injected before the use site"
        );
    }

    #[test]
    fn test_borrow_check_result_failure() {
        let mut body = Body::new(1);
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        body.local_decls.push(LocalDecl::new(
            MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Not),
            None
        ));

        // Borrow, mutate while borrowed, use borrow - should fail
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1)))
                ),
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(42),
                        ty: MirType::Nat,
                    })))
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: Local(2),
                        projection: vec![PlaceElem::Deref],
                    }))
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        let result = checker.into_result();

        assert!(!result.is_ok(), "Mutate-while-borrowed should fail");
        assert!(!result.errors.is_empty());
    }

    #[test]
    fn test_active_loans_at() {
        let mut body = Body::new(1);
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        body.local_decls.push(LocalDecl::new(
            MirType::Ref(Region(0), Box::new(MirType::Nat), Mutability::Not),
            None
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1)))
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: Local(2),
                        projection: vec![PlaceElem::Deref],
                    }))
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        let result = checker.into_result();

        // The loan should be active at statement 1 (where we use the reference)
        let location = Location::new(BasicBlock(0), 1);
        let active = result.active_loans_at(location);
        assert!(!active.is_empty(), "Loan should be active at use site");
    }
}
