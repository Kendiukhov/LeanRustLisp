use crate::analysis::liveness::{compute_liveness, LocalSet};
use crate::errors::{
    BorrowError, BorrowErrorContext, BorrowLoanContext, MirSpan, RegionConstraintChain,
};
use crate::types::{IMKind, MirType, Region};
use crate::{
    BasicBlock, Body, BorrowKind, CallOperand, Literal, Local, Operand, Place, PlaceElem,
    RuntimeCheckKind, Rvalue, Statement, Terminator,
};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

/// A location in the MIR (block + statement index)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Location {
    pub block: BasicBlock,
    pub statement_index: usize,
}

impl Location {
    pub fn new(block: BasicBlock, statement_index: usize) -> Self {
        Self {
            block,
            statement_index,
        }
    }
}

/// Maps MIR locations to a compact linear index for bitset storage.
#[derive(Debug, Clone)]
pub struct LocationIndex {
    block_offsets: Vec<usize>,
    block_lengths: Vec<usize>,
    total: usize,
}

impl LocationIndex {
    pub fn new(body: &Body) -> Self {
        let mut block_offsets = Vec::with_capacity(body.basic_blocks.len());
        let mut block_lengths = Vec::with_capacity(body.basic_blocks.len());
        let mut total = 0;
        for bb in &body.basic_blocks {
            block_offsets.push(total);
            let len = bb.statements.len() + 1; // +1 for terminator slot
            block_lengths.push(len);
            total += len;
        }
        Self {
            block_offsets,
            block_lengths,
            total,
        }
    }

    pub fn len(&self) -> usize {
        self.total
    }

    pub fn is_empty(&self) -> bool {
        self.total == 0
    }

    pub fn index(&self, location: Location) -> Option<usize> {
        let block_idx = location.block.0 as usize;
        if block_idx >= self.block_offsets.len() {
            return None;
        }
        let len = self.block_lengths[block_idx];
        if location.statement_index >= len {
            return None;
        }
        Some(self.block_offsets[block_idx] + location.statement_index)
    }

    pub fn location(&self, index: usize) -> Option<Location> {
        if index >= self.total || self.block_offsets.is_empty() {
            return None;
        }
        let mut lo = 0;
        let mut hi = self.block_offsets.len();
        while lo + 1 < hi {
            let mid = (lo + hi) / 2;
            if self.block_offsets[mid] <= index {
                lo = mid;
            } else {
                hi = mid;
            }
        }
        let block_idx = lo;
        let offset = self.block_offsets[block_idx];
        let stmt_idx = index - offset;
        if stmt_idx >= self.block_lengths[block_idx] {
            return None;
        }
        Some(Location {
            block: BasicBlock(block_idx as u32),
            statement_index: stmt_idx,
        })
    }
}

/// Compact set of MIR locations backed by a bitset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocationSet {
    words: Vec<u64>,
    num_bits: usize,
}

impl LocationSet {
    pub fn new(num_bits: usize) -> Self {
        let words = vec![0; (num_bits + 63) / 64];
        Self { words, num_bits }
    }

    pub fn is_empty(&self) -> bool {
        self.words.iter().all(|word| *word == 0)
    }

    pub fn insert_index(&mut self, index: usize) -> bool {
        if index >= self.num_bits {
            return false;
        }
        let word_idx = index / 64;
        let bit_idx = index % 64;
        let mask = 1u64 << bit_idx;
        let before = self.words[word_idx];
        self.words[word_idx] |= mask;
        before != self.words[word_idx]
    }

    pub fn insert_location(&mut self, index: &LocationIndex, location: Location) -> bool {
        match index.index(location) {
            Some(idx) => self.insert_index(idx),
            None => false,
        }
    }

    pub fn contains_index(&self, index: usize) -> bool {
        if index >= self.num_bits {
            return false;
        }
        let word_idx = index / 64;
        let bit_idx = index % 64;
        (self.words[word_idx] & (1u64 << bit_idx)) != 0
    }

    pub fn contains_location(&self, index: &LocationIndex, location: Location) -> bool {
        match index.index(location) {
            Some(idx) => self.contains_index(idx),
            None => false,
        }
    }

    pub fn union_with(&mut self, other: &LocationSet) -> bool {
        debug_assert_eq!(
            self.words.len(),
            other.words.len(),
            "LocationSet size mismatch"
        );
        let mut changed = false;
        for (word, other_word) in self.words.iter_mut().zip(other.words.iter()) {
            let before = *word;
            *word |= *other_word;
            if *word != before {
                changed = true;
            }
        }
        changed
    }

    fn iter_indices(&self) -> LocationSetIter<'_> {
        LocationSetIter {
            words: &self.words,
            word_index: 0,
            current_word: 0,
            base_index: 0,
            num_bits: self.num_bits,
        }
    }

    pub fn to_locations(&self, index: &LocationIndex) -> Vec<Location> {
        let mut locations = Vec::new();
        for idx in self.iter_indices() {
            if let Some(location) = index.location(idx) {
                locations.push(location);
            }
        }
        locations
    }
}

pub struct LocationSetIter<'a> {
    words: &'a [u64],
    word_index: usize,
    current_word: u64,
    base_index: usize,
    num_bits: usize,
}

impl<'a> Iterator for LocationSetIter<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.current_word == 0 {
                if self.word_index >= self.words.len() {
                    return None;
                }
                self.current_word = self.words[self.word_index];
                self.base_index = self.word_index * 64;
                self.word_index += 1;
                continue;
            }
            let tz = self.current_word.trailing_zeros() as usize;
            let idx = self.base_index + tz;
            self.current_word &= self.current_word - 1;
            if idx < self.num_bits {
                return Some(idx);
            }
        }
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
    pub live_at: LocationSet,
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
#[derive(Debug, Clone)]
pub struct BorrowCheckResult {
    /// Region solution: maps each region to the set of locations where it's live
    pub region_solution: HashMap<Region, LocationSet>,

    /// Location index used for compact region storage
    pub location_index: LocationIndex,

    /// All loans with their computed live ranges
    pub loans_with_ranges: Vec<LoanWithLiveRange>,

    /// List of runtime checks that codegen must emit
    pub runtime_checks: Vec<RuntimeCheck>,

    /// Borrow check errors (empty if check passed)
    pub errors: Vec<BorrowError>,

    /// Whether the borrow check passed
    pub success: bool,
}

/// Deterministic, ordered borrow-check evidence for artifacts/codegen.
#[derive(Debug, Clone)]
pub struct BorrowCheckEvidence {
    pub regions: Vec<RegionEvidence>,
    pub loans: Vec<LoanEvidence>,
    pub runtime_checks: Vec<RuntimeCheckEvidence>,
}

#[derive(Debug, Clone)]
pub struct RegionEvidence {
    pub region: Region,
    pub live_at: Vec<Location>,
}

#[derive(Debug, Clone)]
pub struct LoanEvidence {
    pub loan: NllLoan,
    pub live_at: Vec<Location>,
}

#[derive(Debug, Clone)]
pub struct RuntimeCheckEvidence {
    pub kind: RuntimeCheckKind,
    pub location: Location,
}

impl BorrowCheckResult {
    /// Returns true if the borrow check passed without errors
    pub fn is_ok(&self) -> bool {
        self.success && self.errors.is_empty()
    }

    /// Get all locations where a specific region is live
    pub fn region_live_at(&self, region: Region) -> Option<&LocationSet> {
        self.region_solution.get(&region)
    }

    /// Check if a region is live at a specific location
    pub fn is_region_live_at(&self, region: Region, location: Location) -> bool {
        if region == Region::STATIC {
            return true;
        }
        self.region_solution
            .get(&region)
            .map(|locs| locs.contains_location(&self.location_index, location))
            .unwrap_or(false)
    }

    /// Get all active loans at a specific location
    pub fn active_loans_at(&self, location: Location) -> Vec<&NllLoan> {
        self.loans_with_ranges
            .iter()
            .filter(|lwr| {
                lwr.live_at
                    .contains_location(&self.location_index, location)
            })
            .map(|lwr| &lwr.loan)
            .collect()
    }

    /// Convert the result into deterministic evidence for artifacts/codegen.
    pub fn evidence(&self) -> BorrowCheckEvidence {
        let mut regions: Vec<RegionEvidence> = self
            .region_solution
            .iter()
            .map(|(region, locs)| {
                let mut live_at: Vec<Location> = locs.to_locations(&self.location_index);
                live_at.sort_by_key(location_key);
                RegionEvidence {
                    region: *region,
                    live_at,
                }
            })
            .collect();
        regions.sort_by_key(|region| region.region.0);

        let mut loans: Vec<LoanEvidence> = self
            .loans_with_ranges
            .iter()
            .map(|lwr| {
                let mut live_at: Vec<Location> = lwr.live_at.to_locations(&self.location_index);
                live_at.sort_by_key(location_key);
                LoanEvidence {
                    loan: lwr.loan.clone(),
                    live_at,
                }
            })
            .collect();
        loans.sort_by(cmp_loans);

        let mut runtime_checks: Vec<RuntimeCheckEvidence> = self
            .runtime_checks
            .iter()
            .map(|check| RuntimeCheckEvidence {
                kind: check.kind.clone(),
                location: check.location,
            })
            .collect();
        runtime_checks.sort_by(|a, b| {
            location_key(&a.location)
                .cmp(&location_key(&b.location))
                .then_with(|| runtime_check_key(&a.kind).cmp(&runtime_check_key(&b.kind)))
        });

        BorrowCheckEvidence {
            regions,
            loans,
            runtime_checks,
        }
    }

    /// Insert runtime check statements into the MIR body.
    pub fn inject_runtime_checks(&self, body: &mut Body) {
        if self.runtime_checks.is_empty() {
            return;
        }

        let mut checks_by_block: HashMap<BasicBlock, Vec<(usize, RuntimeCheckKind)>> =
            HashMap::new();
        for check in &self.runtime_checks {
            checks_by_block
                .entry(check.location.block)
                .or_default()
                .push((check.location.statement_index, check.kind.clone()));
        }

        for (bb_idx, bb_data) in body.basic_blocks.iter_mut().enumerate() {
            let bb = BasicBlock(bb_idx as u32);
            let Some(mut checks) = checks_by_block.remove(&bb) else {
                continue;
            };
            checks.sort_by_key(|(idx, _)| *idx);

            let mut new_statements = Vec::with_capacity(bb_data.statements.len() + checks.len());
            let mut check_iter = checks.into_iter().peekable();

            for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
                while let Some((idx, _)) = check_iter.peek() {
                    if *idx <= stmt_idx {
                        if let Some((_, kind)) = check_iter.next() {
                            new_statements.push(Statement::RuntimeCheck(kind));
                        }
                    } else {
                        break;
                    }
                }
                new_statements.push(stmt.clone());
            }

            for (_idx, kind) in check_iter {
                new_statements.push(Statement::RuntimeCheck(kind));
            }

            bb_data.statements = new_statements;
        }
    }
}

impl BorrowCheckEvidence {
    pub fn render_lines(&self) -> Vec<String> {
        let mut lines = Vec::new();

        lines.push("regions:".to_string());
        if self.regions.is_empty() {
            lines.push("  (none)".to_string());
        } else {
            for region in &self.regions {
                let locs = format_locations(&region.live_at);
                lines.push(format!("  {}: [{}]", format_region(region.region), locs));
            }
        }

        lines.push("loans:".to_string());
        if self.loans.is_empty() {
            lines.push("  (none)".to_string());
        } else {
            for loan in &self.loans {
                let live_at = format_locations(&loan.live_at);
                lines.push(format!(
                    "  - place={} kind={} region={} holder={} issued_at={} live_at=[{}]",
                    format_place(&loan.loan.place),
                    format_borrow_kind(loan.loan.kind),
                    format_region(loan.loan.region),
                    format_local(loan.loan.holder),
                    format_location(&loan.loan.issued_at),
                    live_at
                ));
            }
        }

        lines.push("runtime_checks:".to_string());
        if self.runtime_checks.is_empty() {
            lines.push("  (none)".to_string());
        } else {
            for check in &self.runtime_checks {
                lines.push(format!(
                    "  - at {} {}",
                    format_location(&check.location),
                    format_runtime_check(&check.kind)
                ));
            }
        }

        lines
    }
}

fn location_key(location: &Location) -> (u32, usize) {
    (location.block.0, location.statement_index)
}

fn borrow_kind_key(kind: BorrowKind) -> u8 {
    match kind {
        BorrowKind::Shared => 0,
        BorrowKind::Mut => 1,
    }
}

fn runtime_check_key(kind: &RuntimeCheckKind) -> (u8, u32, u32) {
    match kind {
        RuntimeCheckKind::RefCellBorrow { local } => (0, local.0, 0),
        RuntimeCheckKind::MutexLock { local } => (1, local.0, 0),
        RuntimeCheckKind::BoundsCheck { local, index } => (2, local.0, index.0),
    }
}

fn cmp_loans(a: &LoanEvidence, b: &LoanEvidence) -> Ordering {
    location_key(&a.loan.issued_at)
        .cmp(&location_key(&b.loan.issued_at))
        .then_with(|| a.loan.holder.0.cmp(&b.loan.holder.0))
        .then_with(|| a.loan.region.0.cmp(&b.loan.region.0))
        .then_with(|| borrow_kind_key(a.loan.kind).cmp(&borrow_kind_key(b.loan.kind)))
        .then_with(|| cmp_place(&a.loan.place, &b.loan.place))
}

fn cmp_place(a: &Place, b: &Place) -> Ordering {
    a.local
        .0
        .cmp(&b.local.0)
        .then_with(|| cmp_projection(&a.projection, &b.projection))
}

fn cmp_projection(a: &[PlaceElem], b: &[PlaceElem]) -> Ordering {
    for (lhs, rhs) in a.iter().zip(b.iter()) {
        let ord = cmp_place_elem(lhs, rhs);
        if ord != Ordering::Equal {
            return ord;
        }
    }
    a.len().cmp(&b.len())
}

fn cmp_place_elem(a: &PlaceElem, b: &PlaceElem) -> Ordering {
    let tag = |elem: &PlaceElem| match elem {
        PlaceElem::Deref => 0,
        PlaceElem::Field(_) => 1,
        PlaceElem::Downcast(_) => 2,
        PlaceElem::Index(_) => 3,
    };
    let a_tag = tag(a);
    let b_tag = tag(b);
    if a_tag != b_tag {
        return a_tag.cmp(&b_tag);
    }
    match (a, b) {
        (PlaceElem::Field(a_idx), PlaceElem::Field(b_idx)) => a_idx.cmp(b_idx),
        (PlaceElem::Downcast(a_idx), PlaceElem::Downcast(b_idx)) => a_idx.cmp(b_idx),
        (PlaceElem::Index(a_local), PlaceElem::Index(b_local)) => a_local.0.cmp(&b_local.0),
        _ => Ordering::Equal,
    }
}

fn format_region(region: Region) -> String {
    format!("'{}", region.0)
}

fn format_location(location: &Location) -> String {
    format!("bb{}:{}", location.block.0, location.statement_index)
}

fn format_local(local: Local) -> String {
    format!("_{}", local.0)
}

fn format_borrow_kind(kind: BorrowKind) -> &'static str {
    match kind {
        BorrowKind::Shared => "Shared",
        BorrowKind::Mut => "Mut",
    }
}

fn format_locations(locations: &[Location]) -> String {
    locations
        .iter()
        .map(format_location)
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_place(place: &Place) -> String {
    let mut s = format_local(place.local);
    for elem in &place.projection {
        match elem {
            PlaceElem::Deref => s = format!("(*{})", s),
            PlaceElem::Field(i) => s = format!("{}.{}", s, i),
            PlaceElem::Downcast(i) => s = format!("({} as variant#{})", s, i),
            PlaceElem::Index(local) => s = format!("{}[{}]", s, format_local(*local)),
        }
    }
    s
}

fn format_runtime_check(kind: &RuntimeCheckKind) -> String {
    match kind {
        RuntimeCheckKind::RefCellBorrow { local } => {
            format!("RefCellBorrow({})", format_local(*local))
        }
        RuntimeCheckKind::MutexLock { local } => format!("MutexLock({})", format_local(*local)),
        RuntimeCheckKind::BoundsCheck { local, index } => format!(
            "BoundsCheck({}, {})",
            format_local(*local),
            format_local(*index)
        ),
    }
}

pub struct RegionInferenceContext {
    pub num_regions: usize,
    pub constraints: HashSet<Constraint>,
    /// Points where a region is required to be live
    pub liveness_constraints: HashMap<Region, LocationSet>,
    pub region_values: HashMap<Region, LocationSet>,
    pub location_index: LocationIndex,
}

impl RegionInferenceContext {
    pub fn new(body: &Body) -> Self {
        Self {
            num_regions: 1, // 0 is STATIC
            constraints: HashSet::new(),
            liveness_constraints: HashMap::new(),
            region_values: HashMap::new(),
            location_index: LocationIndex::new(body),
        }
    }

    pub fn add_constraint(&mut self, sup: Region, sub: Region) {
        if sup == sub {
            return;
        }
        if sup == Region::STATIC {
            return;
        } // Static outlives everything
        self.constraints.insert(Constraint::Outlives(sup, sub));
    }

    pub fn add_liveness(&mut self, region: Region, location: Location) {
        if region == Region::STATIC {
            return;
        }
        let set = self
            .liveness_constraints
            .entry(region)
            .or_insert_with(|| LocationSet::new(self.location_index.len()));
        set.insert_location(&self.location_index, location);
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
                let sub_locs = self.region_values.get(&sub).cloned();
                let Some(sub_locs) = sub_locs else {
                    continue;
                };
                let sup_locs = self
                    .region_values
                    .entry(sup)
                    .or_insert_with(|| LocationSet::new(self.location_index.len()));
                if sup_locs.union_with(&sub_locs) {
                    changed = true;
                }
            }
        }
    }

    pub fn is_region_live_at(&self, region: Region, location: Location) -> bool {
        if region == Region::STATIC {
            return true;
        }
        self.region_values
            .get(&region)
            .map(|locs| locs.contains_location(&self.location_index, location))
            .unwrap_or(false)
    }

    fn region_has_direct_liveness(&self, region: Region, location: Location) -> bool {
        self.liveness_constraints
            .get(&region)
            .map(|locs| locs.contains_location(&self.location_index, location))
            .unwrap_or(false)
    }

    pub fn explain_region_live_at(
        &self,
        region: Region,
        location: Location,
    ) -> Option<RegionConstraintChain> {
        let live_at = MirSpan {
            block: location.block,
            statement_index: location.statement_index,
        };

        if region == Region::STATIC {
            return Some(RegionConstraintChain {
                chain: vec![Region::STATIC],
                live_at,
            });
        }

        if self.region_has_direct_liveness(region, location) {
            return Some(RegionConstraintChain {
                chain: vec![region],
                live_at,
            });
        }

        let mut constraints: Vec<(Region, Region)> = self
            .constraints
            .iter()
            .map(|constraint| match constraint {
                Constraint::Outlives(sup, sub) => (*sup, *sub),
            })
            .collect();
        constraints.sort_by_key(|(sup, sub)| (sup.0, sub.0));

        let mut queue = std::collections::VecDeque::new();
        let mut visited: HashSet<Region> = HashSet::new();
        let mut prev: HashMap<Region, Region> = HashMap::new();

        queue.push_back(region);
        visited.insert(region);

        let mut root: Option<Region> = None;
        while let Some(current) = queue.pop_front() {
            if self.region_has_direct_liveness(current, location) {
                root = Some(current);
                break;
            }
            for (_sup, sub) in constraints.iter().filter(|(sup, _)| *sup == current) {
                if visited.insert(*sub) {
                    prev.insert(*sub, current);
                    queue.push_back(*sub);
                }
            }
        }

        let root = root?;
        let mut chain = vec![root];
        let mut cursor = root;
        while cursor != region {
            let parent = prev.get(&cursor).copied()?;
            chain.push(parent);
            cursor = parent;
        }
        chain.reverse();

        Some(RegionConstraintChain { chain, live_at })
    }
}

pub struct NllChecker<'a> {
    pub body: &'a Body,
    pub context: RegionInferenceContext,
    pub local_types: HashMap<Local, MirType>,
    local_capture_types: HashMap<Local, Vec<MirType>>,
    region_map: HashMap<Region, Region>,
    synthetic_borrow_regions: HashMap<Local, Region>,
    index_constants: Vec<Option<u64>>,
    pub loans: Vec<NllLoan>,
    pub errors: Vec<BorrowError>,
}

impl<'a> NllChecker<'a> {
    pub fn new(body: &'a Body) -> Self {
        let mut checker = NllChecker {
            body,
            context: RegionInferenceContext::new(body),
            local_types: HashMap::new(),
            local_capture_types: HashMap::new(),
            region_map: HashMap::new(),
            synthetic_borrow_regions: HashMap::new(),
            index_constants: Vec::new(),
            loans: Vec::new(),
            errors: Vec::new(),
        };
        checker.instantiate_local_types();
        checker.index_constants = checker.compute_index_constants();
        checker
    }

    pub fn check(&mut self) {
        self.propagate_closure_captures();
        self.assign_synthetic_borrow_regions();
        self.check_with_assigned_regions();
    }

    fn check_with_assigned_regions(&mut self) {
        // 1. Compute Liveness (ignoring regions for now, just locals)
        let liveness = compute_liveness(self.body);
        let mut precise_liveness: HashMap<Location, LocalSet> = HashMap::new();

        // 2. Compute Precise Liveness (Backward per block)
        for (bb_idx, bb_data) in self.body.basic_blocks.iter().enumerate() {
            let bb = BasicBlock(bb_idx as u32);
            let Some(out_live) = liveness.out_set(bb) else {
                continue;
            };
            let mut live = out_live.clone();

            // Terminator
            let term_loc = Location {
                block: bb,
                statement_index: bb_data.statements.len(),
            };
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
                let loc = Location {
                    block: bb,
                    statement_index: stmt_idx,
                };
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
                let loc = Location {
                    block: bb,
                    statement_index: stmt_idx,
                };
                if let Statement::Assign(dest, rvalue) = stmt {
                    let dest_ty = self.place_type(dest);

                    if let Rvalue::Ref(kind, place) = rvalue {
                        if let Some(region) =
                            self.borrow_region_for_ref_assignment(dest, &dest_ty, loc)
                        {
                            self.loans.push(NllLoan {
                                place: place.clone(),
                                region,
                                kind: *kind,
                                issued_at: loc,
                                holder: dest.local,
                            });
                        }
                    }

                    let rvalue_ty = self.rvalue_type(rvalue, &dest_ty);
                    self.relate_types(&dest_ty, &rvalue_ty);
                }
            }

            if let Some(Terminator::Call {
                func,
                args,
                destination,
                ..
            }) = &bb_data.terminator
            {
                let term_loc = Location {
                    block: bb,
                    statement_index: bb_data.statements.len(),
                };
                self.relate_call_types(func, args, destination, term_loc);
            }
        }

        // 5. Solve
        self.context.solve(self.body);

        // 6. Check Conflicts
        self.check_conflicts();
    }

    fn check_conflicts(&mut self) {
        let mut dangling_reported: HashSet<(BasicBlock, Local)> = HashSet::new();
        for (bb_idx, bb_data) in self.body.basic_blocks.iter().enumerate() {
            let bb = BasicBlock(bb_idx as u32);
            for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
                let loc = Location {
                    block: bb,
                    statement_index: stmt_idx,
                };
                match stmt {
                    Statement::Assign(dest, rvalue) => {
                        // Check mutation of dest
                        self.check_access(dest, AccessKind::Write, loc);
                        // Check read of rvalue
                        self.check_rvalue_access(rvalue, loc);
                    }
                    Statement::StorageDead(local) => {
                        // Check if *local is borrowed?
                        // If local is invalidated, loans of it must be dead.
                        // We check if any loan of `local` is active.
                        for loan in &self.loans {
                            if loan.place.local == *local
                                && self.context.is_region_live_at(loan.region, loc)
                            {
                                self.errors.push(BorrowError::DanglingReference {
                                    borrowed_local: *local,
                                    location: Some(MirSpan {
                                        block: loc.block,
                                        statement_index: loc.statement_index,
                                    }),
                                    context: self.borrow_error_context(loan, loc),
                                });
                                dangling_reported.insert((bb, *local));
                                break;
                            }
                        }
                    }
                    _ => {}
                }
            }
            if let Some(term) = &bb_data.terminator {
                let loc = Location {
                    block: bb,
                    statement_index: bb_data.statements.len(),
                };
                match term {
                    Terminator::Call {
                        func,
                        args,
                        destination,
                        ..
                    } => {
                        self.check_call_operand_access(func, loc);
                        for arg in args {
                            self.check_operand_access(arg, loc);
                        }
                        self.check_access(destination, AccessKind::Write, loc);
                        if let CallOperand::Borrow(kind, place) = func {
                            for arg in args {
                                self.check_call_borrow_operand_conflict(*kind, place, arg, loc);
                            }
                            self.check_call_borrow_access_conflict(
                                *kind,
                                place,
                                AccessKind::Write,
                                destination,
                                loc,
                            );
                        }
                    }
                    Terminator::SwitchInt { discr, .. } => self.check_operand_access(discr, loc),
                    Terminator::Return => {
                        let span = Some(MirSpan {
                            block: loc.block,
                            statement_index: loc.statement_index,
                        });
                        for loan in &self.loans {
                            if !self.context.is_region_live_at(loan.region, loc) {
                                continue;
                            }
                            if dangling_reported.contains(&(bb, loan.place.local)) {
                                continue;
                            }
                            self.errors.push(BorrowError::EscapingReference {
                                place: loan.place.clone(),
                                location: span,
                                context: self.borrow_error_context(loan, loc),
                            });
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    fn borrow_region_for_ref_assignment(
        &mut self,
        dest: &Place,
        dest_ty: &MirType,
        loc: Location,
    ) -> Option<Region> {
        if let MirType::Ref(region, _, _) = dest_ty {
            return Some(*region);
        }
        if let Some(region) = self.synthetic_borrow_regions.get(&dest.local).copied() {
            return Some(region);
        }
        self.errors.push(BorrowError::InternalInvariant {
            invariant: "synthetic borrow region exists for reference assignment destination",
            evidence: format!(
                "destination local _{} has type {:?} but no synthetic borrow region mapping",
                dest.local.0, dest_ty
            ),
            location: Some(MirSpan {
                block: loc.block,
                statement_index: loc.statement_index,
            }),
            context: BorrowErrorContext::default(),
        });
        None
    }

    fn borrow_error_context(&self, loan: &NllLoan, loc: Location) -> BorrowErrorContext {
        let loan_context = BorrowLoanContext {
            place: loan.place.clone(),
            kind: loan.kind,
            region: loan.region,
            issued_at: MirSpan {
                block: loan.issued_at.block,
                statement_index: loan.issued_at.statement_index,
            },
            holder: loan.holder,
        };
        let region_context = self.context.explain_region_live_at(loan.region, loc);
        BorrowErrorContext {
            loan: Some(loan_context),
            region: region_context,
        }
    }

    fn check_access(&mut self, place: &Place, access: AccessKind, loc: Location) {
        for loan in &self.loans {
            // Is loan active?
            if self.context.is_region_live_at(loan.region, loc) {
                // Is place conflicting?
                if self.places_conflict_at(loan, place, loc) {
                    match access {
                        AccessKind::Read => {
                            if loan.kind == BorrowKind::Shared {
                                continue;
                            }
                            self.errors.push(BorrowError::UseWhileBorrowed {
                                place: place.clone(),
                                borrow_kind: loan.kind,
                                location: Some(MirSpan {
                                    block: loc.block,
                                    statement_index: loc.statement_index,
                                }),
                                context: self.borrow_error_context(loan, loc),
                            });
                            break;
                        }
                        AccessKind::Write => {
                            self.errors.push(BorrowError::AssignWhileBorrowed {
                                place: place.clone(),
                                location: Some(MirSpan {
                                    block: loc.block,
                                    statement_index: loc.statement_index,
                                }),
                                context: self.borrow_error_context(loan, loc),
                            });
                            break;
                        }
                        AccessKind::Borrow(requested) => {
                            if requested == BorrowKind::Shared && loan.kind == BorrowKind::Shared {
                                continue;
                            }
                            self.errors.push(BorrowError::ConflictingBorrow {
                                place: place.clone(),
                                existing_kind: loan.kind,
                                requested_kind: requested,
                                location: Some(MirSpan {
                                    block: loc.block,
                                    statement_index: loc.statement_index,
                                }),
                                context: self.borrow_error_context(loan, loc),
                            });
                            break;
                        }
                    }
                }
            }
        }
    }

    fn check_rvalue_access(&mut self, rvalue: &Rvalue, loc: Location) {
        match rvalue {
            Rvalue::Use(op) => self.check_operand_access(op, loc),
            Rvalue::Ref(kind, p) => {
                self.check_access(p, AccessKind::Borrow(*kind), loc);
            }
            _ => {}
        }
    }

    fn check_operand_access(&mut self, op: &Operand, loc: Location) {
        match op {
            Operand::Copy(p) | Operand::Move(p) => self.check_access(p, AccessKind::Read, loc),
            Operand::Constant(c) => {
                if let Some(captures) = c.literal.capture_operands() {
                    for cap in captures {
                        self.check_operand_access(cap, loc);
                    }
                }
            }
        }
    }

    fn check_call_operand_access(&mut self, op: &CallOperand, loc: Location) {
        match op {
            CallOperand::Borrow(kind, place) => {
                self.check_access(place, AccessKind::Borrow(*kind), loc);
            }
            CallOperand::Operand(op) => self.check_operand_access(op, loc),
        }
    }

    fn check_call_borrow_operand_conflict(
        &mut self,
        kind: BorrowKind,
        borrowed: &Place,
        operand: &Operand,
        loc: Location,
    ) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.check_call_borrow_access_conflict(
                    kind,
                    borrowed,
                    AccessKind::Read,
                    place,
                    loc,
                );
            }
            Operand::Constant(c) => {
                if let Some(captures) = c.literal.capture_operands() {
                    for cap in captures {
                        self.check_call_borrow_operand_conflict(kind, borrowed, cap, loc);
                    }
                }
            }
        }
    }

    fn check_call_borrow_access_conflict(
        &mut self,
        kind: BorrowKind,
        borrowed: &Place,
        access: AccessKind,
        place: &Place,
        loc: Location,
    ) {
        if !places_conflict_base(borrowed, place, &self.index_constants) {
            return;
        }
        let span = Some(MirSpan {
            block: loc.block,
            statement_index: loc.statement_index,
        });
        match access {
            AccessKind::Read => {
                if kind == BorrowKind::Mut {
                    self.errors.push(BorrowError::UseWhileBorrowed {
                        place: place.clone(),
                        borrow_kind: kind,
                        location: span,
                        context: BorrowErrorContext::default(),
                    });
                }
            }
            AccessKind::Write => {
                self.errors.push(BorrowError::AssignWhileBorrowed {
                    place: place.clone(),
                    location: span,
                    context: BorrowErrorContext::default(),
                });
            }
            AccessKind::Borrow(requested) => {
                if requested == BorrowKind::Shared && kind == BorrowKind::Shared {
                    return;
                }
                self.errors.push(BorrowError::ConflictingBorrow {
                    place: place.clone(),
                    existing_kind: kind,
                    requested_kind: requested,
                    location: span,
                    context: BorrowErrorContext::default(),
                });
            }
        }
    }

    fn places_conflict_at(&self, loan: &NllLoan, place: &Place, loc: Location) -> bool {
        let access_places = self.resolve_place_at(place, loc);
        let loan_places = self.resolve_place_at(&loan.place, loc);

        for access in &access_places {
            for loan_place in &loan_places {
                if !places_conflict_base(&access.place, &loan_place.place, &self.index_constants) {
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
                    if loan.holder == current.local
                        && self.context.is_region_live_at(loan.region, loc)
                    {
                        let mut new_proj = loan.place.projection.clone();
                        new_proj.extend_from_slice(tail);
                        let new_place = Place {
                            local: loan.place.local,
                            projection: new_proj,
                        };
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

            results.push(ResolvedPlace {
                place: current,
                origin_chain,
            });
        }

        results
    }

    fn record_region_liveness(&mut self, live_locals: &LocalSet, loc: Location) {
        for local in live_locals.iter() {
            if let Some(ty) = self.local_types.get(&local) {
                Self::add_type_regions_live(&mut self.context, ty, loc);
            }
            if let Some(captures) = self.local_capture_types.get(&local) {
                for cap_ty in captures {
                    Self::add_type_regions_live(&mut self.context, cap_ty, loc);
                }
            }
            if let Some(region) = self.synthetic_borrow_regions.get(&local) {
                self.context.add_liveness(*region, loc);
            }
        }
    }

    fn add_type_regions_live(context: &mut RegionInferenceContext, ty: &MirType, loc: Location) {
        match ty {
            MirType::Ref(r, inner, _) => {
                context.add_liveness(*r, loc);
                Self::add_type_regions_live(context, inner, loc);
            }
            MirType::Adt(_, args) => {
                for arg in args {
                    Self::add_type_regions_live(context, arg, loc);
                }
            }
            MirType::InteriorMutable(inner, _) => Self::add_type_regions_live(context, inner, loc),
            _ => {}
        }
    }

    fn place_type(&self, place: &Place) -> MirType {
        let mut ty = self.local_types[&place.local].clone();
        let mut active_variant: Option<usize> = None;
        let mut projections = place.projection.iter().peekable();

        if let Some(PlaceElem::Field(idx)) = projections.peek() {
            if let Some(captures) = self.local_capture_types.get(&place.local) {
                if let Some(field_ty) = captures.get(*idx) {
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

    fn rvalue_type(&self, rvalue: &Rvalue, dest_ty: &MirType) -> MirType {
        match rvalue {
            Rvalue::Use(op) => self.operand_type(op),
            Rvalue::Ref(kind, place) => {
                let place_ty = self.place_type(place);
                if let MirType::Ref(region, _, _) = dest_ty {
                    MirType::Ref(*region, Box::new(place_ty), (*kind).into())
                } else {
                    dest_ty.clone()
                }
            }
            _ => MirType::Unit,
        }
    }

    fn operand_type(&self, op: &Operand) -> MirType {
        match op {
            Operand::Copy(p) | Operand::Move(p) => self.place_type(p),
            Operand::Constant(c) => c.ty.clone(),
        }
    }

    fn call_operand_type(&mut self, op: &CallOperand) -> MirType {
        match op {
            CallOperand::Operand(op) => self.operand_type(op),
            CallOperand::Borrow(_, place) => {
                let place_ty = self.place_type(place);
                match place_ty {
                    MirType::Closure(kind, _self_region, region_params, args, ret) => {
                        let borrow_region = self.next_region();
                        MirType::Closure(kind, borrow_region, region_params, args, ret)
                    }
                    _ => place_ty,
                }
            }
        }
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

    fn substitute_regions(ty: &MirType, map: &HashMap<Region, Region>) -> MirType {
        match ty {
            MirType::Ref(region, inner, mutability) => {
                let region = map.get(region).copied().unwrap_or(*region);
                let inner_renumbered = Self::substitute_regions(inner, map);
                MirType::Ref(region, Box::new(inner_renumbered), *mutability)
            }
            MirType::Adt(id, args) => {
                let new_args = args
                    .iter()
                    .map(|a| Self::substitute_regions(a, map))
                    .collect();
                MirType::Adt(id.clone(), new_args)
            }
            MirType::Fn(kind, region_params, args, ret) => {
                let new_region_params = region_params
                    .iter()
                    .map(|region| map.get(region).copied().unwrap_or(*region))
                    .collect();
                let new_args = args
                    .iter()
                    .map(|a| Self::substitute_regions(a, map))
                    .collect();
                let new_ret = Self::substitute_regions(ret, map);
                MirType::Fn(*kind, new_region_params, new_args, Box::new(new_ret))
            }
            MirType::FnItem(def_id, kind, region_params, args, ret) => {
                let new_region_params = region_params
                    .iter()
                    .map(|region| map.get(region).copied().unwrap_or(*region))
                    .collect();
                let new_args = args
                    .iter()
                    .map(|a| Self::substitute_regions(a, map))
                    .collect();
                let new_ret = Self::substitute_regions(ret, map);
                MirType::FnItem(
                    *def_id,
                    *kind,
                    new_region_params,
                    new_args,
                    Box::new(new_ret),
                )
            }
            MirType::Closure(kind, self_region, region_params, args, ret) => {
                let new_self_region = map.get(self_region).copied().unwrap_or(*self_region);
                let new_region_params = region_params
                    .iter()
                    .map(|region| map.get(region).copied().unwrap_or(*region))
                    .collect();
                let new_args = args
                    .iter()
                    .map(|a| Self::substitute_regions(a, map))
                    .collect();
                let new_ret = Self::substitute_regions(ret, map);
                MirType::Closure(
                    *kind,
                    new_self_region,
                    new_region_params,
                    new_args,
                    Box::new(new_ret),
                )
            }
            MirType::RawPtr(inner, mutability) => {
                MirType::RawPtr(Box::new(Self::substitute_regions(inner, map)), *mutability)
            }
            MirType::InteriorMutable(inner, kind) => {
                MirType::InteriorMutable(Box::new(Self::substitute_regions(inner, map)), *kind)
            }
            _ => ty.clone(),
        }
    }

    fn relate_call_types(
        &mut self,
        func: &CallOperand,
        args: &[Operand],
        destination: &Place,
        loc: Location,
    ) {
        let raw_func_ty = self.call_operand_type(func);
        let func_ty = self.normalize_callable_type(&raw_func_ty);
        match func_ty {
            MirType::Fn(_, region_params, param_tys, ret_ty) => {
                let mut param_tys = param_tys;
                let mut ret_ty = *ret_ty;
                if !region_params.is_empty() {
                    let subst = self.instantiate_region_params(&region_params);
                    param_tys = param_tys
                        .iter()
                        .map(|ty| Self::substitute_regions(ty, &subst))
                        .collect();
                    ret_ty = Self::substitute_regions(&ret_ty, &subst);
                }
                for (arg, param_ty) in args.iter().zip(param_tys.iter()) {
                    let arg_ty = self.operand_type(arg);
                    self.relate_types(param_ty, &arg_ty);
                }
                let dest_ty = self.place_type(destination);
                self.relate_types(&dest_ty, &ret_ty);
            }
            MirType::Closure(_kind, self_region, region_params, param_tys, ret_ty) => {
                let mut param_tys = param_tys;
                let mut ret_ty = *ret_ty;
                if !region_params.is_empty() {
                    let subst = self.instantiate_region_params(&region_params);
                    param_tys = param_tys
                        .iter()
                        .map(|ty| Self::substitute_regions(ty, &subst))
                        .collect();
                    ret_ty = Self::substitute_regions(&ret_ty, &subst);
                }
                for (arg, param_ty) in args.iter().zip(param_tys.iter()) {
                    let arg_ty = self.operand_type(arg);
                    self.relate_types(param_ty, &arg_ty);
                }
                let dest_ty = self.place_type(destination);
                self.relate_types(&dest_ty, &ret_ty);

                if let CallOperand::Borrow(borrow_kind, place) = func {
                    let mut ref_regions = Vec::new();
                    Self::collect_ref_regions(&ret_ty, &mut ref_regions);
                    ref_regions.sort_by_key(|r| r.0);
                    ref_regions.dedup();
                    ref_regions.retain(|region| *region != Region::STATIC);
                    if !ref_regions.is_empty() {
                        for region in ref_regions {
                            self.context.add_constraint(self_region, region);
                        }
                        self.loans.push(NllLoan {
                            place: place.clone(),
                            region: self_region,
                            kind: *borrow_kind,
                            issued_at: loc,
                            holder: destination.local,
                        });
                    }
                }
            }
            _ => {}
        }
    }

    fn normalize_callable_type(&self, ty: &MirType) -> MirType {
        match ty {
            MirType::Fn(_, _, _, _) => ty.clone(),
            MirType::FnItem(_id, kind, regions, args, ret) => {
                MirType::Fn(*kind, regions.clone(), args.clone(), ret.clone())
            }
            MirType::Closure(_, _, _, _, _) => ty.clone(),
            _ => ty.clone(),
        }
    }

    fn collect_ref_regions(ty: &MirType, out: &mut Vec<Region>) {
        match ty {
            MirType::Ref(region, inner, _) => {
                out.push(*region);
                Self::collect_ref_regions(inner, out);
            }
            MirType::Adt(_, args) => {
                for arg in args {
                    Self::collect_ref_regions(arg, out);
                }
            }
            MirType::InteriorMutable(inner, _) => Self::collect_ref_regions(inner, out),
            MirType::RawPtr(inner, _) => Self::collect_ref_regions(inner, out),
            _ => {}
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
            }
            (MirType::Adt(id1, args1), MirType::Adt(id2, args2)) => {
                if id1 != id2 || args1.len() != args2.len() {
                    return;
                }
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    match (a1, a2) {
                        (MirType::IndexTerm(t1), MirType::IndexTerm(t2)) => {
                            if t1 != t2 {
                                return;
                            }
                        }
                        (MirType::IndexTerm(_), _) | (_, MirType::IndexTerm(_)) => {
                            return;
                        }
                        _ => {}
                    }
                }
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    self.relate_types(a1, a2);
                }
            }
            _ => {}
        }
    }

    fn instantiate_local_types(&mut self) {
        for (i, decl) in self.body.local_decls.iter().enumerate() {
            let local = Local(i as u32);
            let ty = self.renumber_regions(&decl.ty);
            self.local_types.insert(local, ty);
            if !decl.closure_captures.is_empty() {
                let captures: Vec<MirType> = decl
                    .closure_captures
                    .iter()
                    .map(|ty| self.renumber_regions(ty))
                    .collect();
                self.local_capture_types.insert(local, captures);
            }
        }
    }

    fn compute_index_constants(&self) -> Vec<Option<u64>> {
        let local_count = self.body.local_decls.len();
        let mut assignment_counts = vec![0usize; local_count];
        let mut values: Vec<Option<u64>> = vec![None; local_count];
        let mut invalid = vec![false; local_count];

        for bb in &self.body.basic_blocks {
            for stmt in &bb.statements {
                let Statement::Assign(dest, rvalue) = stmt else {
                    continue;
                };
                if !dest.projection.is_empty() {
                    continue;
                }
                let idx = dest.local.0 as usize;
                if idx >= local_count {
                    continue;
                }
                assignment_counts[idx] += 1;
                match rvalue {
                    Rvalue::Use(Operand::Constant(c)) => {
                        if let Literal::Nat(n) = &c.literal {
                            match values[idx] {
                                None => values[idx] = Some(*n),
                                Some(existing) => {
                                    if existing != *n {
                                        invalid[idx] = true;
                                    }
                                }
                            }
                        } else {
                            invalid[idx] = true;
                        }
                    }
                    _ => {
                        invalid[idx] = true;
                    }
                }
            }

            if let Some(Terminator::Call { destination, .. }) = &bb.terminator {
                if destination.projection.is_empty() {
                    let idx = destination.local.0 as usize;
                    if idx < local_count {
                        assignment_counts[idx] += 1;
                        invalid[idx] = true;
                    }
                }
            }
        }

        let mut result = vec![None; local_count];
        for idx in 0..local_count {
            if assignment_counts[idx] == 1 && !invalid[idx] {
                result[idx] = values[idx];
            }
        }
        result
    }

    fn propagate_closure_captures(&mut self) {
        let mut changed = true;
        while changed {
            changed = false;
            for bb in &self.body.basic_blocks {
                for stmt in &bb.statements {
                    let Statement::Assign(dest, rvalue) = stmt else {
                        continue;
                    };
                    if self.place_has_deref(dest) {
                        continue;
                    }
                    let Some(captures) = self.captures_from_rvalue(rvalue) else {
                        continue;
                    };
                    if self.union_capture_types(dest.local, captures) {
                        changed = true;
                    }
                }
            }
        }
    }

    fn captures_from_rvalue(&self, rvalue: &Rvalue) -> Option<Vec<MirType>> {
        let Rvalue::Use(op) = rvalue else {
            return None;
        };
        match op {
            Operand::Constant(c) => {
                c.literal.capture_operands()?;
                let mut captures = Vec::new();
                self.collect_capture_payload_types(op, &mut captures);
                if captures.is_empty() {
                    None
                } else {
                    Some(captures)
                }
            }
            Operand::Copy(place) | Operand::Move(place) => self.capture_types_for_place(place),
        }
    }

    fn collect_capture_payload_types(&self, op: &Operand, out: &mut Vec<MirType>) {
        if let Operand::Copy(place) | Operand::Move(place) = op {
            if let Some(captures) = self.capture_types_for_place(place) {
                out.extend(captures);
            }
        }

        if let Operand::Constant(c) = op {
            if let Some(captures) = c.literal.capture_operands() {
                for capture in captures {
                    self.collect_capture_payload_types(capture, out);
                }
                return;
            }
        }

        out.push(self.operand_type(op));
    }

    fn capture_types_for_place(&self, place: &Place) -> Option<Vec<MirType>> {
        if self.place_has_deref(place) {
            return None;
        }
        if place.projection.is_empty() {
            return self.local_capture_types.get(&place.local).cloned();
        }
        self.local_capture_types.get(&place.local).cloned()
    }

    fn place_has_deref(&self, place: &Place) -> bool {
        place
            .projection
            .iter()
            .any(|elem| matches!(elem, PlaceElem::Deref))
    }

    fn union_capture_types(&mut self, local: Local, captures: Vec<MirType>) -> bool {
        if captures.is_empty() {
            return false;
        }
        let entry = self.local_capture_types.entry(local).or_default();
        let mut changed = false;
        for ty in captures {
            if !entry.contains(&ty) {
                entry.push(ty);
                changed = true;
            }
        }
        changed
    }

    fn renumber_region(&mut self, region: Region) -> Region {
        if region == Region::STATIC {
            return Region::STATIC;
        }
        if let Some(existing) = self.region_map.get(&region) {
            return *existing;
        }
        let fresh = self.next_region();
        self.region_map.insert(region, fresh);
        fresh
    }

    fn renumber_regions(&mut self, ty: &MirType) -> MirType {
        match ty {
            MirType::Ref(region, inner, mutability) => {
                let region = self.renumber_region(*region);
                let inner_renumbered = self.renumber_regions(inner);
                MirType::Ref(region, Box::new(inner_renumbered), *mutability)
            }
            MirType::Adt(id, args) => {
                let new_args = args.iter().map(|a| self.renumber_regions(a)).collect();
                MirType::Adt(id.clone(), new_args)
            }
            MirType::Fn(kind, region_params, args, ret) => {
                let new_region_params = region_params
                    .iter()
                    .map(|region| self.renumber_region(*region))
                    .collect();
                let new_args = args.iter().map(|a| self.renumber_regions(a)).collect();
                let new_ret = self.renumber_regions(ret);
                MirType::Fn(*kind, new_region_params, new_args, Box::new(new_ret))
            }
            MirType::FnItem(def_id, kind, region_params, args, ret) => {
                let new_region_params = region_params
                    .iter()
                    .map(|region| self.renumber_region(*region))
                    .collect();
                let new_args = args.iter().map(|a| self.renumber_regions(a)).collect();
                let new_ret = self.renumber_regions(ret);
                MirType::FnItem(
                    *def_id,
                    *kind,
                    new_region_params,
                    new_args,
                    Box::new(new_ret),
                )
            }
            MirType::Closure(kind, self_region, region_params, args, ret) => {
                let new_self_region = self.renumber_region(*self_region);
                let new_region_params = region_params
                    .iter()
                    .map(|region| self.renumber_region(*region))
                    .collect();
                let new_args = args.iter().map(|a| self.renumber_regions(a)).collect();
                let new_ret = self.renumber_regions(ret);
                MirType::Closure(
                    *kind,
                    new_self_region,
                    new_region_params,
                    new_args,
                    Box::new(new_ret),
                )
            }
            MirType::RawPtr(inner, mutability) => {
                MirType::RawPtr(Box::new(self.renumber_regions(inner)), *mutability)
            }
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

    fn assign_synthetic_borrow_regions(&mut self) {
        for bb in &self.body.basic_blocks {
            for stmt in &bb.statements {
                let Statement::Assign(dest, rvalue) = stmt else {
                    continue;
                };
                if !matches!(rvalue, Rvalue::Ref(_, _)) {
                    continue;
                }

                let dest_ty = self.place_type(dest);
                if matches!(dest_ty, MirType::Ref(_, _, _)) {
                    continue;
                }

                if let std::collections::hash_map::Entry::Vacant(entry) =
                    self.synthetic_borrow_regions.entry(dest.local)
                {
                    let region = Region(self.context.num_regions);
                    self.context.num_regions += 1;
                    entry.insert(region);
                }
            }
        }
    }

    /// Collect runtime checks needed for interior mutability constructs
    fn collect_runtime_checks(&self) -> Vec<RuntimeCheck> {
        let mut checks = Vec::new();

        for (i, decl) in self.body.local_decls.iter().enumerate() {
            self.collect_runtime_checks_for_type(&decl.ty, Local(i as u32), &mut checks);
        }

        self.collect_runtime_checks_for_borrows(&mut checks);

        checks.sort_by(|a, b| {
            location_key(&a.location)
                .cmp(&location_key(&b.location))
                .then_with(|| runtime_check_key(&a.kind).cmp(&runtime_check_key(&b.kind)))
        });
        checks.dedup_by(|a, b| {
            a.location == b.location && runtime_check_key(&a.kind) == runtime_check_key(&b.kind)
        });

        checks
    }

    fn collect_runtime_checks_for_type(
        &self,
        ty: &MirType,
        local: Local,
        checks: &mut Vec<RuntimeCheck>,
    ) {
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
                            let location =
                                Location::new(BasicBlock(bb_idx as u32), bb_data.statements.len());
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

    fn collect_runtime_checks_for_borrows(&self, checks: &mut Vec<RuntimeCheck>) {
        for (bb_idx, bb_data) in self.body.basic_blocks.iter().enumerate() {
            let bb = BasicBlock(bb_idx as u32);
            for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
                let Statement::Assign(_, Rvalue::Ref(_, place)) = stmt else {
                    continue;
                };
                let location = Location::new(bb, stmt_idx);
                let place_ty = self.place_type(place);
                Self::collect_runtime_checks_for_type_at_location(
                    &place_ty,
                    place.local,
                    location,
                    checks,
                );
            }
        }
    }

    fn collect_runtime_checks_for_type_at_location(
        ty: &MirType,
        local: Local,
        location: Location,
        checks: &mut Vec<RuntimeCheck>,
    ) {
        match ty {
            MirType::InteriorMutable(inner, kind) => {
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
                Self::collect_runtime_checks_for_type_at_location(inner, local, location, checks);
            }
            MirType::Ref(_, inner, _) => {
                Self::collect_runtime_checks_for_type_at_location(inner, local, location, checks);
            }
            MirType::Adt(_, args) => {
                for arg in args {
                    Self::collect_runtime_checks_for_type_at_location(arg, local, location, checks);
                }
            }
            _ => {}
        }
    }

    fn statement_uses_local(&self, stmt: &Statement, local: Local) -> bool {
        match stmt {
            // Runtime checks must guard reads, not write destinations. Treating a
            // destination local as a "use" injects checks before initialization.
            Statement::Assign(_, rvalue) => match rvalue {
                Rvalue::Use(op) => Self::operand_uses_local(op, local),
                Rvalue::Ref(_, place) => place.local == local,
                Rvalue::Discriminant(place) => place.local == local,
            },
            Statement::RuntimeCheck(_) => false,
            Statement::StorageLive(_) | Statement::StorageDead(_) => false,
            Statement::Nop => false,
        }
    }

    fn terminator_uses_local(&self, term: &Terminator, local: Local) -> bool {
        match term {
            Terminator::Call { func, args, .. } => {
                if self.call_operand_uses_local(func, local) {
                    return true;
                }
                if args.iter().any(|arg| Self::operand_uses_local(arg, local)) {
                    return true;
                }
                false
            }
            Terminator::SwitchInt { discr, .. } => Self::operand_uses_local(discr, local),
            _ => false,
        }
    }

    fn operand_uses_local(op: &Operand, local: Local) -> bool {
        match op {
            Operand::Copy(p) | Operand::Move(p) => p.local == local,
            Operand::Constant(c) => c.literal.capture_operands().map_or(false, |caps| {
                caps.iter().any(|op| Self::operand_uses_local(op, local))
            }),
        }
    }

    fn call_operand_uses_local(&self, op: &CallOperand, local: Local) -> bool {
        match op {
            CallOperand::Borrow(_, place) => place.local == local,
            CallOperand::Operand(op) => Self::operand_uses_local(op, local),
        }
    }

    /// Convert the checker state into a structured result for codegen
    pub fn into_result(self) -> BorrowCheckResult {
        let num_locations = self.context.location_index.len();
        let location_index = self.context.location_index.clone();

        // Compute loans with live ranges
        let loans_with_ranges: Vec<LoanWithLiveRange> = self
            .loans
            .iter()
            .map(|loan| {
                let live_at = self
                    .context
                    .region_values
                    .get(&loan.region)
                    .cloned()
                    .unwrap_or_else(|| LocationSet::new(num_locations));
                LoanWithLiveRange {
                    loan: loan.clone(),
                    live_at,
                }
            })
            .collect();

        // Collect runtime checks
        let runtime_checks = self.collect_runtime_checks();

        let success = self.errors.is_empty();

        BorrowCheckResult {
            region_solution: self.context.region_values,
            location_index,
            loans_with_ranges,
            runtime_checks,
            errors: self.errors,
            success,
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum AccessKind {
    Read,
    Write,
    Borrow(BorrowKind),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ResolvedPlace {
    place: Place,
    origin_chain: Vec<Local>,
}

fn places_conflict_base(p1: &Place, p2: &Place, index_constants: &[Option<u64>]) -> bool {
    if p1.local != p2.local {
        return false;
    }
    // Simplification: if local matches, they likely conflict unless disjoint fields.
    // E.g. x.0 vs x.1
    for (e1, e2) in p1.projection.iter().zip(p2.projection.iter()) {
        if e1 != e2 {
            if let (PlaceElem::Field(i), PlaceElem::Field(j)) = (e1, e2) {
                if i != j {
                    return false;
                }
            }
            if let (PlaceElem::Downcast(i), PlaceElem::Downcast(j)) = (e1, e2) {
                if i != j {
                    return false;
                }
            }
            if let (PlaceElem::Index(i), PlaceElem::Index(j)) = (e1, e2) {
                let idx_i = index_constants.get(i.0 as usize).copied().flatten();
                let idx_j = index_constants.get(j.0 as usize).copied().flatten();
                match (idx_i, idx_j) {
                    (Some(lhs), Some(rhs)) if lhs != rhs => return false,
                    (Some(_), Some(_)) => continue,
                    _ => return true,
                }
            }
            return true;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{AdtId, Mutability};
    use crate::{BasicBlockData, Constant, Literal, LocalDecl};
    use kernel::ast::Term;

    #[test]
    fn test_renumber() {
        let mut body = Body::new(0);
        // Ref(Region(1), Nat)
        let ty = MirType::Ref(Region(1), Box::new(MirType::Nat), Mutability::Not);
        body.local_decls.push(LocalDecl::new(ty, None));
        body.local_decls.push(LocalDecl::new(
            MirType::Ref(Region::STATIC, Box::new(MirType::Nat), Mutability::Not),
            None,
        ));

        let checker = NllChecker::new(&body);

        let local_ty = &checker.local_types[&Local(0)];
        if let MirType::Ref(r, _, _) = local_ty {
            assert_eq!(r.0, 1, "Should be renumbered to 1 (0 is static)");
        } else {
            panic!("Expected Ref");
        }
        let static_ty = &checker.local_types[&Local(1)];
        if let MirType::Ref(r, _, _) = static_ty {
            assert_eq!(*r, Region::STATIC, "Static region should be preserved");
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
            statements: vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
            )],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        let result = checker.into_result();

        assert!(result.is_ok(), "Simple copy should pass borrow check");
        assert!(result.errors.is_empty());
        assert!(
            result.runtime_checks.is_empty(),
            "No interior mutability, no runtime checks"
        );
    }

    #[test]
    fn relate_types_skips_mismatched_indices() {
        let body = Body::new(0);
        let mut checker = NllChecker::new(&body);

        let zero = Term::ctor("Nat".to_string(), 0);
        let one = Term::app(Term::ctor("Nat".to_string(), 1), zero.clone());
        let adt_id = AdtId::new("Vec");

        let ty_a = MirType::Adt(
            adt_id.clone(),
            vec![
                MirType::Ref(Region(1), Box::new(MirType::Nat), Mutability::Not),
                MirType::IndexTerm(zero),
            ],
        );
        let ty_b = MirType::Adt(
            adt_id,
            vec![
                MirType::Ref(Region(2), Box::new(MirType::Nat), Mutability::Not),
                MirType::IndexTerm(one),
            ],
        );

        checker.relate_types(&ty_a, &ty_b);

        assert!(
            checker.context.constraints.is_empty(),
            "Expected no constraints for index-mismatched ADTs, got {:?}",
            checker.context.constraints
        );
    }

    #[test]
    fn test_borrow_check_result_with_loan() {
        let mut body = Body::new(1);
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        body.local_decls.push(LocalDecl::new(
            MirType::Ref(Region(1), Box::new(MirType::Nat), Mutability::Not),
            None,
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: Local(2),
                        projection: vec![PlaceElem::Deref],
                    })),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        let result = checker.into_result();

        assert!(result.is_ok(), "Borrow and deref should pass");
        assert_eq!(result.loans_with_ranges.len(), 1, "Should have one loan");
        assert!(
            !result.loans_with_ranges[0].live_at.is_empty(),
            "Loan should have live range"
        );
    }

    #[test]
    fn test_borrow_check_result_with_refcell() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));
        body.local_decls.push(LocalDecl::new(
            MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell),
            None,
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell),
                    }))),
                ),
                // Explicit read use; runtime checks are only injected for reads.
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.check();
        let result = checker.into_result();

        assert!(result.is_ok());
        // Should have runtime checks for RefCell usage
        assert!(
            !result.runtime_checks.is_empty(),
            "RefCell should generate runtime checks"
        );
        assert!(matches!(
            result.runtime_checks[0].kind,
            RuntimeCheckKind::RefCellBorrow { .. }
        ));
    }

    #[test]
    fn test_inject_runtime_checks() {
        let mut body = Body::new(0);
        body.local_decls.push(LocalDecl::new(MirType::Unit, None));
        body.local_decls.push(LocalDecl::new(
            MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell),
            None,
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(0),
                        ty: MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell),
                    }))),
                ),
                // Explicit read use; runtime checks are only injected for reads.
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
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
                body_with_checks.basic_blocks[0].statements[1],
                Statement::RuntimeCheck(RuntimeCheckKind::RefCellBorrow { .. })
            ),
            "Expected runtime check to be injected before the use site"
        );
    }

    #[test]
    fn test_missing_synthetic_region_reports_internal_invariant() {
        let mut body = Body::new(1);
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
            )],
            terminator: Some(Terminator::Return),
        });

        let mut checker = NllChecker::new(&body);
        checker.propagate_closure_captures();
        checker.assign_synthetic_borrow_regions();
        checker.synthetic_borrow_regions.clear();
        checker.check_with_assigned_regions();

        let invariant_error = checker.errors.iter().find_map(|e| match e {
            BorrowError::InternalInvariant {
                invariant,
                evidence,
                location,
                ..
            } => Some((invariant, evidence, location)),
            _ => None,
        });

        let (invariant, evidence, location) = invariant_error
            .expect("expected internal invariant diagnostic for missing synthetic region");
        assert_eq!(
            *invariant,
            "synthetic borrow region exists for reference assignment destination"
        );
        assert!(
            evidence.contains("destination local _2"),
            "expected evidence to mention destination local, got: {}",
            evidence
        );
        assert_eq!(
            *location,
            Some(MirSpan {
                block: BasicBlock(0),
                statement_index: 0,
            })
        );
    }

    #[test]
    fn test_borrow_check_result_failure() {
        let mut body = Body::new(1);
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        body.local_decls.push(LocalDecl::new(MirType::Nat, None));
        body.local_decls.push(LocalDecl::new(
            MirType::Ref(Region(1), Box::new(MirType::Nat), Mutability::Not),
            None,
        ));

        // Borrow, mutate while borrowed, use borrow - should fail
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(42),
                        ty: MirType::Nat,
                    }))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: Local(2),
                        projection: vec![PlaceElem::Deref],
                    })),
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
            MirType::Ref(Region(1), Box::new(MirType::Nat), Mutability::Not),
            None,
        ));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Ref(BorrowKind::Shared, Place::from(Local(1))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: Local(2),
                        projection: vec![PlaceElem::Deref],
                    })),
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
