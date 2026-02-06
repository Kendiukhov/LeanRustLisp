use crate::{
    BasicBlock, Body, CallOperand, Local, Operand, RuntimeCheckKind, Statement, Terminator,
};

/// Compact set of locals backed by a fixed-size bitset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalSet {
    words: Vec<u64>,
    num_bits: usize,
}

impl LocalSet {
    pub fn new(num_bits: usize) -> Self {
        let words = vec![0; num_bits.div_ceil(64)];
        Self { words, num_bits }
    }

    pub fn insert(&mut self, local: Local) -> bool {
        self.insert_index(local.index())
    }

    pub fn remove(&mut self, local: Local) -> bool {
        self.remove_index(local.index())
    }

    pub fn contains(&self, local: Local) -> bool {
        self.contains_index(local.index())
    }

    pub fn union_with(&mut self, other: &LocalSet) -> bool {
        if self.num_bits != other.num_bits {
            return false;
        }
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

    pub fn iter(&self) -> impl Iterator<Item = Local> + '_ {
        self.iter_indices().map(|idx| Local(idx as u32))
    }

    fn insert_index(&mut self, index: usize) -> bool {
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

    fn remove_index(&mut self, index: usize) -> bool {
        if index >= self.num_bits {
            return false;
        }
        let word_idx = index / 64;
        let bit_idx = index % 64;
        let mask = 1u64 << bit_idx;
        let before = self.words[word_idx];
        self.words[word_idx] &= !mask;
        before != self.words[word_idx]
    }

    fn contains_index(&self, index: usize) -> bool {
        if index >= self.num_bits {
            return false;
        }
        let word_idx = index / 64;
        let bit_idx = index % 64;
        (self.words[word_idx] & (1u64 << bit_idx)) != 0
    }

    fn iter_indices(&self) -> LocalSetIter<'_> {
        LocalSetIter {
            words: &self.words,
            word_index: 0,
            current_word: 0,
            base_index: 0,
            num_bits: self.num_bits,
        }
    }
}

struct LocalSetIter<'a> {
    words: &'a [u64],
    word_index: usize,
    current_word: u64,
    base_index: usize,
    num_bits: usize,
}

impl<'a> Iterator for LocalSetIter<'a> {
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

/// Result of liveness analysis: live locals at entry/exit of each block.
pub struct LivenessResult {
    pub ins: Vec<LocalSet>,
    pub outs: Vec<LocalSet>,
}

impl LivenessResult {
    pub fn in_set(&self, block: BasicBlock) -> Option<&LocalSet> {
        self.ins.get(block.index())
    }

    pub fn out_set(&self, block: BasicBlock) -> Option<&LocalSet> {
        self.outs.get(block.index())
    }
}

pub fn compute_liveness(body: &Body) -> LivenessResult {
    let local_count = body.local_decls.len();
    let mut ins = vec![LocalSet::new(local_count); body.basic_blocks.len()];
    let mut outs = vec![LocalSet::new(local_count); body.basic_blocks.len()];

    let mut changed = true;
    while changed {
        changed = false;

        // Backward traversal
        for i in (0..body.basic_blocks.len()).rev() {
            let block = &body.basic_blocks[i];

            // Out = Union of Successors' In
            let mut new_out = LocalSet::new(local_count);
            if let Some(term) = &block.terminator {
                for_each_successor(term, |succ| {
                    if let Some(succ_in) = ins.get(succ.index()) {
                        new_out.union_with(succ_in);
                    }
                });
            }

            if new_out != outs[i] {
                outs[i] = new_out.clone();
                changed = true;
            }

            // In = (Out - Kill) U Gen
            let mut current_live = new_out;

            if let Some(term) = &block.terminator {
                process_terminator(term, &mut current_live);
            }

            for stmt in block.statements.iter().rev() {
                process_statement(stmt, &mut current_live);
            }

            if current_live != ins[i] {
                ins[i] = current_live;
                changed = true;
            }
        }
    }

    LivenessResult { ins, outs }
}

fn for_each_successor(term: &Terminator, mut f: impl FnMut(BasicBlock)) {
    match term {
        Terminator::Goto { target } => f(*target),
        Terminator::SwitchInt { targets, .. } => {
            for target in &targets.targets {
                f(*target);
            }
        }
        Terminator::Call { target, .. } => {
            if let Some(t) = target {
                f(*t);
            }
        }
        _ => {}
    }
}

pub fn process_statement(stmt: &Statement, live: &mut LocalSet) {
    match stmt {
        Statement::Assign(place, rvalue) => {
            if place.projection.is_empty() {
                live.remove(place.local);
            } else {
                live.insert(place.local);
            }

            use crate::Rvalue::*;
            match rvalue {
                Use(op) => process_operand(op, live),
                Ref(_, p) => {
                    live.insert(p.local);
                }
                Discriminant(p) => {
                    live.insert(p.local);
                }
            }
        }
        Statement::RuntimeCheck(check) => match check {
            RuntimeCheckKind::RefCellBorrow { local } => {
                live.insert(*local);
            }
            RuntimeCheckKind::MutexLock { local } => {
                live.insert(*local);
            }
            RuntimeCheckKind::BoundsCheck { local, index } => {
                live.insert(*local);
                live.insert(*index);
            }
        },
        Statement::StorageLive(l) => {
            live.remove(*l);
        }
        Statement::StorageDead(l) => {
            live.remove(*l);
        }
        Statement::Nop => {}
    }
}

pub fn process_terminator(term: &Terminator, live: &mut LocalSet) {
    use crate::Terminator::*;
    match term {
        SwitchInt { discr, .. } => process_operand(discr, live),
        Call {
            func,
            args,
            destination,
            ..
        } => {
            process_call_operand(func, live);
            for arg in args {
                process_operand(arg, live);
            }
            if destination.projection.is_empty() {
                live.remove(destination.local);
            } else {
                live.insert(destination.local);
            }
        }
        Return => {
            live.insert(Local(0));
        }
        _ => {}
    }
}

fn process_operand(op: &Operand, live: &mut LocalSet) {
    use crate::Operand::*;
    match op {
        Copy(p) | Move(p) => {
            live.insert(p.local);
        }
        Constant(c) => {
            if let Some(captures) = c.literal.capture_operands() {
                for cap in captures {
                    process_operand(cap, live);
                }
            }
        }
    }
}

fn process_call_operand(op: &CallOperand, live: &mut LocalSet) {
    match op {
        CallOperand::Borrow(_, place) => {
            live.insert(place.local);
        }
        CallOperand::Operand(op) => process_operand(op, live),
    }
}
