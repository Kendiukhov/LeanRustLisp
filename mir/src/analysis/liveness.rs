use crate::{Body, Local, BasicBlock, Statement, Terminator, Operand, RuntimeCheckKind};
use std::collections::{HashMap, HashSet};

/// Result of liveness analysis: Sets of live locals at entry/exit of each block.
pub struct LivenessResult {
    pub ins: HashMap<BasicBlock, HashSet<Local>>,
    pub outs: HashMap<BasicBlock, HashSet<Local>>,
}

pub fn compute_liveness(body: &Body) -> LivenessResult {
    let mut ins = HashMap::new();
    let mut outs = HashMap::new();
    
    // Init sets
    for (i, _) in body.basic_blocks.iter().enumerate() {
        ins.insert(BasicBlock(i as u32), HashSet::new());
        outs.insert(BasicBlock(i as u32), HashSet::new());
    }
    
    let mut changed = true;
    while changed {
        changed = false;
        
        // Backward traversal
        for i in (0..body.basic_blocks.len()).rev() {
            let bb = BasicBlock(i as u32);
            let block = &body.basic_blocks[i];
            
            // Out = Union of Successors' In
            let mut new_out = HashSet::new();
            if let Some(term) = &block.terminator {
                for succ in successors(term) {
                    if let Some(succ_in) = ins.get(&succ) {
                        new_out.extend(succ_in.iter().cloned());
                    }
                }
            }
            
            if new_out != outs[&bb] {
                outs.insert(bb, new_out.clone());
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
            
            if current_live != ins[&bb] {
                ins.insert(bb, current_live);
                changed = true;
            }
        }
    }
    
    LivenessResult { ins, outs }
}

fn successors(term: &Terminator) -> Vec<BasicBlock> {
    match term {
        Terminator::Goto { target } => vec![*target],
        Terminator::SwitchInt { targets, .. } => targets.targets.clone(),
        Terminator::Call { target, .. } => {
            if let Some(t) = target { vec![*t] } else { vec![] }
        },
        _ => vec![],
    }
}

pub fn process_statement(stmt: &Statement, live: &mut HashSet<Local>) {
    match stmt {
        Statement::Assign(place, rvalue) => {
            if place.projection.is_empty() {
                live.remove(&place.local);
            } else {
                live.insert(place.local);
            }
            
            use crate::Rvalue::*;
            match rvalue {
                Use(op) => process_operand(op, live),
                Ref(_, p) => { live.insert(p.local); },
                Discriminant(p) => { live.insert(p.local); },
            }
        },
        Statement::RuntimeCheck(check) => {
            match check {
                RuntimeCheckKind::RefCellBorrow { local } => { live.insert(*local); }
                RuntimeCheckKind::MutexLock { local } => { live.insert(*local); }
                RuntimeCheckKind::BoundsCheck { local, index } => {
                    live.insert(*local);
                    live.insert(*index);
                }
            }
        }
        Statement::StorageLive(l) => {
            live.remove(l);
        },
        Statement::StorageDead(l) => {
            live.remove(l);
        },
        Statement::Nop => {},
    }
}

pub fn process_terminator(term: &Terminator, live: &mut HashSet<Local>) {
    use crate::Terminator::*;
    match term {
        SwitchInt { discr, .. } => process_operand(discr, live),
        Call { func, args, destination, .. } => {
            process_operand(func, live);
            for arg in args {
                process_operand(arg, live);
            }
            if destination.projection.is_empty() {
                live.remove(&destination.local);
            } else {
                live.insert(destination.local);
            }
        },
        Return => {
            live.insert(Local(0));
        },
        _ => {},
    }
}

fn process_operand(op: &Operand, live: &mut HashSet<Local>) {
    use crate::Operand::*;
    match op {
        Copy(p) | Move(p) => {
            live.insert(p.local);
        },
        Constant(_) => {},
    }
}
