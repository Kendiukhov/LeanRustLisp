use crate::{Body, Local, Statement, Terminator};
use std::collections::HashSet;

/// Ensure function-exit blocks explicitly drop locals so borrowck sees dangling borrows.
pub fn insert_exit_storage_deads(body: &mut Body) {
    let num_locals = body.local_decls.len();
    if num_locals <= 1 {
        return;
    }

    for bb in &mut body.basic_blocks {
        if !matches!(bb.terminator, Some(Terminator::Return)) {
            continue;
        }

        let mut already_dead = HashSet::new();
        for stmt in &bb.statements {
            if let Statement::StorageDead(local) = stmt {
                already_dead.insert(*local);
            }
        }

        for idx in (1..num_locals).rev() {
            let local = Local(idx as u32);
            if already_dead.contains(&local) {
                continue;
            }
            bb.statements.push(Statement::StorageDead(local));
        }
    }
}
