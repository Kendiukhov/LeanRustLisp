//! Dead Code Elimination pass for MIR
//!
//! This pass removes:
//! 1. Unreachable basic blocks
//! 2. Unused local variables
//! 3. Storage statements for unused locals

use crate::{
    BasicBlock, Body, CallOperand, Operand, RuntimeCheckKind, Rvalue, Statement, Terminator,
};
use std::collections::{HashMap, HashSet};

/// Remove unreachable basic blocks and unused locals from a MIR body.
pub fn eliminate_dead_code(body: &mut Body) {
    // Phase 1: Find reachable blocks
    let reachable = find_reachable_blocks(body);

    // Phase 2: Remove unreachable blocks and remap block indices
    let block_remap = remove_unreachable_blocks(body, &reachable);

    // Phase 3: Update block references in terminators
    update_block_references(body, &block_remap);

    // Phase 4: Find used locals
    let used_locals = find_used_locals(body);

    // Phase 5: Remove storage statements for unused locals
    remove_unused_storage(body, &used_locals);
}

/// Find all basic blocks reachable from the entry block (block 0).
fn find_reachable_blocks(body: &Body) -> HashSet<usize> {
    let mut reachable = HashSet::new();
    let mut worklist = vec![0usize]; // Start from entry block

    while let Some(block_idx) = worklist.pop() {
        if reachable.contains(&block_idx) {
            continue;
        }
        if block_idx >= body.basic_blocks.len() {
            continue;
        }

        reachable.insert(block_idx);

        // Add successors to worklist
        if let Some(term) = &body.basic_blocks[block_idx].terminator {
            for succ in terminator_successors(term) {
                if !reachable.contains(&succ) {
                    worklist.push(succ);
                }
            }
        }
    }

    reachable
}

/// Get the successor block indices from a terminator.
fn terminator_successors(term: &Terminator) -> Vec<usize> {
    match term {
        Terminator::Return | Terminator::Unreachable => vec![],
        Terminator::Goto { target } => vec![target.index()],
        Terminator::SwitchInt { targets, .. } => {
            targets.targets.iter().map(|b| b.index()).collect()
        }
        Terminator::Call { target, .. } => {
            if let Some(t) = target {
                vec![t.index()]
            } else {
                vec![]
            }
        }
    }
}

/// Remove unreachable blocks and return a mapping from old indices to new indices.
fn remove_unreachable_blocks(body: &mut Body, reachable: &HashSet<usize>) -> HashMap<usize, usize> {
    let mut block_remap = HashMap::new();
    let mut new_blocks = Vec::new();

    for (old_idx, block) in body.basic_blocks.drain(..).enumerate() {
        if reachable.contains(&old_idx) {
            let new_idx = new_blocks.len();
            block_remap.insert(old_idx, new_idx);
            new_blocks.push(block);
        }
    }

    body.basic_blocks = new_blocks;
    block_remap
}

/// Update all block references in terminators to use new indices.
fn update_block_references(body: &mut Body, remap: &HashMap<usize, usize>) {
    for block in &mut body.basic_blocks {
        if let Some(term) = &mut block.terminator {
            match term {
                Terminator::Goto { target } => {
                    if let Some(&new_idx) = remap.get(&target.index()) {
                        *target = BasicBlock::from(new_idx);
                    }
                }
                Terminator::SwitchInt { targets, .. } => {
                    for target in &mut targets.targets {
                        if let Some(&new_idx) = remap.get(&target.index()) {
                            *target = BasicBlock::from(new_idx);
                        }
                    }
                }
                Terminator::Call {
                    target: Some(target),
                    ..
                } => {
                    if let Some(&new_idx) = remap.get(&target.index()) {
                        *target = BasicBlock::from(new_idx);
                    }
                }
                Terminator::Call { target: None, .. } => {}
                _ => {}
            }
        }
    }
}

/// Find all locals that are used (read from) in the MIR body.
fn find_used_locals(body: &Body) -> HashSet<usize> {
    let mut used = HashSet::new();

    // _0 is always used (return value)
    used.insert(0);

    // Arguments are always used
    for i in 1..=body.arg_count {
        used.insert(i);
    }

    for block in &body.basic_blocks {
        // Check statements
        for stmt in &block.statements {
            match stmt {
                Statement::Assign(dest, rvalue) => {
                    // The destination is defined, not used
                    // But if it has projections, the base is used
                    if !dest.projection.is_empty() {
                        used.insert(dest.local.index());
                    }

                    // Collect uses from rvalue
                    collect_rvalue_uses(rvalue, &mut used);
                }
                Statement::RuntimeCheck(check) => match check {
                    RuntimeCheckKind::RefCellBorrow { local } => {
                        used.insert(local.index());
                    }
                    RuntimeCheckKind::MutexLock { local } => {
                        used.insert(local.index());
                    }
                    RuntimeCheckKind::BoundsCheck { local, index } => {
                        used.insert(local.index());
                        used.insert(index.index());
                    }
                },
                Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => {}
            }
        }

        // Check terminator
        if let Some(term) = &block.terminator {
            match term {
                Terminator::SwitchInt { discr, .. } => {
                    collect_operand_uses(discr, &mut used);
                }
                Terminator::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {
                    collect_call_operand_uses(func, &mut used);
                    for arg in args {
                        collect_operand_uses(arg, &mut used);
                    }
                    // Destination's projections might use the base
                    if !destination.projection.is_empty() {
                        used.insert(destination.local.index());
                    }
                }
                _ => {}
            }
        }
    }

    used
}

fn collect_rvalue_uses(rvalue: &Rvalue, used: &mut HashSet<usize>) {
    match rvalue {
        Rvalue::Use(op) => collect_operand_uses(op, used),
        Rvalue::Ref(_, place) => {
            used.insert(place.local.index());
        }
        Rvalue::Discriminant(place) => {
            used.insert(place.local.index());
        }
    }
}

fn collect_operand_uses(op: &Operand, used: &mut HashSet<usize>) {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            used.insert(place.local.index());
        }
        Operand::Constant(c) => {
            if let Some(captures) = c.literal.capture_operands() {
                for cap in captures {
                    collect_operand_uses(cap, used);
                }
            }
        }
    }
}

fn collect_call_operand_uses(op: &CallOperand, used: &mut HashSet<usize>) {
    match op {
        CallOperand::Borrow(_, place) => {
            used.insert(place.local.index());
        }
        CallOperand::Operand(op) => collect_operand_uses(op, used),
    }
}

/// Remove StorageLive/StorageDead statements for unused locals.
fn remove_unused_storage(body: &mut Body, used: &HashSet<usize>) {
    for block in &mut body.basic_blocks {
        block.statements.retain(|stmt| match stmt {
            Statement::StorageLive(local) | Statement::StorageDead(local) => {
                used.contains(&local.index())
            }
            _ => true,
        });
    }
}

/// Simplify control flow by removing empty blocks and folding unconditional jumps.
pub fn simplify_cfg(body: &mut Body) {
    // Iteratively simplify until no more changes
    loop {
        let changed = simplify_cfg_once(body);
        if !changed {
            break;
        }
    }
}

/// Single pass of CFG simplification. Returns true if any changes were made.
fn simplify_cfg_once(body: &mut Body) -> bool {
    let mut changed = false;

    // Phase 1: Find blocks that can be bypassed (empty blocks with just Goto)
    // Resolve the full bypass chain to avoid intermediate blocks
    let mut bypass_map: HashMap<usize, usize> = HashMap::new();

    for (idx, block) in body.basic_blocks.iter().enumerate() {
        // Don't bypass entry block
        if idx == 0 {
            continue;
        }

        // Check if block is empty and just does a Goto
        if block.statements.is_empty() {
            if let Some(Terminator::Goto { target }) = &block.terminator {
                bypass_map.insert(idx, target.index());
            }
        }
    }

    // Resolve bypass chains (A -> B -> C becomes A -> C)
    let resolved_bypass: HashMap<usize, usize> = bypass_map
        .keys()
        .map(|&start| {
            let mut current = start;
            let mut visited = HashSet::new();
            while let Some(&next) = bypass_map.get(&current) {
                if visited.contains(&next) || next == start {
                    break; // Avoid infinite loops
                }
                visited.insert(current);
                current = next;
            }
            (start, current)
        })
        .filter(|(start, end)| start != end)
        .collect();

    // Phase 2: Update terminators to bypass empty blocks
    for block in &mut body.basic_blocks {
        if let Some(term) = &mut block.terminator {
            match term {
                Terminator::Goto { target } => {
                    if let Some(&new_target) = resolved_bypass.get(&target.index()) {
                        if new_target != target.index() {
                            *target = BasicBlock::from(new_target);
                            changed = true;
                        }
                    }
                }
                Terminator::SwitchInt { targets, .. } => {
                    for target in &mut targets.targets {
                        if let Some(&new_target) = resolved_bypass.get(&target.index()) {
                            if new_target != target.index() {
                                *target = BasicBlock::from(new_target);
                                changed = true;
                            }
                        }
                    }
                }
                Terminator::Call {
                    target: Some(target),
                    ..
                } => {
                    if let Some(&new_target) = resolved_bypass.get(&target.index()) {
                        if new_target != target.index() {
                            *target = BasicBlock::from(new_target);
                            changed = true;
                        }
                    }
                }
                Terminator::Call { target: None, .. } => {}
                _ => {}
            }
        }
    }

    // Phase 3: Merge blocks with single predecessor and single successor
    // Only do this if we didn't do any bypassing (to avoid stale predecessor info)
    if !changed {
        let predecessors = build_predecessor_map(body);

        for idx in 0..body.basic_blocks.len() {
            // Skip blocks that are bypass targets (they might be removed later)
            if resolved_bypass.values().any(|&v| v == idx) {
                continue;
            }

            if let Some(Terminator::Goto { target }) = body.basic_blocks[idx].terminator.clone() {
                let target_idx = target.index();
                if target_idx != idx && target_idx < body.basic_blocks.len() {
                    // Check if target has exactly one predecessor and isn't empty (bypass handles empty)
                    if let Some(preds) = predecessors.get(&target_idx) {
                        if preds.len() == 1 && preds.contains(&idx) {
                            // Only merge if target has statements (non-empty blocks)
                            if !body.basic_blocks[target_idx].statements.is_empty() {
                                let target_stmts =
                                    std::mem::take(&mut body.basic_blocks[target_idx].statements);
                                let target_term = body.basic_blocks[target_idx].terminator.take();

                                body.basic_blocks[idx].statements.extend(target_stmts);
                                body.basic_blocks[idx].terminator = target_term;
                                changed = true;
                                break; // Only one merge per iteration for safety
                            }
                        }
                    }
                }
            }
        }
    }

    changed
}

/// Build a map from block index to its predecessors.
fn build_predecessor_map(body: &Body) -> HashMap<usize, HashSet<usize>> {
    let mut predecessors: HashMap<usize, HashSet<usize>> = HashMap::new();

    for (idx, block) in body.basic_blocks.iter().enumerate() {
        if let Some(term) = &block.terminator {
            for succ in terminator_successors(term) {
                predecessors.entry(succ).or_default().insert(idx);
            }
        }
    }

    predecessors
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::MirType;
    use crate::{BasicBlockData, Local, LocalDecl, Place, SwitchTargets};

    fn dummy_ty() -> MirType {
        MirType::Unit
    }

    #[test]
    fn test_remove_unreachable_blocks() {
        let mut body = Body::new(0);

        // Block 0: goto 1
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(1),
            }),
        });

        // Block 1: return (reachable)
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        // Block 2: unreachable (no edge to it)
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_0".to_string())));

        eliminate_dead_code(&mut body);

        assert_eq!(
            body.basic_blocks.len(),
            2,
            "Unreachable block should be removed"
        );
    }

    #[test]
    fn test_remove_unused_storage() {
        let mut body = Body::new(0);

        // Create locals
        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_0".to_string()))); // Return
        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_1".to_string()))); // Used
        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_2".to_string()))); // Unused

        // Block with storage statements for both used and unused locals
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::StorageLive(Local(1)),
                Statement::StorageLive(Local(2)), // Unused
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
                ),
                Statement::StorageDead(Local(1)),
                Statement::StorageDead(Local(2)), // Unused
            ],
            terminator: Some(Terminator::Return),
        });

        eliminate_dead_code(&mut body);

        // StorageLive/Dead for Local(2) should be removed
        let storage_count = body.basic_blocks[0]
            .statements
            .iter()
            .filter(|s| {
                matches!(
                    s,
                    Statement::StorageLive(Local(2)) | Statement::StorageDead(Local(2))
                )
            })
            .count();
        assert_eq!(
            storage_count, 0,
            "Unused storage statements should be removed"
        );
    }

    #[test]
    fn test_find_reachable_with_switch() {
        let mut body = Body::new(0);

        // Block 0: switch to 1 or 2
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::SwitchInt {
                discr: Operand::Constant(Box::new(crate::Constant {
                    literal: crate::Literal::Nat(0),
                    ty: dummy_ty(),
                })),
                targets: SwitchTargets {
                    values: vec![0],
                    targets: vec![BasicBlock(1), BasicBlock(2)],
                },
            }),
        });

        // Block 1: return
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        // Block 2: return
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        // Block 3: unreachable
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_0".to_string())));

        let reachable = find_reachable_blocks(&body);

        assert!(reachable.contains(&0));
        assert!(reachable.contains(&1));
        assert!(reachable.contains(&2));
        assert!(!reachable.contains(&3), "Block 3 should be unreachable");
    }

    #[test]
    fn test_cfg_simplify_bypass_empty_block() {
        let mut body = Body::new(0);

        // Block 0: goto 1
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(1),
            }),
        });

        // Block 1: empty, goto 2 (should be bypassed)
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(2),
            }),
        });

        // Block 2: return
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Return),
        });

        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_0".to_string())));

        simplify_cfg(&mut body);

        // Block 0 should now goto 2 directly
        if let Some(Terminator::Goto { target }) = &body.basic_blocks[0].terminator {
            assert_eq!(
                target.index(),
                2,
                "Block 0 should bypass block 1 and go to block 2"
            );
        } else {
            panic!("Expected Goto terminator");
        }
    }

    #[test]
    fn test_cfg_simplify_merge_blocks() {
        let mut body = Body::new(0);

        // Block 0: has statements, goto 1
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Nop],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(1),
            }),
        });

        // Block 1: has statements, return (only predecessor is block 0)
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Nop, Statement::Nop],
            terminator: Some(Terminator::Return),
        });

        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_0".to_string())));

        simplify_cfg(&mut body);

        // Block 0 should now have all statements and return
        assert_eq!(
            body.basic_blocks[0].statements.len(),
            3,
            "Block 0 should have merged statements"
        );
        assert!(matches!(
            body.basic_blocks[0].terminator,
            Some(Terminator::Return)
        ));
    }

    #[test]
    fn test_cfg_simplify_chain() {
        let mut body = Body::new(0);

        // Chain: 0 -> 1 -> 2 -> 3 (all empty except 3)
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(1),
            }),
        });
        body.basic_blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator::Goto {
                target: BasicBlock(2),
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

        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_0".to_string())));

        simplify_cfg(&mut body);

        // Block 0 should eventually go to block 3
        if let Some(Terminator::Goto { target }) = &body.basic_blocks[0].terminator {
            assert_eq!(target.index(), 3, "Block 0 should bypass chain to block 3");
        } else {
            panic!("Expected Goto terminator");
        }
    }
}
