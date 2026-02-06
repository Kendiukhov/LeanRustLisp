//! Basic inlining and constant folding optimizations for MIR
//!
//! This module provides:
//! 1. Constant folding - evaluate constant expressions at compile time
//! 2. Copy propagation - replace uses of copied values with the original
//!
//! Note: Full function inlining is complex for functional languages with closures.
//! This module provides a foundation that can be extended.

use crate::{Body, CallOperand, Constant, Local, Operand, Rvalue, Statement};
use std::collections::HashMap;

/// Perform constant folding and copy propagation on a MIR body.
pub fn optimize(body: &mut Body) {
    // Run multiple passes until no changes
    loop {
        let changed = optimize_once(body);
        if !changed {
            break;
        }
    }
}

/// Single optimization pass. Returns true if any changes were made.
fn optimize_once(body: &mut Body) -> bool {
    let mut changed = false;

    // Build a map of locals that are simple copies of other locals or constants
    let copy_map = build_copy_map(body);

    // Propagate copies through the body
    for block in &mut body.basic_blocks {
        for stmt in &mut block.statements {
            if let Statement::Assign(_, rvalue) = stmt {
                if propagate_copies(rvalue, &copy_map) {
                    changed = true;
                }
            }
        }

        // Propagate in terminator operands
        if let Some(term) = &mut block.terminator {
            match term {
                crate::Terminator::SwitchInt { discr, .. } => {
                    if propagate_operand_copies(discr, &copy_map) {
                        changed = true;
                    }
                }
                crate::Terminator::Call { func, args, .. } => {
                    if propagate_call_operand_copies(func, &copy_map) {
                        changed = true;
                    }
                    for arg in args {
                        if propagate_operand_copies(arg, &copy_map) {
                            changed = true;
                        }
                    }
                }
                _ => {}
            }
        }
    }

    changed
}

/// Map from local to its known value (either another local or a constant).
#[derive(Clone)]
enum KnownValue {
    Local(Local),
    Constant(Box<Constant>),
}

/// Build a map of locals that are simple copies.
fn build_copy_map(body: &Body) -> HashMap<usize, KnownValue> {
    let mut copy_map = HashMap::new();

    for block in &body.basic_blocks {
        for stmt in &block.statements {
            if let Statement::Assign(place, rvalue) = stmt {
                // Only track simple local assignments (no projections)
                if !place.projection.is_empty() {
                    continue;
                }

                let local_idx = place.local.index();

                match rvalue {
                    Rvalue::Use(Operand::Copy(src)) | Rvalue::Use(Operand::Move(src)) => {
                        if src.projection.is_empty() {
                            // local = other_local
                            copy_map.insert(local_idx, KnownValue::Local(src.local));
                        }
                    }
                    Rvalue::Use(Operand::Constant(c)) => {
                        // local = constant
                        copy_map.insert(local_idx, KnownValue::Constant(c.clone()));
                    }
                    _ => {
                        // Complex assignment - remove from map if previously tracked
                        copy_map.remove(&local_idx);
                    }
                }
            }
        }
    }

    // Resolve chains: if A = B and B = C, then A = C
    let mut resolved = HashMap::new();
    for (&local, _) in &copy_map {
        let final_value = resolve_chain(local, &copy_map);
        resolved.insert(local, final_value);
    }

    resolved
}

/// Resolve a chain of copies to find the ultimate source.
fn resolve_chain(start: usize, copy_map: &HashMap<usize, KnownValue>) -> KnownValue {
    let mut current = start;
    let mut visited = std::collections::HashSet::new();

    loop {
        if visited.contains(&current) {
            // Cycle detected - return the local itself
            return KnownValue::Local(Local(current as u32));
        }
        visited.insert(current);

        match copy_map.get(&current) {
            Some(KnownValue::Local(next)) => {
                current = next.index();
            }
            Some(KnownValue::Constant(c)) => {
                return KnownValue::Constant(c.clone());
            }
            None => {
                return KnownValue::Local(Local(current as u32));
            }
        }
    }
}

/// Propagate known copies into an rvalue. Returns true if changed.
fn propagate_copies(rvalue: &mut Rvalue, copy_map: &HashMap<usize, KnownValue>) -> bool {
    match rvalue {
        Rvalue::Use(op) => propagate_operand_copies(op, copy_map),
        Rvalue::Ref(_, _) => false,
        Rvalue::Discriminant(_) => false,
    }
}

/// Propagate known copies into an operand. Returns true if changed.
fn propagate_operand_copies(op: &mut Operand, copy_map: &HashMap<usize, KnownValue>) -> bool {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            if place.projection.is_empty() {
                if let Some(known) = copy_map.get(&place.local.index()) {
                    match known {
                        KnownValue::Constant(c) => {
                            *op = Operand::Constant(c.clone());
                            return true;
                        }
                        KnownValue::Local(src) => {
                            if src.index() != place.local.index() {
                                place.local = *src;
                                return true;
                            }
                        }
                    }
                }
            }
            false
        }
        Operand::Constant(_) => false,
    }
}

fn propagate_call_operand_copies(
    op: &mut CallOperand,
    copy_map: &HashMap<usize, KnownValue>,
) -> bool {
    match op {
        CallOperand::Operand(inner) => propagate_operand_copies(inner, copy_map),
        CallOperand::Borrow(_, place) => {
            if place.projection.is_empty() {
                if let Some(KnownValue::Local(src)) = copy_map.get(&place.local.index()) {
                    if src.index() != place.local.index() {
                        place.local = *src;
                        return true;
                    }
                }
            }
            false
        }
    }
}

/// Fold constant Nat operations (addition, etc.) if we ever add binary ops to MIR.
/// Currently a placeholder for future expansion.
pub fn fold_constants(_body: &mut Body) {
    // MIR currently doesn't have binary operations - they're function calls.
    // This would be expanded if we add intrinsic operations.
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::MirType;
    use crate::{BasicBlockData, Literal, LocalDecl, Place, Terminator};

    fn dummy_ty() -> MirType {
        MirType::Unit
    }

    #[test]
    fn test_constant_propagation() {
        let mut body = Body::new(0);

        // _0: return
        // _1 = Nat(42)
        // _0 = _1
        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_0".to_string())));
        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_1".to_string())));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(42),
                        ty: dummy_ty(),
                    }))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        optimize(&mut body);

        // After optimization, _0 should be assigned the constant directly
        if let Statement::Assign(_, Rvalue::Use(Operand::Constant(c))) =
            &body.basic_blocks[0].statements[1]
        {
            if let Literal::Nat(n) = c.literal {
                assert_eq!(n, 42, "Constant should be propagated");
            } else {
                panic!("Expected Nat literal");
            }
        } else {
            panic!("Expected constant assignment after propagation");
        }
    }

    #[test]
    fn test_copy_chain_propagation() {
        let mut body = Body::new(0);

        // _0: return
        // _1 = Nat(100)
        // _2 = _1
        // _3 = _2
        // _0 = _3
        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_0".to_string())));
        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_1".to_string())));
        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_2".to_string())));
        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_3".to_string())));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(1)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Nat(100),
                        ty: dummy_ty(),
                    }))),
                ),
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
                ),
                Statement::Assign(
                    Place::from(Local(3)),
                    Rvalue::Use(Operand::Copy(Place::from(Local(2)))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place::from(Local(3)))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        optimize(&mut body);

        // After optimization, _0 should be assigned the constant directly
        if let Statement::Assign(_, Rvalue::Use(Operand::Constant(c))) =
            &body.basic_blocks[0].statements[3]
        {
            if let Literal::Nat(n) = c.literal {
                assert_eq!(n, 100, "Constant should be propagated through chain");
            } else {
                panic!("Expected Nat literal");
            }
        } else {
            panic!("Expected constant assignment after chain propagation");
        }
    }

    #[test]
    fn test_local_propagation() {
        let mut body = Body::new(1); // One argument

        // _0: return
        // _1: argument
        // _2 = _1
        // _0 = _2
        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_0".to_string())));
        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_1".to_string())));
        body.local_decls
            .push(LocalDecl::new(dummy_ty(), Some("_2".to_string())));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place::from(Local(2)))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        optimize(&mut body);

        // After optimization, _0 should be assigned from _1 directly
        if let Statement::Assign(_, Rvalue::Use(Operand::Copy(place))) =
            &body.basic_blocks[0].statements[1]
        {
            assert_eq!(place.local.index(), 1, "Should copy from _1 directly");
        } else {
            panic!("Expected copy from _1");
        }
    }
}
