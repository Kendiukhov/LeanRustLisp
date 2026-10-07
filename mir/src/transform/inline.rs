//! Basic inlining and constant folding optimizations for MIR
//!
//! This module provides:
//! 1. Constant folding - evaluate constant expressions at compile time
//! 2. Copy propagation - replace uses of copied values with the original
//!
//! Note: Full function inlining is complex for functional languages with closures.
//! This module provides a foundation that can be extended.

use crate::types::MirType;
use crate::{Body, CallOperand, Constant, Local, Operand, Rvalue, Statement, Terminator};
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
    let local_types: Vec<MirType> = body
        .local_decls
        .iter()
        .map(|decl| decl.ty.clone())
        .collect();

    // Propagate copies through the body
    for block in &mut body.basic_blocks {
        for stmt in &mut block.statements {
            if let Statement::Assign(place, rvalue) = stmt {
                // An assignment between a stuck type and a known one is a change of
                // representation (see `propagation_keeps_representation`); its source stays the
                // local whose declared type states the known side.
                if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue {
                    if place.projection.is_empty()
                        && !propagation_keeps_representation(
                            &local_types[src.local.index()],
                            &local_types[place.local.index()],
                        )
                    {
                        continue;
                    }
                }
                if propagate_copies(rvalue, &copy_map) {
                    changed = true;
                }
            }
        }

        // Propagate in terminator operands
        if let Some(term) = &mut block.terminator {
            match term {
                Terminator::SwitchInt { discr, .. } => {
                    if propagate_operand_copies(discr, &copy_map) {
                        changed = true;
                    }
                }
                Terminator::Call { func, args, .. } => {
                    // Likewise for an argument passed to a parameter of a stuck type.
                    let callee_ty = match &*func {
                        CallOperand::Operand(Operand::Copy(place) | Operand::Move(place))
                        | CallOperand::Borrow(_, place) => {
                            Some(local_types[place.local.index()].clone())
                        }
                        CallOperand::Operand(Operand::Constant(c)) => Some(c.ty.clone()),
                    };
                    let param_has_stuck_type = match &callee_ty {
                        Some(MirType::Fn(_, _, params, _))
                        | Some(MirType::FnItem(_, _, _, params, _))
                        | Some(MirType::Closure(_, _, _, params, _)) => {
                            params.iter().any(contains_stuck_type)
                        }
                        _ => false,
                    };
                    if propagate_call_operand_copies(func, &copy_map) {
                        changed = true;
                    }
                    for arg in args {
                        if let Operand::Copy(src) | Operand::Move(src) = &*arg {
                            if param_has_stuck_type
                                || contains_stuck_type(&local_types[src.local.index()])
                            {
                                continue;
                            }
                        }
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

/// Build the map of locals whose uses may be replaced by a known value.
///
/// The analysis is flow-insensitive, so it only records facts that hold at every use:
/// - the destination `d` is written exactly once in the body (one whole-local assignment, no
///   call-destination or projected writes) and is neither the return place nor an argument;
/// - the assignment is `d = const c` with a capture-free constant `c` (not a closure literal), or
///   `d = copy s` (a Copy operand, so `d` and `s` have a Copy
///   type) where the source `s` is stable: written at most once (an argument counts as written on
///   entry) and never killed by `StorageDead` before the function exit.
///
/// Moves are never propagated: replacing a use of `d` after `d = move s` by `s` would move `s`
/// twice (the original move stays in place).
fn build_copy_map(body: &Body) -> HashMap<usize, KnownValue> {
    let num_locals = body.local_decls.len();
    let mut writes = vec![0usize; num_locals];
    let mut killed_before_exit = vec![false; num_locals];
    for count in writes.iter_mut().skip(1).take(body.arg_count) {
        *count += 1;
    }
    for block in &body.basic_blocks {
        let is_exit_block = matches!(block.terminator, Some(Terminator::Return));
        for stmt in &block.statements {
            match stmt {
                Statement::Assign(place, _) => {
                    if let Some(count) = writes.get_mut(place.local.index()) {
                        *count += 1;
                    }
                }
                Statement::StorageDead(local) if !is_exit_block => {
                    if let Some(killed) = killed_before_exit.get_mut(local.index()) {
                        *killed = true;
                    }
                }
                _ => {}
            }
        }
        if let Some(Terminator::Call { destination, .. }) = &block.terminator {
            if let Some(count) = writes.get_mut(destination.local.index()) {
                *count += 1;
            }
        }
    }

    let mut copy_map = HashMap::new();
    for block in &body.basic_blocks {
        for stmt in &block.statements {
            let Statement::Assign(place, rvalue) = stmt else {
                continue;
            };
            if !place.projection.is_empty() {
                continue;
            }
            let dest = place.local.index();
            if dest == 0 || dest <= body.arg_count || writes.get(dest) != Some(&1) {
                continue;
            }
            let dest_ty = &body.local_decls[dest].ty;
            match rvalue {
                Rvalue::Use(Operand::Copy(src)) if src.projection.is_empty() => {
                    let src_idx = src.local.index();
                    let stable = src_idx != 0
                        && src_idx != dest
                        && writes.get(src_idx).is_some_and(|count| *count <= 1)
                        && !killed_before_exit.get(src_idx).copied().unwrap_or(true)
                        && propagation_keeps_representation(&body.local_decls[src_idx].ty, dest_ty);
                    if stable {
                        copy_map.insert(dest, KnownValue::Local(src.local));
                    }
                }
                // A closure literal carries its captured operands (possibly moves): duplicating
                // it would duplicate those captures, so only capture-free constants propagate.
                // A constant of a polymorphic type (a generic global function, whose type
                // mentions its own type parameters) is not propagated either: the typed backend
                // instantiates it through the local it is stored in (rustc infers the type
                // arguments from that local's uses), and a copy left behind in a dead local
                // could not be inferred (rustc E0283, bug W_A_vectors_8).
                Rvalue::Use(Operand::Constant(c))
                    if c.literal.capture_operands().is_none()
                        && !contains_type_param(&c.ty)
                        && propagation_keeps_representation(&c.ty, dest_ty) =>
                {
                    copy_map.insert(dest, KnownValue::Constant(c.clone()));
                }
                _ => {}
            }
        }
    }

    // Resolve chains: if A = B and B = C, then A = C
    let mut resolved = HashMap::new();
    for &local in copy_map.keys() {
        let final_value = resolve_chain(local, &copy_map);
        resolved.insert(local, final_value);
    }

    resolved
}

/// Whether uses of a local of type `dest_ty` may be replaced by a value of type `src_ty`. An
/// assignment between a stuck type (a type computed at run time, `MirType::is_stuck_type`) and a
/// known type changes the value's representation (the typed backend boxes or unboxes it, and a
/// large elimination routes an alternative that is never taken through a stuck temporary,
/// docs/spec/mir/typing.md "Types Computed at Run Time"): propagating across it would assign a
/// value to a place of an unrelated type.
fn propagation_keeps_representation(src_ty: &MirType, dest_ty: &MirType) -> bool {
    (!contains_stuck_type(src_ty) && !contains_stuck_type(dest_ty)) || src_ty == dest_ty
}

fn contains_stuck_type(ty: &MirType) -> bool {
    match ty {
        MirType::Opaque { .. } => ty.is_stuck_type(),
        MirType::Adt(_, args) => args.iter().any(contains_stuck_type),
        MirType::Ref(_, inner, _)
        | MirType::RawPtr(inner, _)
        | MirType::InteriorMutable(inner, _) => contains_stuck_type(inner),
        MirType::Fn(_, _, args, ret)
        | MirType::FnItem(_, _, _, args, ret)
        | MirType::Closure(_, _, _, args, ret) => {
            args.iter().any(contains_stuck_type) || contains_stuck_type(ret)
        }
        MirType::Unit | MirType::Bool | MirType::Nat | MirType::Param(_) => false,
    }
}

fn contains_type_param(ty: &MirType) -> bool {
    match ty {
        MirType::Param(_) => true,
        MirType::Adt(_, args) => args.iter().any(contains_type_param),
        MirType::Ref(_, inner, _)
        | MirType::RawPtr(inner, _)
        | MirType::InteriorMutable(inner, _) => contains_type_param(inner),
        MirType::Fn(_, _, args, ret)
        | MirType::FnItem(_, _, _, args, ret)
        | MirType::Closure(_, _, _, args, ret) => {
            args.iter().any(contains_type_param) || contains_type_param(ret)
        }
        MirType::Unit | MirType::Bool | MirType::Nat | MirType::Opaque { .. } => false,
    }
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
                                // The source has a Copy type (see `build_copy_map`), so the
                                // replacement is always a copy, never a move of the source.
                                *op = Operand::Copy(crate::Place::from(*src));
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
        // A borrowed callee is never redirected to another local: that would change which
        // place the loan is taken on.
        CallOperand::Borrow(_, _) => false,
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

    fn nat_ty() -> MirType {
        MirType::Nat
    }

    /// Regression (p23): `_2 = move _1; _0 = move _2` must not become `_0 = move _1` while the
    /// original move stays in place (that moved `_1` twice and made a typed binary panic).
    #[test]
    fn test_move_is_not_propagated() {
        let mut body = Body::new(1);
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
                    Rvalue::Use(Operand::Move(Place::from(Local(1)))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Move(Place::from(Local(2)))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        optimize(&mut body);

        match &body.basic_blocks[0].statements[1] {
            Statement::Assign(_, Rvalue::Use(Operand::Move(place))) => {
                assert_eq!(place.local.index(), 2, "move of _2 must stay a move of _2");
            }
            other => panic!("unexpected statement after optimize: {:?}", other),
        }
    }

    /// A copy whose source is written again later is not propagated (flow-insensitive map).
    #[test]
    fn test_copy_of_rewritten_source_is_not_propagated() {
        let mut body = Body::new(0);
        for name in ["_0", "_1", "_2"] {
            body.local_decls
                .push(LocalDecl::new(nat_ty(), Some(name.to_string())));
        }
        let nat = |n| {
            Rvalue::Use(Operand::Constant(Box::new(Constant {
                literal: Literal::Nat(n),
                ty: nat_ty(),
            })))
        };
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(Place::from(Local(1)), nat(1)),
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
                ),
                Statement::Assign(Place::from(Local(1)), nat(2)),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place::from(Local(2)))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        optimize(&mut body);

        match &body.basic_blocks[0].statements[3] {
            Statement::Assign(_, Rvalue::Use(Operand::Copy(place))) => {
                assert_eq!(
                    place.local.index(),
                    2,
                    "_0 must still read _2 (== 1), not _1 (== 2)"
                );
            }
            other => panic!("unexpected statement after optimize: {:?}", other),
        }
    }

    /// A borrowed callee is never redirected to the local it was copied from.
    #[test]
    fn test_borrowed_callee_is_not_redirected() {
        let mut body = Body::new(1);
        for name in ["_0", "_1", "_2"] {
            body.local_decls
                .push(LocalDecl::new(dummy_ty(), Some(name.to_string())));
        }
        body.basic_blocks.push(BasicBlockData {
            statements: vec![Statement::Assign(
                Place::from(Local(2)),
                Rvalue::Use(Operand::Copy(Place::from(Local(1)))),
            )],
            terminator: Some(Terminator::Call {
                func: CallOperand::Borrow(crate::BorrowKind::Shared, Place::from(Local(2))),
                args: vec![],
                destination: Place::from(Local(0)),
                target: None,
            }),
        });

        optimize(&mut body);

        match &body.basic_blocks[0].terminator {
            Some(Terminator::Call {
                func: CallOperand::Borrow(_, place),
                ..
            }) => assert_eq!(place.local.index(), 2),
            other => panic!("unexpected terminator after optimize: {:?}", other),
        }
    }

    /// A closure literal that moves a capture is not duplicated into its uses.
    #[test]
    fn test_closure_constant_is_not_propagated() {
        let mut body = Body::new(1);
        for name in ["_0", "_1", "_2"] {
            body.local_decls
                .push(LocalDecl::new(dummy_ty(), Some(name.to_string())));
        }
        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(2)),
                    Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Closure(0, vec![Operand::Move(Place::from(Local(1)))]),
                        ty: dummy_ty(),
                    }))),
                ),
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Move(Place::from(Local(2)))),
                ),
            ],
            terminator: Some(Terminator::Return),
        });

        optimize(&mut body);

        match &body.basic_blocks[0].statements[1] {
            Statement::Assign(_, Rvalue::Use(Operand::Move(place))) => {
                assert_eq!(place.local.index(), 2);
            }
            other => panic!("closure literal was propagated: {:?}", other),
        }
    }
}
