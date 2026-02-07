use crate::types::{AdtId, MirType};
use crate::{Body, Constant, Literal, Operand, Rvalue, Statement, Terminator};
use std::collections::HashSet;

fn collect_prop_adts(body: &Body) -> HashSet<AdtId> {
    let mut adts = HashSet::new();
    for decl in &body.local_decls {
        if !decl.is_prop {
            continue;
        }
        if let MirType::Adt(adt_id, _) = &decl.ty {
            adts.insert(adt_id.clone());
        }
    }
    adts
}

fn is_function_like(ty: &MirType) -> bool {
    matches!(
        ty,
        MirType::Fn(_, _, _, _) | MirType::FnItem(_, _, _, _, _) | MirType::Closure(_, _, _, _, _)
    )
}

fn should_erase_prop_value(ty: &MirType, is_prop: bool) -> bool {
    is_prop && !is_function_like(ty)
}

fn erase_runtime_type(ty: &MirType, prop_adts: &HashSet<AdtId>) -> MirType {
    match ty {
        MirType::Adt(adt_id, args) => {
            if prop_adts.contains(adt_id) {
                MirType::Unit
            } else {
                MirType::Adt(
                    adt_id.clone(),
                    args.iter()
                        .map(|arg| erase_runtime_type(arg, prop_adts))
                        .collect(),
                )
            }
        }
        MirType::Ref(region, inner, mutability) => MirType::Ref(
            *region,
            Box::new(erase_runtime_type(inner, prop_adts)),
            *mutability,
        ),
        MirType::Fn(kind, regions, args, ret) => MirType::Fn(
            *kind,
            regions.clone(),
            args.iter()
                .map(|arg| erase_runtime_type(arg, prop_adts))
                .collect(),
            Box::new(erase_runtime_type(ret, prop_adts)),
        ),
        MirType::FnItem(def_id, kind, regions, args, ret) => MirType::FnItem(
            *def_id,
            *kind,
            regions.clone(),
            args.iter()
                .map(|arg| erase_runtime_type(arg, prop_adts))
                .collect(),
            Box::new(erase_runtime_type(ret, prop_adts)),
        ),
        MirType::Closure(kind, self_region, regions, args, ret) => MirType::Closure(
            *kind,
            *self_region,
            regions.clone(),
            args.iter()
                .map(|arg| erase_runtime_type(arg, prop_adts))
                .collect(),
            Box::new(erase_runtime_type(ret, prop_adts)),
        ),
        MirType::RawPtr(inner, mutability) => {
            MirType::RawPtr(Box::new(erase_runtime_type(inner, prop_adts)), *mutability)
        }
        MirType::InteriorMutable(inner, kind) => {
            MirType::InteriorMutable(Box::new(erase_runtime_type(inner, prop_adts)), *kind)
        }
        MirType::Unit
        | MirType::Bool
        | MirType::Nat
        | MirType::Opaque { .. }
        | MirType::IndexTerm(_)
        | MirType::Param(_) => ty.clone(),
    }
}

fn erase_constant_type(constant: &mut Constant, prop_adts: &HashSet<AdtId>) {
    constant.ty = erase_runtime_type(&constant.ty, prop_adts);
}

fn erase_operand_types(op: &mut Operand, prop_adts: &HashSet<AdtId>) {
    if let Operand::Constant(constant) = op {
        erase_constant_type(constant, prop_adts);
    }
}

fn erase_call_operand_types(op: &mut crate::CallOperand, prop_adts: &HashSet<AdtId>) {
    if let crate::CallOperand::Operand(operand) = op {
        erase_operand_types(operand, prop_adts);
    }
}

/// Erase computationally irrelevant values (Prop) from the MIR body.
/// Replaces assignments to Prop-typed locals with a dummy unit value.
pub fn erase_proofs(body: &mut Body) {
    let prop_adts = collect_prop_adts(body);

    // Erase Prop-typed runtime signatures before statement rewriting so that all
    // generated runtime call signatures stay consistent with value erasure.
    for decl in &mut body.local_decls {
        if should_erase_prop_value(&decl.ty, decl.is_prop) {
            decl.ty = MirType::Unit;
        } else {
            decl.ty = erase_runtime_type(&decl.ty, &prop_adts);
        }
        decl.is_copy = decl.ty.is_copy();
        decl.closure_captures = decl
            .closure_captures
            .iter()
            .map(|ty| erase_runtime_type(ty, &prop_adts))
            .collect();
    }

    // 1. Identify Prop locals
    // They are already marked in `body.local_decls` via `is_prop`.

    // 2. Iterate statements and erase assignments
    for block in &mut body.basic_blocks {
        for stmt in &mut block.statements {
            if let Statement::Assign(place, rvalue) = stmt {
                if let Rvalue::Use(Operand::Constant(constant)) = rvalue {
                    erase_constant_type(constant, &prop_adts);
                }
                // Check if destination is Prop
                let decl_idx = place.local.index();
                if should_erase_prop_value(
                    &body.local_decls[decl_idx].ty,
                    body.local_decls[decl_idx].is_prop,
                ) {
                    // It's a proof! Erase the computation.
                    *rvalue = Rvalue::Use(Operand::Constant(Box::new(Constant {
                        literal: Literal::Unit,
                        ty: MirType::Unit,
                    })));
                }
            }
        }

        // 3. Handle Terminators
        let terminator = &mut block.terminator;
        if let Some(term) = terminator {
            match term {
                Terminator::SwitchInt { discr, targets } => {
                    erase_operand_types(discr, &prop_adts);
                    // Check if discriminant is Prop
                    let is_prop_discr = match discr {
                        Operand::Copy(p) | Operand::Move(p) => {
                            // Get LocalDecl
                            let decl = &body.local_decls[p.local.index()];
                            should_erase_prop_value(&decl.ty, decl.is_prop)
                        }
                        Operand::Constant(_) => false, // Constants (Nat/Bool) are data? Or Prop constant?
                                                       // Constant(Unit) is Prop value.
                    };

                    if is_prop_discr {
                        // Erase the Switch.
                        if !targets.targets.is_empty() {
                            let target = targets.targets[0];
                            *terminator = Some(crate::Terminator::Goto { target });
                        } else {
                            // Empty switch (e.g. False elim)
                            *terminator = Some(crate::Terminator::Unreachable);
                        }
                    }
                }
                Terminator::Call {
                    func,
                    args,
                    destination,
                    target,
                } => {
                    erase_call_operand_types(func, &prop_adts);
                    for arg in args.iter_mut() {
                        erase_operand_types(arg, &prop_adts);
                    }

                    let dest_decl = &body.local_decls[destination.local.index()];
                    let is_prop = should_erase_prop_value(&dest_decl.ty, dest_decl.is_prop);

                    // Check if destination is Prop
                    if is_prop {
                        // Erase the Call!
                        // We must simulate the return of Unit.
                        if let Some(target) = *target {
                            // 1. Assign Unit to destination
                            block.statements.push(Statement::Assign(
                                destination.clone(),
                                Rvalue::Use(Operand::Constant(Box::new(Constant {
                                    literal: Literal::Unit,
                                    ty: MirType::Unit,
                                }))),
                            ));

                            // 2. Goto target
                            *terminator = Some(crate::Terminator::Goto { target });
                        }
                        // If target is None, the call diverges. Keep it.
                    }
                }
                Terminator::Return | Terminator::Goto { .. } | Terminator::Unreachable => {}
            }
        }
    }
}
