use crate::types::MirType;
use crate::{Body, Constant, Literal, Operand, Rvalue, Statement};

/// Erase computationally irrelevant values (Prop) from the MIR body.
/// Replaces assignments to Prop-typed locals with a dummy unit value.
pub fn erase_proofs(body: &mut Body) {
    // 1. Identify Prop locals
    // They are already marked in `body.local_decls` via `is_prop`.

    // 2. Iterate statements and erase assignments
    for block in &mut body.basic_blocks {
        for stmt in &mut block.statements {
            if let Statement::Assign(place, rvalue) = stmt {
                // Check if destination is Prop
                let decl_idx = place.local.index();
                if body.local_decls[decl_idx].is_prop {
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
        if let Some(crate::Terminator::SwitchInt { discr, targets }) = terminator {
            // Check if discriminant is Prop
            let is_prop_discr = match discr {
                Operand::Copy(p) | Operand::Move(p) => {
                    // Get LocalDecl
                    body.local_decls[p.local.index()].is_prop
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
        } else if let Some(crate::Terminator::Call {
            destination,
            target,
            ..
        }) = terminator
        {
            let is_prop = body.local_decls[destination.local.index()].is_prop;

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
    }
}
