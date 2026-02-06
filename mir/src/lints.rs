use crate::types::MirType;
use crate::{
    Body, CallOperand, Operand, Place, PlaceElem, RuntimeCheckKind, Rvalue, Statement, Terminator,
};

pub struct PanicFreeLinter<'a> {
    body: &'a Body,
    pub errors: Vec<String>,
}

impl<'a> PanicFreeLinter<'a> {
    pub fn new(body: &'a Body) -> Self {
        Self {
            body,
            errors: Vec::new(),
        }
    }

    pub fn check(&mut self) {
        // Check local declarations for interior mutability types
        for (i, decl) in self.body.local_decls.iter().enumerate() {
            if self.contains_interior_mutability(&decl.ty) {
                self.errors.push(format!(
                    "Local {:?} uses interior mutability (RefCell/Mutex/Atomic). Forbidden in panic-free profile.",
                    i
                ));
            }
        }

        let mut index_error_emitted = false;
        let mut borrow_error_emitted = false;

        // Check statements for indexing and borrow axioms
        for bb in &self.body.basic_blocks {
            for stmt in &bb.statements {
                match stmt {
                    Statement::RuntimeCheck(RuntimeCheckKind::BoundsCheck { .. }) => {
                        if !index_error_emitted {
                            self.errors.push(
                                "Indexing requires a bounds check and may panic. Forbidden in panic-free profile."
                                    .to_string(),
                            );
                            index_error_emitted = true;
                        }
                    }
                    Statement::Assign(_, Rvalue::Ref(_, _)) => {
                        if !borrow_error_emitted {
                            self.errors.push(
                                "Borrowing via borrow_shared/borrow_mut is forbidden in panic-free profile."
                                    .to_string(),
                            );
                            borrow_error_emitted = true;
                        }
                    }
                    Statement::Assign(place, rvalue) => {
                        if !index_error_emitted
                            && (place_has_index(place) || rvalue_has_index(rvalue))
                        {
                            self.errors.push(
                                "Indexing requires a bounds check and may panic. Forbidden in panic-free profile."
                                    .to_string(),
                            );
                            index_error_emitted = true;
                        }
                    }
                    _ => {}
                }
            }

            if !index_error_emitted {
                if let Some(terminator) = &bb.terminator {
                    if terminator_has_index(terminator) {
                        self.errors.push(
                            "Indexing requires a bounds check and may panic. Forbidden in panic-free profile."
                                .to_string(),
                        );
                        index_error_emitted = true;
                    }
                }
            }
        }
    }

    fn contains_interior_mutability(&self, ty: &MirType) -> bool {
        match ty {
            MirType::InteriorMutable(_, _) => true,
            MirType::Ref(_, inner, _) => self.contains_interior_mutability(inner),
            MirType::Adt(_, args) => args.iter().any(|a| self.contains_interior_mutability(a)),
            MirType::Fn(_, _, args, ret)
            | MirType::FnItem(_, _, _, args, ret)
            | MirType::Closure(_, _, _, args, ret) => {
                args.iter().any(|a| self.contains_interior_mutability(a))
                    || self.contains_interior_mutability(ret)
            }
            MirType::RawPtr(inner, _) => self.contains_interior_mutability(inner),
            _ => false,
        }
    }
}

fn place_has_index(place: &Place) -> bool {
    place
        .projection
        .iter()
        .any(|elem| matches!(elem, PlaceElem::Index(_)))
}

fn operand_has_index(operand: &Operand) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_has_index(place),
        Operand::Constant(_) => false,
    }
}

fn call_operand_has_index(operand: &CallOperand) -> bool {
    match operand {
        CallOperand::Borrow(_, place) => place_has_index(place),
        CallOperand::Operand(op) => operand_has_index(op),
    }
}

fn rvalue_has_index(rvalue: &Rvalue) -> bool {
    match rvalue {
        Rvalue::Use(operand) => operand_has_index(operand),
        Rvalue::Ref(_, place) => place_has_index(place),
        Rvalue::Discriminant(place) => place_has_index(place),
    }
}

fn terminator_has_index(terminator: &Terminator) -> bool {
    match terminator {
        Terminator::Return | Terminator::Goto { .. } | Terminator::Unreachable => false,
        Terminator::SwitchInt { discr, .. } => operand_has_index(discr),
        Terminator::Call {
            func,
            args,
            destination,
            ..
        } => {
            call_operand_has_index(func)
                || args.iter().any(operand_has_index)
                || place_has_index(destination)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{IMKind, MirType};
    use crate::LocalDecl;

    #[test]
    fn test_rejects_refcell() {
        let mut body = Body::new(0);
        let refcell_ty = MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell);
        body.local_decls.push(LocalDecl::new(refcell_ty, None));

        let mut linter = PanicFreeLinter::new(&body);
        linter.check();
        assert!(!linter.errors.is_empty());
        assert!(linter.errors[0].contains("interior mutability"));
    }

    #[test]
    fn test_rejects_mutex() {
        let mut body = Body::new(0);
        let mutex_ty = MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::Mutex);
        body.local_decls.push(LocalDecl::new(mutex_ty, None));

        let mut linter = PanicFreeLinter::new(&body);
        linter.check();
        assert!(!linter.errors.is_empty());
    }
}
