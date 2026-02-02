use crate::Body;
use crate::types::{MirType, IMKind};

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
        // Check local declarations for RefCell-like types
        for (i, decl) in self.body.local_decls.iter().enumerate() {
            if self.contains_refcell(&decl.ty) {
                self.errors.push(format!(
                    "Local {:?} uses RefCell-like interior mutability which may panic. Forbidden in panic-free profile.",
                    i
                ));
            }
        }
    }

    fn contains_refcell(&self, ty: &MirType) -> bool {
        match ty {
            MirType::InteriorMutable(inner, kind) => {
                if matches!(kind, IMKind::RefCell) {
                    true
                } else {
                    self.contains_refcell(inner)
                }
            },
            MirType::Ref(_, inner, _) => self.contains_refcell(inner),
            MirType::Adt(_, args) => args.iter().any(|a| self.contains_refcell(a)),
            MirType::Fn(args, ret) => args.iter().any(|a| self.contains_refcell(a)) || self.contains_refcell(ret),
            MirType::RawPtr(inner, _) => self.contains_refcell(inner),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::LocalDecl;
    use crate::types::{MirType, IMKind};

    #[test]
    fn test_rejects_refcell() {
        let mut body = Body::new(0);
        let refcell_ty = MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell);
        body.local_decls.push(LocalDecl::new(refcell_ty, None));

        let mut linter = PanicFreeLinter::new(&body);
        linter.check();
        assert!(!linter.errors.is_empty());
        assert!(linter.errors[0].contains("RefCell-like"));
    }

    #[test]
    fn test_accepts_mutex() {
        let mut body = Body::new(0);
        let mutex_ty = MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::Mutex);
        body.local_decls.push(LocalDecl::new(mutex_ty, None));

        let mut linter = PanicFreeLinter::new(&body);
        linter.check();
        assert!(linter.errors.is_empty());
    }
}
