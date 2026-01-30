import LRL.Typing

namespace LRL

-- Example: Identity function identity \x. x
def idTerm : Term := Term.lam (Term.sort (Level.zero)) (Term.var 0)

-- Proving it is well typed would require constructing the derivation tree.
-- logical verification would happen by Lean kernel when this file is compiled.

end LRL
