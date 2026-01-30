namespace LRL

/-- Universe levels -/
inductive Level where
  | zero : Level
  | succ : Level -> Level
  | max  : Level -> Level -> Level
  | imax : Level -> Level -> Level
  | param : String -> Level
  deriving Repr, DecidableEq

/-- The core terms of the calculus, using de Bruijn indices. -/
inductive Term where
  | var  : Nat -> Term                  -- Bound variable (de Bruijn index)
  | sort : Level -> Term                -- Universe
  | const : String -> List Level -> Term -- Constant (global definition)
  | app  : Term -> Term -> Term         -- Application
  | lam  : Term -> Term -> Term         -- Lambda abstraction (type, body)
  | pi   : Term -> Term -> Term         -- Pi type (binder type, body)
  | letE : Term -> Term -> Term -> Term -- Let binding (type, value, body)
  deriving Repr, DecidableEq

end LRL
