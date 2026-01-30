import LRL.Syntax
import LRL.Reduction

namespace LRL

/-- Global environment context -/
structure Env where
  -- Map derived from constants to types/values...
  dummy : Unit -- Placeholder

/-- Local context (list of types for bound variables) -/
def Context := List Term

/-- Local lookup helper -/
def lookup {α} : List α -> Nat -> Option α
  | [], _ => none
  | x::_, 0 => some x
  | _::xs, n+1 => lookup xs n

/-- Typing relation: Γ ⊢ t : T -/
inductive Typing (env : Env) : Context -> Term -> Term -> Prop where
  | var (ctx : Context) (n : Nat) (ty : Term) :
      lookup ctx n = some ty ->
      Typing env ctx (Term.var n) (shift ty 0 (n + 1)) -- Need lift for DB indices

  | sort (ctx : Context) (l : Level) :
      Typing env ctx (Term.sort l) (Term.sort (Level.succ l))

  | app (ctx : Context) (f a A B : Term) :
      Typing env ctx f (Term.pi A B) ->
      Typing env ctx a A ->
      Typing env ctx (Term.app f a) (subst B 0 a)

  | lam (ctx : Context) (A t B : Term) (s : Level) :
      Typing env ctx A (Term.sort s) ->
      Typing env (A :: ctx) t B ->
      Typing env ctx (Term.lam A t) (Term.pi A B)

  | pi (ctx : Context) (A B : Term) (s1 s2 : Level) :
      Typing env ctx A (Term.sort s1) ->
      Typing env (A :: ctx) B (Term.sort s2) ->
      Typing env ctx (Term.pi A B) (Term.sort (Level.imax s1 s2))

  -- Conversion rule
  | conv (ctx : Context) (t A B : Term) :
      Typing env ctx t A ->
      Typing env ctx B (Term.sort (Level.zero)) -> -- B is a type
      Conv A B ->
      Typing env ctx t B

  -- Note: lift needs to be defined in Reduction or Syntax, I used it above.
  -- assuming 'lift' matches 'shift' logic.

end LRL
