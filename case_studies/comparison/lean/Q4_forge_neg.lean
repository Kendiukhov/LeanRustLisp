/-!
Q4 (negative: forged evidence). `safeDiv` asks for a proof that the divisor is positive; the
caller postulates one with an `axiom` instead of proving it, and divides by zero. Lean accepts
`axiom` declarations in ordinary code, and a computable definition may use a propositional axiom
(the proof is erased, so nothing has to be executed): the program compiles and runs.
(`#print axioms useForged` would list `forged`; nothing rejects the program.)
Compare `../lrl/q04_erasure__forge.lrl` (rejected: a total definition may not depend on an axiom)
and `../rust/q04_zero_sized_proofs.rs --cfg forge` (rejected: private constructor).
-/

def safeDiv (a b : Nat) (_h : b > 0) : Nat := a / b

axiom forged : (0 : Nat) > 0

def useForged : Nat := safeDiv 10 0 forged

def main : IO Unit :=
  IO.println s!"safeDiv 10 0 (forged proof) = {useForged}"
