/-!
Q4 (negative: a wrong proof). `safeDiv` asks for a proof that the divisor is positive; the
caller passes the divisor 0 and tries to prove `0 > 0` with `decide`: rejected (`decide` evaluates
the proposition to `false`). Compare `../lrl/q04_erasure__zero_divisor.lrl`.
-/

def safeDiv (a b : Nat) (_h : b > 0) : Nat := a / b

def useZero : Nat := safeDiv 10 0 (by decide)   -- CHANGED: divisor 0

def main : IO Unit :=
  IO.println s!"safeDiv 10 0 = {useZero}"
