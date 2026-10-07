-- Q4 (negative: forged evidence). Identical to the `safeDiv` of Q4_erasure.idr; the caller
-- does not prove `NonZero 0` (there is no proof) but forges the quantity-0 argument with
-- `believe_me`, which the type checker accepts in ordinary (even `%default total`) code.
-- The program compiles; nothing checks the forged argument. When it runs, `div` on Nat (the
-- `Integral Nat` instance in Data.Nat) calls the partial function `Data.Nat.divNat`, which has
-- no clause for a zero divisor, and the program stops with an error.
-- Compare ../lrl/q04_erasure__forge.lrl (rejected: a total definition may not depend on an
-- axiom) and ../rust/q04_zero_sized_proofs.rs --cfg forge (rejected: private constructor).
module Main

import Data.Nat

%default total

safeDiv : Nat -> (b : Nat) -> (0 _ : NonZero b) -> Nat
safeDiv a b _ = div a b

main : IO ()
main = putStrLn ("safeDiv 10 0 (forged proof) = " ++ show (safeDiv 10 0 (believe_me ())))
