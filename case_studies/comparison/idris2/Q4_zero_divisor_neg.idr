-- Q4 (negative: a wrong proof). The `safeDiv` of Q4_erasure.idr called with the divisor 0 and
-- the proof `ItIsSucc`, which only proves `NonZero (S n)`: a type error.
-- Compare ../lrl/q04_erasure__zero_divisor.lrl.
module Main

import Data.Nat

safeDiv : Nat -> (b : Nat) -> (0 _ : NonZero b) -> Nat
safeDiv a b _ = div a b

main : IO ()
main = putStrLn ("safeDiv 10 0 = " ++ show (safeDiv 10 0 ItIsSucc))   -- CHANGED: divisor 0
