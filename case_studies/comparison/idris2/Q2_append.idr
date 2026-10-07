-- Q2 (positive). `append` whose result length is the sum of the input lengths.
-- `plus` recurses on its first argument, so `S k + m` reduces to `S (k + m)` and the
-- cons clause type-checks without a cast. `Data.Vect.(++)` has the same type.
module Main

import Data.Vect

data Vec : Nat -> Type -> Type where
  Nil  : Vec Z a
  (::) : a -> Vec n a -> Vec (S n) a

total
append : Vec n a -> Vec m a -> Vec (n + m) a
append []        ys = ys
append (x :: xs) ys = x :: append xs ys

total
toList : Vec n a -> List a
toList []        = []
toList (x :: xs) = x :: toList xs

-- Checked statically: 2 + 3 = 5.
five : Vec 5 Nat
five = append [1, 2] [3, 4, 5]

fiveLib : Vect 5 Nat
fiveLib = [1, 2] ++ [3, 4, 5]

main : IO ()
main = do
  putStrLn ("append     = " ++ show (Main.toList five))
  putStrLn ("Vect (++)  = " ++ show fiveLib)
