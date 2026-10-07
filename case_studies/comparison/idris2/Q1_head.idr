-- Q1 (positive). Length-indexed vector with a total `head`.
-- `vhead` has a single clause: the index `S n` rules out `Nil`, and Idris 2's coverage
-- checker accepts the function as total. The library's `Data.Vect.head` has the same type.
-- The case tree dumped with `--dumpcases` has one branch and no default/error branch.
module Main

import Data.Vect

data Vec : Nat -> Type -> Type where
  Nil  : Vec Z a
  (::) : a -> Vec n a -> Vec (S n) a

total
vhead : Vec (S n) a -> a
vhead (x :: _) = x

main : IO ()
main = do
  putStrLn ("vhead [1, 2] = " ++ show (vhead [1, 2]))
  putStrLn ("Data.Vect.head [7, 8, 9] = " ++ show (head [7, 8, 9]))
