-- Q2 (negative). An `append` that drops an element cannot be given the sum type.
module Main

data Vec : Nat -> Type -> Type where
  Nil  : Vec Z a
  (::) : a -> Vec n a -> Vec (S n) a

append : Vec n a -> Vec m a -> Vec (n + m) a
append []        ys = ys
append (_ :: xs) ys = append xs ys    -- bug: the element is dropped
