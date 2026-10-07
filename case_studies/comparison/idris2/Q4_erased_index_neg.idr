-- Q4 (negative). A quantity-0 (erased) index cannot be used at run time.
module Main

data Vec : Nat -> Type -> Type where
  Nil  : Vec Z a
  (::) : a -> Vec n a -> Vec (S n) a

vlength : {0 n : Nat} -> Vec n a -> Nat
vlength _ = n
