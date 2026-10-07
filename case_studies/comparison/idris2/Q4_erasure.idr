-- Q4. Are proofs and indices absent at run time? Evidence: the compiled case trees
-- written by `idris2 --dumpcases <file>` (the last intermediate form before Scheme).
--
-- (a) `safeDiv` takes a quantity-0 proof `NonZero b`: the compiled definition has two
--     arguments and the call site passes two.
-- (b) The length index of a user-defined `Vec` is an unbound implicit (quantity 0): a
--     cons cell has two fields (element and tail), and `push` takes two arguments.
-- (c) An index the program does need at run time must be bound with quantity omega
--     (`{n : Nat}`); `vlength` then receives it as an ordinary argument.
--     Using a quantity-0 index at run time is rejected (see Q4_erased_index_neg.idr).
-- `%noinline` keeps the three functions visible in the dump (otherwise they are inlined).
module Main

import Data.Nat

data Vec : Nat -> Type -> Type where
  Nil  : Vec Z a
  (::) : a -> Vec n a -> Vec (S n) a

%noinline
safeDiv : Nat -> (b : Nat) -> (0 _ : NonZero b) -> Nat
safeDiv a b _ = div a b

%noinline
push : a -> Vec n a -> Vec (S n) a
push x xs = x :: xs

%noinline
vlength : {n : Nat} -> Vec n a -> Nat
vlength _ = n

main : IO ()
main = do
  putStrLn ("safeDiv 10 2 = " ++ show (safeDiv 10 2 ItIsSucc))
  putStrLn ("vlength (push 1 [2, 3]) = " ++ show (vlength (push (the Nat 1) [2, 3])))
