-- Q3 (positive). Compiler-checked proofs that reverse is an involution.
--
-- (1) Lists: `rev` is a user-defined (quadratic) list reverse; `revRev` is proved by
--     induction with one auxiliary lemma.
-- (2) Length-indexed vectors: `vrev : Vect n a -> Vect n a`, defined with the library's
--     `Data.Vect.snoc`; `vrevRev` is proved the same way.
-- (3) The base library proves the law for its own list `reverse`
--     (`Data.List.reverseInvolutive`), restated below.
-- `%default total`: every definition, including the proofs, is checked total.
module Main

import Data.List
import Data.Vect

%default total

rev : List a -> List a
rev []        = []
rev (x :: xs) = rev xs ++ [x]

revDistrib : (xs, ys : List a) -> rev (xs ++ ys) = rev ys ++ rev xs
revDistrib []        ys = sym (appendNilRightNeutral (rev ys))
revDistrib (x :: xs) ys =
  rewrite revDistrib xs ys in sym (appendAssociative (rev ys) (rev xs) [x])

revRev : (xs : List a) -> rev (rev xs) = xs
revRev []        = Refl
revRev (x :: xs) = rewrite revDistrib (rev xs) [x] in rewrite revRev xs in Refl

vrev : Vect n a -> Vect n a
vrev []        = []
vrev (x :: xs) = snoc (vrev xs) x

vrevSnoc : (xs : Vect n a) -> (y : a) -> vrev (snoc xs y) = y :: vrev xs
vrevSnoc []        y = Refl
vrevSnoc (x :: xs) y = rewrite vrevSnoc xs y in Refl

vrevRev : (xs : Vect n a) -> vrev (vrev xs) = xs
vrevRev []        = Refl
vrevRev (x :: xs) = rewrite vrevSnoc (vrev xs) x in rewrite vrevRev xs in Refl

libRevRev : (xs : List a) -> reverse (reverse xs) = xs
libRevRev = reverseInvolutive

main : IO ()
main = do
  putStrLn ("rev (rev [1, 2, 3]) = " ++ show (rev (rev [the Nat 1, 2, 3])))
  putStrLn ("vrev [1, 2, 3] = " ++ show (vrev [the Nat 1, 2, 3]))
