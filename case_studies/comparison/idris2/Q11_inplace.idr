-- Q11. In-place update of an unshared structure.
--
-- (1) `Data.Linear.Array` (package `contrib`): a `LinArray` is a linear handle to a
--     mutable `IOArray`. `write` takes the handle with quantity 1 and returns the same
--     handle, so the old version can never be observed (Q11_array_reuse_neg.idr) and the
--     write is a destructive update. `revInPlace` reverses an 8-element array by swaps.
--     Evidence (see run_lean_idris.sh): in the `--dumpcases` output `write` returns its
--     input array after `Data.IOArray.writeArray`, whose Chez code calls `vector-set!`.
-- (2) `Data.Linear.LVect.reverse` (package `linear`) is a consuming reverse on a linear
--     length-indexed vector. Its compiled case tree (`--dumpcases`) constructs a new cons
--     cell (`%con [cons]`) for every element instead of updating the input in place.
module Main

import Data.Maybe
import Data.Linear.Array
import Data.Linear.LVect
import Data.Linear.Notation

fill : (1 arr : LinArray Int) -> Int -> Int -> LinArray Int
fill arr i n =
  if i >= n then arr
  else let (_ # arr) = write arr i i in fill arr (i + 1) n

swapAt : (1 arr : LinArray Int) -> Int -> Int -> LinArray Int
swapAt arr i j =
  let (mx # arr) = mread arr i
      (my # arr) = mread arr j
      (_ # arr) = write arr i (fromMaybe 0 my)
      (_ # arr) = write arr j (fromMaybe 0 mx)
  in arr

revInPlace : (1 arr : LinArray Int) -> Int -> Int -> LinArray Int
revInPlace arr i j =
  if i >= j then arr else revInPlace (swapAt arr i j) (i + 1) (j - 1)

toL : (1 _ : LVect n (!* Nat)) -> List Nat -> List Nat
toL []               acc = reverse acc
toL (MkBang x :: xs) acc = toL xs (x :: acc)

main : IO ()
main = do
  putStrLn ("LinArray reversed in place: " ++ show
    (newArray 8 (\arr => toIArray (revInPlace (fill arr 0 8) 0 7)
                                  (\ia => map (\k => fromMaybe 0 (read ia k)) [0 .. 7]))))
  putStrLn ("LVect.reverse: " ++ show
    (toL (Data.Linear.LVect.reverse [MkBang 1, MkBang 2, MkBang 3]) []))
