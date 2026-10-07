-- Q3 (negative control). A false "law" is rejected.
module Main

rev : List a -> List a
rev []        = []
rev (x :: xs) = rev xs ++ [x]

revId : (xs : List a) -> rev xs = xs
revId []        = Refl
revId (x :: xs) = rewrite revId xs in Refl
