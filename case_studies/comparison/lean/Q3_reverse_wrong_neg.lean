/-!
Q3 (negative control). A false law, `rev xs = xs`, attempted by the same kind of
induction, is rejected: after `simp [rev, ih]` the `cons` goal `xs ++ [x] = x :: xs` remains.
-/

def rev : List α → List α
  | []      => []
  | x :: xs => rev xs ++ [x]

theorem rev_id (xs : List α) : rev xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rev, ih]
