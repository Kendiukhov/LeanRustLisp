/-!
Q1 (negative, core library). `Vector.head` of an empty core `Vector` must be rejected:
`Vector.head` requires an instance `NeZero n`, and there is none for `n = 0`.
-/

def bad : Nat := (#v[] : Vector Nat 0).head
