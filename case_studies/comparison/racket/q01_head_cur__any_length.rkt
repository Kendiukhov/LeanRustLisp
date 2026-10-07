#lang cur
;; Q1 negative (Cur): a `head` that accepts vectors of any length (type (Vect A n) -> A).
;; Self-contained copy of q01_head_cur.rkt with only `head` changed. Expected: type error in
;; the nil case.
(require cur/stdlib/nat cur/stdlib/sugar)

(data Unit : 0 Type [tt : Unit])

(data Vect : 1 (Π (A : (Type 0)) (Π (n : Nat) (Type 0)))
  [vnil : (Π (A : (Type 0)) (Vect A z))]
  [vcons : (Π (A : (Type 0)) (Π (n : Nat) (Π (x : A) (Π (xs : (Vect A n)) (Vect A (s n))))))])

;; large elimination: a type computed by recursion on the index
(define HeadT
  (λ (A : (Type 0)) (k : Nat)
    (new-elim k (λ (k : Nat) (Type 0)) Unit (λ (k : Nat) (λ (ih : (Type 0)) A)))))

;; a head for vectors of ANY length, with the constant motive A: the nil case has no element
;; of type A to return (returning the empty vector itself is a type error)
(define head
  (λ (A : (Type 0)) (n : Nat) (v : (Vect A n))
    (new-elim v
              (λ (k : Nat) (λ (vs : (Vect A k)) A))
              (vnil A)
              (λ (k : Nat) (λ (x : A) (λ (xs : (Vect A k)) (λ (ih : A) x)))))))

(define v3 (vcons Nat 2 1 (vcons Nat 1 2 (vcons Nat 0 3 (vnil Nat)))))

(head Nat 3 v3)
