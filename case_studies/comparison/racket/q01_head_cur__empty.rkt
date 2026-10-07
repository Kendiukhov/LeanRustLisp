#lang cur
;; Q1 negative (Cur): head of the empty vector. Self-contained copy of q01_head_cur.rkt whose
;; last line applies head to (vnil Nat). Expected: type error (Vect Nat z is not Vect Nat (s z)).
(require cur/stdlib/nat cur/stdlib/sugar)

(data Unit : 0 Type [tt : Unit])

(data Vect : 1 (Π (A : (Type 0)) (Π (n : Nat) (Type 0)))
  [vnil : (Π (A : (Type 0)) (Vect A z))]
  [vcons : (Π (A : (Type 0)) (Π (n : Nat) (Π (x : A) (Π (xs : (Vect A n)) (Vect A (s n))))))])

;; large elimination: a type computed by recursion on the index
(define HeadT
  (λ (A : (Type 0)) (k : Nat)
    (new-elim k (λ (k : Nat) (Type 0)) Unit (λ (k : Nat) (λ (ih : (Type 0)) A)))))

(define head
  (λ (A : (Type 0)) (n : Nat) (v : (Vect A (s n)))
    (new-elim v
              (λ (k : Nat) (λ (vs : (Vect A k)) (HeadT A k)))
              tt
              (λ (k : Nat) (λ (x : A) (λ (xs : (Vect A k)) (λ (ih : (HeadT A k)) x)))))))

(define v3 (vcons Nat 2 1 (vcons Nat 1 2 (vcons Nat 0 3 (vnil Nat)))))

(head Nat z (vnil Nat))
