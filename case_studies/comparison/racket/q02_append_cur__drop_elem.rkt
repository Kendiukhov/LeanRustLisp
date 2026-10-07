#lang cur
;; Q2 negative (Cur): an append whose cons case forgets the head element (returns the induction
;; hypothesis instead of (vcons ... x ih)). Self-contained copy of q02_append_cur.rkt with that
;; one change. Expected: type error (the case must have type (Vect A (s (plus k m)))).
(require cur/stdlib/nat cur/stdlib/sugar)

(data Vect : 1 (Π (A : (Type 0)) (Π (n : Nat) (Type 0)))
  [vnil : (Π (A : (Type 0)) (Vect A z))]
  [vcons : (Π (A : (Type 0)) (Π (n : Nat) (Π (x : A) (Π (xs : (Vect A n)) (Vect A (s n))))))])

(define append
  (λ (A : (Type 0)) (n : Nat) (m : Nat) (xs : (Vect A n)) (ys : (Vect A m))
    (new-elim xs
              (λ (k : Nat) (λ (vs : (Vect A k)) (Vect A (plus k m))))
              ys
              (λ (k : Nat) (λ (x : A) (λ (vs : (Vect A k)) (λ (ih : (Vect A (plus k m)))
                ih)))))))

(define two (vcons Nat 1 1 (vcons Nat 0 2 (vnil Nat))))
(define one (vcons Nat 0 3 (vnil Nat)))
(define (vect3 [v : (Vect Nat 3)]) v)

;; the module prints the normal form of the appended vector (elements 1, 2, 3)
(vect3 (append Nat 2 1 two one))
