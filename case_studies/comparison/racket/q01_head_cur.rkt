#lang cur
;; Q1 (Cur, a dependently typed language implemented with Turnstile+ macros on Racket):
;; a length-indexed vector and a total `head`. `head` takes a (Vect A (s n)), so it is only
;; applicable to non-empty vectors. It is written with the dependent eliminator `new-elim`;
;; the motive computes the result type from the index (HeadT A z = Unit, HeadT A (s k) = A),
;; so the impossible nil case returns the trivial value `tt` instead of needing a default.
;; Negatives (self-contained copies): q01_head_cur__empty.rkt, q01_head_cur__any_length.rkt.
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

;; the module prints the normal form of this expression: (s (z)), i.e. 1
(head Nat 2 v3)
