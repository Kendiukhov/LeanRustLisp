#lang cur
;; Q2 (Cur): append on length-indexed vectors, with the type
;;   (Π A n m (Vect A n) (Vect A m) (Vect A (plus n m)))
;; written with the dependent eliminator (the same shape as Cur's own test
;; cur-test/cur/tests/vector-append.rkt). `vect3` only accepts a (Vect Nat 3), so applying it
;; to the result checks that (plus 2 1) reduces to 3.
;; Negatives (self-contained copies): q02_append_cur__wrong_len.rkt, q02_append_cur__drop_elem.rkt.
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
                (vcons A (plus k m) x ih))))))))

(define two (vcons Nat 1 1 (vcons Nat 0 2 (vnil Nat))))
(define one (vcons Nat 0 3 (vnil Nat)))
(define (vect3 [v : (Vect Nat 3)]) v)

;; the module prints the normal form of the appended vector (elements 1, 2, 3)
(vect3 (append Nat 2 1 two one))
