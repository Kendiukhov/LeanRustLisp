#lang cur
;; Q3 (Cur): a machine-checked proof that reverse is an involution, with Cur's ntac tactic
;; library (the development follows the Lists chapter of Software Foundations, as in Cur's own
;; test suite). The theorems are checked when the module is compiled.
;;
;; Note (Racket 9.3 + cur 98f7218): `(by-intros l1 l2 ...)` followed by `(by-induction l1 ...)`
;; fails with "l1: unbound identifier in module", also in Cur's own test
;; cur-test/cur/tests/ntac/software-foundations/Lists.rkt; we therefore introduce one variable
;; at a time with `by-intro`.
;; Negative (self-contained copy): q03_reverse_involution_cur__buggy.rkt.
(require cur/stdlib/nat
         cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite)

(data NatList : 0 Type
  [nil : NatList]
  [cons : (-> Nat NatList NatList)])

(define/rec/match app : NatList [ys : NatList] -> NatList
  [nil => ys]
  [(cons h t) => (cons h (app t ys))])

(define/rec/match rev : NatList -> NatList
  [nil => nil]
  [(cons h t) => (app (rev t) (cons h nil))])

(define-theorem app-nil-r
  (∀ [l : NatList] (== NatList (app l nil) l))
  (by-intro l)
  (by-induction l #:as [() (h t IH)])
  reflexivity
  (by-rewrite IH)
  reflexivity)

(define-theorem app-assoc
  (∀ [l1 : NatList] [l2 : NatList] [l3 : NatList]
     (== NatList (app (app l1 l2) l3) (app l1 (app l2 l3))))
  (by-intro l1)
  (by-intro l2)
  (by-intro l3)
  (by-induction l1 #:as [() (h t IH)])
  reflexivity
  (by-rewrite IH)
  reflexivity)

(define-theorem rev-app-distr
  (∀ [l1 : NatList] [l2 : NatList]
     (== NatList (rev (app l1 l2)) (app (rev l2) (rev l1))))
  (by-intro l1)
  (by-intro l2)
  (by-induction l1 #:as [() (h t IH)])
  (by-rewrite app-nil-r)
  reflexivity
  (by-rewrite IH)
  (by-rewrite app-assoc)
  reflexivity)

(define-theorem rev-involutive
  (∀ [l : NatList] (== NatList (rev (rev l)) l))
  (by-intro l)
  (by-induction l #:as [() (h t IH)])
  reflexivity
  (by-rewrite rev-app-distr)
  (by-rewrite IH)
  reflexivity)

;; the module prints the normal form of (rev (rev [1 2 3]))
(rev (rev (cons 1 (cons 2 (cons 3 nil)))))
