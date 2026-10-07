#lang typed/racket/base
;; Q4 (Typed Racket): an evidence token for "the divisor is non-zero". Racket has no
;; erasure of such values: the token is an ordinary run-time value (a struct instance)
;; that is created, passed as an argument and can be inspected at run time.
;; Like the Rust program, the `main` submodule checks the property itself: it exits with an
;; error when the evidence is a run-time argument of `div-with-proof` (expected here: the
;; function takes 3 run-time arguments, the evidence included).
;; The module exports only `check-nonzero` and `div-with-proof`, not the constructor, so other
;; modules cannot forge a token (negative client: q04_evidence_tokens_typed__forge.rkt).
(provide check-nonzero div-with-proof)

(struct IsNonZero ())

(: check-nonzero (-> Integer (U IsNonZero #f)))
(define (check-nonzero b) (if (zero? b) #f (IsNonZero)))

(: div-with-proof (-> Integer Integer IsNonZero Integer))
(define (div-with-proof a b _evidence) (quotient a b))

(module+ main
  (define p (assert (check-nonzero 4)))
  (printf "the token exists at run time: (IsNonZero? p) = ~a\n" (IsNonZero? p))
  (printf "div-with-proof takes ~a run-time arguments\n" (procedure-arity div-with-proof))
  (printf "(div-with-proof 12 4 p) = ~a\n" (div-with-proof 12 4 p))
  (unless (equal? (procedure-arity div-with-proof) 2)
    (error 'q04 "the evidence is a run-time argument (arity ~a): it is not erased"
           (procedure-arity div-with-proof))))
