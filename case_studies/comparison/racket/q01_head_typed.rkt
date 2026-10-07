#lang typed/racket/base
;; Q1 (Typed Racket): a total head. The type (Pairof A (Listof A)) means "at least one
;; element", so `head` is `car` of a pair and cannot fail. This encodes non-emptiness, not
;; a length index. Negative client: q01_head_typed__empty.rkt.
(provide head)

(: head (All (A) (-> (Pairof A (Listof A)) A)))
(define (head xs) (car xs))

(module+ main
  (printf "head = ~a\n" (head '(1 2 3))))
