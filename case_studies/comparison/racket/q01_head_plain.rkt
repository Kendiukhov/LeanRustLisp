#lang racket/base
;; Q1 (plain Racket): `head` on lists. Racket has no static types, so `head` of an empty
;; list is not rejected before running; it fails at run time (`car` contract violation).
;; Negative client: q01_head_plain__empty.rkt.
(provide head)

(define (head xs) (car xs))

(module+ main
  (printf "head = ~a\n" (head '(1 2 3))))
