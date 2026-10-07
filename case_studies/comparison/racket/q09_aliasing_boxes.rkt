#lang racket/base
;; Q9 (plain Racket): two simultaneously live mutable references to the same location.
;; Racket has no borrow checking: two aliases of one mutable box can both be written,
;; and the program is accepted and runs.

(define (bump! a b)
  (set-box! a (+ (unbox a) 1))
  (set-box! b (+ (unbox b) 10)))

(module+ main
  (define x (box 0))
  (define r1 x)
  (define r2 x)
  (bump! r1 r2)
  (printf "x = ~a (both writes went to the same box)\n" (unbox x)))
