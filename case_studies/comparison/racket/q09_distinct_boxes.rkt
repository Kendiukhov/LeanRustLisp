#lang racket/base
;; Q9 positive (plain Racket): two mutable references to two different locations, passed to one
;; call. Accepted (as in every language here). Contrast: q09_aliasing_boxes.rkt.
(define (bump! a b)
  (set-box! a (+ (unbox a) 1))
  (set-box! b (+ (unbox b) 10)))

(module+ main
  (define x (box 0))
  (define y (box 0))
  (bump! x y)
  (printf "x = ~a, y = ~a\n" (unbox x) (unbox y)))
