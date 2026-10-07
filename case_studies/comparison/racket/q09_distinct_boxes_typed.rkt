#lang typed/racket/base
;; Q9 positive (Typed Racket): two mutable references to two different locations, passed to one
;; call. Accepted. Contrast: q09_aliasing_boxes_typed.rkt (same box twice, also accepted).
(: bump! (-> (Boxof Integer) (Boxof Integer) Void))
(define (bump! a b)
  (set-box! a (+ (unbox a) 1))
  (set-box! b (+ (unbox b) 10)))

(module+ main
  (define x : (Boxof Integer) (box 0))
  (define y : (Boxof Integer) (box 0))
  (bump! x y)
  (printf "x = ~a, y = ~a\n" (unbox x) (unbox y)))
