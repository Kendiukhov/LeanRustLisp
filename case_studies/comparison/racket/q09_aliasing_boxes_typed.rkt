#lang typed/racket/base
;; Q9 (Typed Racket): the aliasing program of q09_aliasing_boxes.rkt with types. Typed Racket
;; has no notion of borrowing either: two live aliases of one mutable box are accepted.
(: bump! (-> (Boxof Integer) (Boxof Integer) Void))
(define (bump! a b)
  (set-box! a (+ (unbox a) 1))
  (set-box! b (+ (unbox b) 10)))

(module+ main
  (define x : (Boxof Integer) (box 0))
  (define r1 x)
  (define r2 x)
  (bump! r1 r2)
  (printf "x = ~a (both writes went to the same box)\n" (unbox x)))
