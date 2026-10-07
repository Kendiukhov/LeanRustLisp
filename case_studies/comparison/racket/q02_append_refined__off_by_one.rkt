#lang typed/racket #:with-refinements
;; Q2 negative (Typed Racket refinements): an append implementation that allocates one slot
;; too many. Expected: type error.
(: vappend (-> ([a : (Vectorof Integer)]
                [b : (Vectorof Integer)])
               (Refine [r : (Vectorof Integer)]
                       (= (vector-length r) (+ (vector-length a) (vector-length b))))))
(define (vappend a b)
  (define r (make-vector (+ (vector-length a) (vector-length b) 1) 0))
  (for ([i (in-range (vector-length a))])
    (vector-set! r i (vector-ref a i)))
  (for ([j (in-range (vector-length b))])
    (vector-set! r (+ (vector-length a) j) (vector-ref b j)))
  r)
