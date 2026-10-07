#lang typed/racket #:with-refinements
;; Q2 (Typed Racket, experimental refinement types): a vector append whose dependent
;; function type states that the result length is the sum of the argument lengths.
;; The result is allocated with `make-vector`, for which the refinement checker tracks the
;; length; the copy loops use ordinary (run-time checked) `vector-ref` / `vector-set!`.
;; Negative clients: __wrong_len (caller claims length 2), __off_by_one (implementation
;; allocates one slot too many). Limit probe: __vector_append (library `vector-append`).
(provide vappend)

(: vappend (-> ([a : (Vectorof Integer)]
                [b : (Vectorof Integer)])
               (Refine [r : (Vectorof Integer)]
                       (= (vector-length r) (+ (vector-length a) (vector-length b))))))
(define (vappend a b)
  (define r (make-vector (+ (vector-length a) (vector-length b)) 0))
  (for ([i (in-range (vector-length a))])
    (vector-set! r i (vector-ref a i)))
  (for ([j (in-range (vector-length b))])
    (vector-set! r (+ (vector-length a) j) (vector-ref b j)))
  r)

;; The caller's claim "the result has length 3" is checked against vappend's type.
(: three (Refine [v : (Vectorof Integer)] (= 3 (vector-length v))))
(define three (vappend (vector 1 2) (vector 3)))

(module+ main
  (printf "vappend = ~a\n" three))
