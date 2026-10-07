#lang racket/base
;; Q2 (plain Racket): "the result length is the sum of the argument lengths" can be stated as a
;; dependent contract (->i). The contract is checked at run time, on every call; nothing is
;; checked before running. Negative: q02_append_plain__off_by_one.rkt.
(require racket/contract)
(provide length-sum/c)

;; a dependent function contract: the result's length depends on the arguments
(define length-sum/c
  (->i ([a vector?] [b vector?])
       [r (a b) (λ (r) (= (vector-length r) (+ (vector-length a) (vector-length b))))]))

(define/contract (vappend a b)
  length-sum/c
  (define r (make-vector (+ (vector-length a) (vector-length b)) 0))
  (vector-copy! r 0 a)
  (vector-copy! r (vector-length a) b)
  r)

(module+ main
  (printf "vappend = ~a\n" (vappend (vector 1 2) (vector 3))))
