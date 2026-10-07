#lang racket/base
;; Q2 negative (plain Racket): an append that allocates one slot too many, under the same
;; dependent contract. Expected: accepted by the expander; the contract fails at run time,
;; blaming the implementation.
(require racket/contract "q02_append_plain.rkt")

(define/contract (vappend a b)
  length-sum/c
  (define r (make-vector (+ (vector-length a) (vector-length b) 1) 0))
  (vector-copy! r 0 a)
  (vector-copy! r (vector-length a) b)
  r)

(printf "vappend = ~a\n" (vappend (vector 1 2) (vector 3)))
