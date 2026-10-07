#lang typed/racket #:with-refinements
;; Q2 negative (Typed Racket refinements): the caller claims that appending a 2-vector and a
;; 1-vector gives a 2-vector. Expected: type error.
(require "q02_append_refined.rkt")
(: two (Refine [v : (Vectorof Integer)] (= 2 (vector-length v))))
(define two (vappend (vector 1 2) (vector 3)))
