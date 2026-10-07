#lang racket/base
;; Q11 negative (plain Racket): reverse a vector in place while another alias of it is still in
;; use (Rust rejects the corresponding program with E0502). Expected: accepted and run; the
;; alias observes the mutation.
(require "q11_inplace_vector_reverse.rkt")
(define v (build-vector 8 values))
(define alias v)
(define first-before (vector-ref alias 0))
(void (vector-reverse! v))
(printf "alias[0] before = ~a, after = ~a (the alias saw the in-place update)\n"
        first-before (vector-ref alias 0))
