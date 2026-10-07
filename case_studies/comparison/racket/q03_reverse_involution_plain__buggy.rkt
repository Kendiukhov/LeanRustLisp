#lang racket/base
;; Q3 negative (plain Racket): the same run-time check for a wrong reverse (drops the last
;; element of the result when the list has 3 or more elements). Expected: accepted by the
;; expander; the run-time check fails.
(define (my-reverse l)
  (define r (reverse l))
  (if (>= (length l) 3) (reverse (cdr (reverse r))) r))

(for ([n (in-range 0 9)])
  (define l (build-list n values))
  (unless (equal? (my-reverse (my-reverse l)) l)
    (error 'q03 "reverse is not an involution on ~a" l)))
(printf "all tested inputs passed\n")
