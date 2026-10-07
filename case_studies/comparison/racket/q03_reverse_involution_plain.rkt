#lang racket/base
;; Q3 (plain Racket): "reverse is an involution". Plain Racket has no way to state or check
;; a proof; the closest is a run-time check on chosen inputs.
(module+ main
  (define tested
    (for/sum ([n (in-range 0 9)])
      (define l (build-list n values))
      (unless (equal? (reverse (reverse l)) l)
        (error 'q03 "reverse is not an involution on ~a" l))
      1))
  (printf "(reverse (reverse l)) = l held on ~a tested inputs (run-time check only)\n" tested))
