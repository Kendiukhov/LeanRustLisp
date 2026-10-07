#lang s-exp turnstile/examples/linear/lin+chan
;; Q5 negative (Turnstile linear language): receive twice from the same channel variable `in`
;; instead of from the channel returned by the first `channel-get`.
;; Expected: rejected before running (linear variable used more than once).
(let* ([(in out) (make-channel {Int})])
  (begin
    (thread (λ () (channel-put out 7)))
    (let* ([(in2 v) (channel-get in)]
           [(in3 w) (channel-get in)])
      (begin (drop in2) (drop in3) v))))
