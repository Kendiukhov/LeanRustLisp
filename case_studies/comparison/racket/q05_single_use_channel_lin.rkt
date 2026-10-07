#lang s-exp turnstile/examples/linear/lin+chan
;; Q5 (Turnstile linear language): the `lin+chan` example language from the turnstile-example
;; package (a linear lambda calculus implemented as Turnstile macros, with channels). The
;; receiving end of a channel, (InChan Int), is a linear type: every variable of that type must
;; be used exactly once, so `channel-get` returns the channel together with the value and the
;; program continues with the new name. Negative: q05_single_use_channel_lin__reuse.rkt.
;; The module prints the received value, 7.
(let* ([(in out) (make-channel {Int})])
  (begin
    (thread (λ () (channel-put out 7)))
    (let* ([(in2 v) (channel-get in)])
      (begin (drop in2) v))))
