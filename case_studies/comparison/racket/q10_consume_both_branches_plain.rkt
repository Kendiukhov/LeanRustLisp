#lang racket/base
;; Q10 (plain Racket): a single-use channel (the run-time-flag channel of
;; q05_single_use_channel_plain.rkt) used in both branches of an `if`. Racket has no static
;; notion of consumption, so this is accepted, and so is a use after the `if`
;; (negative client q10_consume_both_branches_plain__use_after.rkt), which fails at run time.
(require "q05_single_use_channel_plain.rkt")

(module+ main
  (define flag (> (vector-length (current-command-line-arguments)) 5))
  (define c (make-chan 1))
  (if flag (send! c 1) (send! c 2)))
