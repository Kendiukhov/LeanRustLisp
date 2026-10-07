#lang racket/base
;; Q10 negative (plain Racket): the channel is used in both branches and then once more.
;; Expected: accepted by the expander; run-time error from the flag check.
(require "q05_single_use_channel_plain.rkt")
(define flag (> (vector-length (current-command-line-arguments)) 5))
(define c (make-chan 1))
(if flag (send! c 1) (send! c 2))
(send! c 3)
