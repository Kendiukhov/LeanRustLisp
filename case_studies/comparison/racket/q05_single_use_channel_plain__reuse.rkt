#lang racket/base
;; Q5 negative (plain Racket): a second send on the same channel. Expected: accepted by the
;; expander; the run-time flag check raises an error on the second send.
(require "q05_single_use_channel_plain.rkt")
(define c (make-chan 1))
(send! c 7)
(send! c 8)
