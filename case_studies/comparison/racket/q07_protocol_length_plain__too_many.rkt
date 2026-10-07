#lang racket/base
;; Q7 negative (plain Racket): a third send on a channel opened for two messages.
;; Expected: accepted by the expander; run-time error from the count check.
(require "q07_protocol_length_plain.rkt")
(close (send (send (send (open-chan 2) 1) 2) 3))
