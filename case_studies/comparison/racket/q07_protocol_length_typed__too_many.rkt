#lang typed/racket/base
;; Q7 negative (Typed Racket): a third send on a channel opened for two messages.
;; Expected: type error.
(require "q07_protocol_length_typed.rkt")
(close (send (send (send (open2) 1) 2) 3))
