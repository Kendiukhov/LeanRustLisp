#lang typed/racket/base
;; Q7 negative (Typed Racket): close after one send on a channel opened for two messages.
;; Expected: type error.
(require "q07_protocol_length_typed.rkt")
(close (send (open2) 1))
