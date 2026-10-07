#lang racket/base
;; Q6 negative (plain Racket): send on a closed channel. Expected: accepted by the expander;
;; run-time error.
(require "q06_typestate_plain.rkt")
(send (close (send (new-chan) 1)) 2)
