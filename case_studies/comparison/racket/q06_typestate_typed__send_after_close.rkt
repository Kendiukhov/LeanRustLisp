#lang typed/racket/base
;; Q6 negative (Typed Racket): send on a closed channel. Expected: type error.
(require "q06_typestate_typed.rkt")
(send (close (send (new-chan) 1)) 2)
