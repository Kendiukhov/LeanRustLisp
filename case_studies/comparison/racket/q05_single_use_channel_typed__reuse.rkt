#lang typed/racket/base
;; Q5 negative (Typed Racket): a second send on the same channel. Expected: accepted by the
;; type checker; run-time error from the flag check.
(require "q05_single_use_channel_typed.rkt")
(define c (make-chan 1))
(send! c 7)
(send! c 8)
