#lang typed/racket/base
;; Q12 negative (Typed Racket): the once-only closure called twice. Expected: accepted by the
;; type checker; run-time error on the second call.
(require "q12_once_closure_typed.rkt")
(define consume (once (lambda () (string-length "secret"))))
(printf "first call: ~a\n" (consume))
(printf "second call: ~a\n" (consume))
