#lang racket/base
;; Q12 negative (plain Racket): the once-only closure called twice. Expected: accepted by
;; the expander; run-time error on the second call.
(require "q12_once_closure_plain.rkt")
(define consume (once (lambda () (string-length "secret"))))
(printf "first call: ~a\n" (consume))
(printf "second call: ~a\n" (consume))
