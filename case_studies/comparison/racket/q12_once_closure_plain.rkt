#lang racket/base
;; Q12 (plain Racket): a once-only closure. Racket can only enforce "call at most once"
;; dynamically, by a wrapper that fails on the second call.
;; Negative client: q12_once_closure_plain__call_twice.rkt.
(provide once)

(define (once f)
  (define called? #f)
  (lambda args
    (when called? (error 'once "closure called a second time"))
    (set! called? #t)
    (apply f args)))

(module+ main
  (define token "secret")
  (define consume (once (lambda () (string-length token))))
  (printf "first call: ~a\n" (consume)))
