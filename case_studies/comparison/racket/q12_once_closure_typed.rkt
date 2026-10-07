#lang typed/racket/base
;; Q12 (Typed Racket): Typed Racket has no once-only (linear/affine) function types, so a
;; "call at most once" discipline is again a run-time wrapper, now with a type.
;; Negative client: q12_once_closure_typed__call_twice.rkt.
(provide once)

(: once (All (A) (-> (-> A) (-> A))))
(define (once f)
  (define called? : Boolean #f)
  (lambda ()
    (when called? (error 'once "closure called a second time"))
    (set! called? #t)
    (f)))

(module+ main
  (define consume (once (lambda () (string-length "secret"))))
  (printf "first call: ~a\n" (consume)))
