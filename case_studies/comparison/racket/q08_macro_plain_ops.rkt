#lang racket/base
;; Q8 (plain Racket): the same `def-unit` macro as q08_macro_typed_ops.rkt, in untyped Racket.
;; The generated operations are ordinary functions; mixing two units is not detected before
;; running, only by the struct accessor's run-time check.
;; Negative client: q08_macro_plain_ops__mix_units.rkt.
(require (for-syntax racket/base racket/syntax syntax/parse))
(provide (all-defined-out))

(define-syntax (def-unit stx)
  (syntax-parse stx
    [(_ unit:id)
     #:with get (format-id #'unit "~a-v" #'unit)
     #:with add (format-id #'unit "~a-add" #'unit)
     #'(begin
         (struct unit (v))
         (define (add a b)
           (let ([tmp (+ (get a) (get b))])
             (unit tmp))))]))

(def-unit Meters)
(def-unit Seconds)

(module+ main
  (printf "(Meters-add (Meters 3) (Meters 4)) = ~a\n" (Meters-v (Meters-add (Meters 3) (Meters 4)))))
