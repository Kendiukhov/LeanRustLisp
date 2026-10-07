#lang typed/racket/base
;; Q8 (Typed Racket + syntax-parse): a hygienic macro that generates typed operations.
;; `def-unit` generates a struct and typed `-add` / `-get` functions; the generated code is
;; type-checked like hand-written code, so mixing two generated units is a type error
;; (negative client: q08_macro_typed_ops__mix_units.rkt). The template's local binder `tmp`
;; does not capture the user's `tmp`.
(require (for-syntax racket/base racket/syntax syntax/parse))
(provide (all-defined-out))

(define-syntax (def-unit stx)
  (syntax-parse stx
    [(_ unit:id)
     #:with get (format-id #'unit "~a-v" #'unit)
     #:with add (format-id #'unit "~a-add" #'unit)
     #'(begin
         (struct unit ([v : Natural]))
         (: add (-> unit unit unit))
         (define (add a b)
           (let ([tmp (+ (get a) (get b))])
             (unit tmp))))]))

(def-unit Meters)
(def-unit Seconds)

(define-syntax-rule (with-tmp e)
  (let ([tmp 1]) (+ e tmp)))

(module+ main
  (printf "(Meters-add (Meters 3) (Meters 4)) = ~a\n" (Meters-v (Meters-add (Meters 3) (Meters 4))))
  (define tmp 100)
  (printf "(with-tmp tmp) = ~a (101 = hygienic, 2 = captured)\n" (with-tmp tmp)))
