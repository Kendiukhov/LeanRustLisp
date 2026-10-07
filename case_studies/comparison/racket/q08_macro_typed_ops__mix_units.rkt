#lang typed/racket/base
;; Q8 negative (Typed Racket): add Seconds to Meters with the macro-generated operation.
;; Expected: type error.
(require "q08_macro_typed_ops.rkt")
(Meters-add (Meters 3) (Seconds 4))
