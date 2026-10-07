#lang racket/base
;; Q8 negative (plain Racket): add Seconds to Meters with the macro-generated operation.
;; Expected: accepted by the expander; run-time contract error from the generated accessor.
(require "q08_macro_plain_ops.rkt")
(Meters-v (Meters-add (Meters 3) (Seconds 4)))
