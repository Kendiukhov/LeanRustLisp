#lang typed/racket/base
;; Q2 limit probe (Typed Racket, no refinements): Typed Racket has fixed-length list types
;; such as (List Integer Integer), but `append` is typed as (Listof A) ... -> (Listof A), so
;; the length of the result is not known to the type checker. Annotating the result of
;; appending a 2-list and a 1-list as a 3-list is therefore expected to be rejected.
(define r (append (list 1 2) (list 3)))
(ann r (List Integer Integer Integer))
