#lang typed/racket #:with-refinements
;; Q1 negative (Typed Racket refinements): the unchecked access of q01_head_refined.rkt in a
;; function whose type has NO length precondition, so it can be applied to an empty vector.
;; Typed Racket gives `unsafe-vector-ref` an ordinary type, (Vectorof a) Index -> a, with no
;; refinement, so the body of a refined function is trusted rather than verified; this
;; definition is therefore expected to be accepted. (The program does not call it on an empty
;; vector: an out-of-bounds unsafe access has undefined behaviour.)
(require racket/unsafe/ops)
(: vhead-unrefined (All (A) (-> (Vectorof A) A)))
(define (vhead-unrefined v) (unsafe-vector-ref v 0))
(printf "accepted: vhead-unrefined : (All (A) (-> (Vectorof A) A)) uses unsafe-vector-ref with no length check\n")
