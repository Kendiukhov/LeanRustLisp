#lang typed/racket #:with-refinements
;; Q1 (Typed Racket, experimental refinement types): head on vectors, with a dependent
;; function type whose precondition says the length is positive (the style of the
;; `safe-ref` example in the Typed Racket reference, "Experimental Features").
;; Callers must prove the precondition; `unsafe-vector-ref` does no run-time bounds check.
;; The body itself is trusted: Typed Racket does not check that `unsafe-vector-ref` is in
;; bounds (see q01_head_refined__unrefined.rkt).
;; Negative client: q01_head_refined__empty.rkt.
(require racket/unsafe/ops)
(provide vhead)

(: vhead (All (A) (-> ([v : (Vectorof A)])
                      #:pre (v) (< 0 (vector-length v))
                      A)))
(define (vhead v) (unsafe-vector-ref v 0))

(module+ main
  (printf "vhead = ~a\n" (vhead (vector 1 2 3))))
