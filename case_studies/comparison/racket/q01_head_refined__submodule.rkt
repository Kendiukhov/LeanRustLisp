#lang typed/racket #:with-refinements
;; Q1 probe (Typed Racket refinements): the precondition written as a refinement of the
;; ARGUMENT type, (Refine [v : (Vectorof A)] (< 0 (vector-length v))), instead of the dependent
;; `#:pre` form used in q01_head_refined.rkt. The program is correct. The call at module level
;; type-checks; the identical call inside the `main` submodule is expected to be rejected
;; ("could not be applied to arguments"). With the `#:pre` form, calls inside `module+ main`
;; type-check (q01_head_refined.rkt). This records an incompleteness of the experimental
;; refinement checker, not an error in the program.
(require racket/unsafe/ops)
(: vhead (All (A) (-> (Refine [v : (Vectorof A)] (< 0 (vector-length v))) A)))
(define (vhead v) (unsafe-vector-ref v 0))

(define v1 (vector 1 2 3))
(printf "module level: vhead = ~a\n" (vhead v1))

(module+ main
  (define v2 (vector 1 2 3))
  (printf "main submodule: vhead = ~a\n" (vhead v2)))
