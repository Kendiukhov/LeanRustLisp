#lang racket/base
;; Q11 (plain Racket): in-place update. A mutable vector can be reversed in place with
;; `vector-set!` (same object, `eq?`); list `reverse` builds a new list. Nothing prevents another
;; alias from observing the mutation (negative client: q11_inplace_vector_reverse__alias.rkt).
(provide vector-reverse!)

(define (vector-reverse! v)
  (let loop ([i 0] [j (sub1 (vector-length v))])
    (when (< i j)
      (define t (vector-ref v i))
      (vector-set! v i (vector-ref v j))
      (vector-set! v j t)
      (loop (add1 i) (sub1 j))))
  v)

(module+ main
  (define v (build-vector 8 values))
  (define w (vector-reverse! v))
  (printf "vector-reverse!: same object = ~a, v = ~a\n" (eq? v w) v)
  (define l (build-list 8 values))
  (define r (reverse l))
  (printf "list reverse: same object = ~a, original list unchanged = ~a\n" (eq? l r) l))
