#lang typed/racket #:with-refinements
;; Q2 limit probe (Typed Racket refinements): the same type for an append that calls the
;; library function `vector-append`. Its type, (Vectorof a) * -> (Mutable-Vectorof a),
;; carries no length information, so the checker is expected to reject the definition.
(: vappend (-> ([a : (Vectorof Integer)]
                [b : (Vectorof Integer)])
               (Refine [r : (Vectorof Integer)]
                       (= (vector-length r) (+ (vector-length a) (vector-length b))))))
(define (vappend a b) (vector-append a b))
