#lang typed/racket #:with-refinements
;; Q3 (Typed Racket, experimental refinement types): try to state "reverse is an involution"
;; in the result type of (reverse (reverse l)). The refinement logic is linear integer
;; arithmetic over numbers and vector lengths, so an equation between two lists cannot be
;; written. Expected: rejected (the statement is not a valid refinement), although the program
;; itself is correct.
(: rev2 (-> ([l : (Listof Integer)]) (Refine [r : (Listof Integer)] (= r l))))
(define (rev2 l) (reverse (reverse l)))

(module+ main
  (printf "~a\n" (rev2 (list 1 2 3))))
