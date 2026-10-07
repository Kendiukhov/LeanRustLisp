#lang typed/racket/base
;; Q7 limit probe (Typed Racket): a generic function that sends every element of a
;; length-indexed vector over a channel whose index is the same length. The vector of
;; length N is a value of the Peano type N carrying one element per S (type VS below).
;; Typed Racket would have to learn N = Z (resp. N = (VS M)) from the test on the vector
;; and use that to retype the channel; occurrence typing refines the vector's type but not
;; the type variable N, so this definition is expected to be rejected.
(struct VZ ())
(struct (N) VS ([x : Integer] [rest : N]))
(struct (N) Chan ([remaining : N] [sent : (Listof Integer)]))

(: send (All (N) (-> (Chan (VS N)) Integer (Chan N))))
(define (send c x) (Chan (VS-rest (Chan-remaining c)) (cons x (Chan-sent c))))

(: close (-> (Chan VZ) (Listof Integer)))
(define (close c) (reverse (Chan-sent c)))

(: send-all (All (N) (-> N (Chan N) (Listof Integer))))
(define (send-all v c)
  (cond
    [(VZ? v) (close c)]
    [(VS? v) (send-all (VS-rest v) (send c (VS-x v)))]
    [else (error 'send-all "not a vector")]))
