#lang typed/racket/base
;; Q7 (Typed Racket): a protocol counter in the types. Peano numerals are polymorphic
;; structs (Z, (S N)); a channel (Chan N) has N messages remaining; `send` needs (Chan (S N))
;; and returns (Chan N); `close` needs (Chan Z). This counts messages for a fixed, written-out
;; sequence of calls. Negative clients: __too_many, __too_few (fixed sequences), and
;; __send_all (a generic "send every element of a length-N vector" function, a limit probe).
(provide (all-defined-out))

(struct Z ())
(struct (N) S ([pred : N]))
(struct (N) Chan ([remaining : N] [sent : (Listof Integer)]))

(: send (All (N) (-> (Chan (S N)) Integer (Chan N))))
(define (send c x) (Chan (S-pred (Chan-remaining c)) (cons x (Chan-sent c))))

(: close (-> (Chan Z) (Listof Integer)))
(define (close c) (reverse (Chan-sent c)))

(: open2 (-> (Chan (S (S Z)))))
(define (open2) (Chan (S (S (Z))) '()))

(module+ main
  (printf "manual transcript: ~a\n" (close (send (send (open2) 1) 2))))
