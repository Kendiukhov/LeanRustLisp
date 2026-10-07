#lang typed/racket/base
;; Q6 (Typed Racket): typestate. The channel's state is a type argument of a polymorphic
;; struct; `send` and `close` accept only (Chan Open).
;; Negative client: q06_typestate_typed__send_after_close.rkt.
(provide (all-defined-out))

(struct Open ())
(struct Closed ())
(struct (S) Chan ([state : S] [log : (Listof Integer)]))

(: new-chan (-> (Chan Open)))
(define (new-chan) (Chan (Open) '()))

(: send (-> (Chan Open) Integer (Chan Open)))
(define (send c x) (Chan (Open) (cons x (Chan-log c))))

(: close (-> (Chan Open) (Chan Closed)))
(define (close c) (Chan (Closed) (Chan-log c)))

(: transcript (-> (Chan Closed) (Listof Integer)))
(define (transcript c) (reverse (Chan-log c)))

(module+ main
  (printf "transcript: ~a\n" (transcript (close (send (send (new-chan) 1) 2)))))
