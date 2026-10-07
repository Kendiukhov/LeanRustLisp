#lang typed/racket/base
;; Q5 (Typed Racket): Typed Racket has no linear or affine types, so a second use of a
;; channel type-checks; only a run-time flag can catch it.
;; Negative client: q05_single_use_channel_typed__reuse.rkt.
(provide make-chan send!)

(struct chan ([id : Integer] [used? : Boolean]) #:mutable)

(: make-chan (-> Integer chan))
(define (make-chan id) (chan id #f))

(: send! (-> chan Integer Void))
(define (send! c x)
  (when (chan-used? c)
    (error 'send! "channel ~a was already used" (chan-id c)))
  (set-chan-used?! c #t)
  (printf "sent ~a on channel ~a\n" x (chan-id c)))

(module+ main
  (send! (make-chan 1) 7))
