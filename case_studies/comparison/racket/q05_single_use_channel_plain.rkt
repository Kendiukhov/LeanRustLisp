#lang racket/base
;; Q5 (plain Racket): a single-use channel. Without static types, single use can only be
;; enforced by a run-time flag. Negative client: q05_single_use_channel_plain__reuse.rkt.
(provide make-chan send!)

(struct chan (id [used? #:mutable]))

(define (make-chan id) (chan id #f))

(define (send! c x)
  (when (chan-used? c)
    (error 'send! "channel ~a was already used" (chan-id c)))
  (set-chan-used?! c #t)
  (printf "sent ~a on channel ~a\n" x (chan-id c)))

(module+ main
  (define c (make-chan 1))
  (send! c 7))
