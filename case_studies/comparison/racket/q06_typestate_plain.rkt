#lang racket/base
;; Q6 (plain Racket): protocol states can only be checked at run time.
;; Negative client: q06_typestate_plain__send_after_close.rkt.
(provide new-chan send close transcript)

(struct chan (state log))

(define (new-chan) (chan 'open '()))

(define (send c x)
  (unless (eq? (chan-state c) 'open)
    (error 'send "channel is ~a, expected open" (chan-state c)))
  (chan 'open (cons x (chan-log c))))

(define (close c)
  (unless (eq? (chan-state c) 'open)
    (error 'close "channel is ~a, expected open" (chan-state c)))
  (chan 'closed (chan-log c)))

(define (transcript c) (reverse (chan-log c)))

(module+ main
  (printf "transcript: ~a\n" (transcript (close (send (send (new-chan) 1) 2)))))
