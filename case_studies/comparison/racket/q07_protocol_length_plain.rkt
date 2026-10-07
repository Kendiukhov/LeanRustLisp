#lang racket/base
;; Q7 (plain Racket): a channel that counts the remaining messages. Without static types the
;; count can only be checked at run time, by the operations themselves.
;; Negative client: q07_protocol_length_plain__too_many.rkt.
(provide open-chan send close send-all)

(struct chan (remaining sent))

(define (open-chan n) (chan n '()))

(define (send c x)
  (when (zero? (chan-remaining c))
    (error 'send "no messages remaining"))
  (chan (sub1 (chan-remaining c)) (cons x (chan-sent c))))

(define (close c)
  (unless (zero? (chan-remaining c))
    (error 'close "~a messages still to send" (chan-remaining c)))
  (reverse (chan-sent c)))

;; send every element of a list, then close
(define (send-all xs c)
  (if (null? xs) (close c) (send-all (cdr xs) (send c (car xs)))))

(module+ main
  (printf "send-all transcript: ~a\n" (send-all '(10 20 30) (open-chan 3)))
  (printf "manual transcript: ~a\n" (close (send (send (open-chan 2) 1) 2))))
