#lang racket

(provide nondecreasing?)

;;; Check whether a list's elements only increase
(define (nondecreasing? xs)
  (define/match (nondecreasing?/list xs)
    [((list a b more ...)) (and (<= a b) (nondecreasing?/list (cons b more)))]
    [((list a)) #t]
    [((list)) #t])
  (nondecreasing?/list (sequence->list xs)))
