#lang racket

(provide nondecreasing? 
         sym-counts/flat sym-counts)

;;; Check whether a list's elements only increase
(define (nondecreasing? xs)
  (define/match (nondecreasing?/list xs)
    [((list a b more ...)) (and (<= a b) (nondecreasing?/list (cons b more)))]
    [((list a)) #t]
    [((list)) #t])
  (nondecreasing?/list (sequence->list xs)))

;;; Count occurrences of each symbol in a flat sequence
(define (sym-counts/flat seq [counts (hash)])
  (for/fold ([c counts])
            ([item seq])
    (if (symbol? item)
        (hash-update c item add1 0)
        c)))

;;; Count occurrences of each symbol in a list of lists (representing a list
;;; of word equations)
(define (sym-counts eqns [counts (hash)])
  (for/fold ([c counts])
            ([eqn eqns])
    (sym-counts/flat eqn c)))
