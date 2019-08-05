#lang racket

(provide leftmost rightmost
         hash-extend! hash-extend*!
         nondecreasing? 
         sym-counts/flat sym-counts
         remove-consecutive-duplicates
         interval-overlap?
         interval-join
         merge-intervals)
(module+ test (require rackunit))

;;; Leftmost element of a boundary sequence
(define (leftmost xs) (for/first ([x xs]) x))
;;; Rightmost element of a boundary sequence
(define (rightmost xs) (for/last ([x xs]) x))

;;; In a mutable hash whose values are sets, add a new element to some key's
;;; set. If that key does not already exist, map it to a singleton set (i.e.,
;;; treat it as though it were previously mapped to the empty set).
(define (hash-extend! h k v)
  (hash-update! h k (λ (old) (set-add old v)) (set)))
;;; As in hash-extend!, but take a sequence of things to add into the mapped set.
(define (hash-extend*! h k vs)
  (for ([v vs]) (hash-extend! h k v)))

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

;;; Skip the first chunk of contiguous stream elements that match a predicate
(define (stream-skip pred xs)
  (cond [(stream-empty? xs) xs]
        [(pred (stream-first xs))
         (stream-skip pred (stream-rest xs))]
        [else xs]))

;;; Drop consecutive occurrences of "equal" items in a list
(define (remove-consecutive-duplicates xs [eqfn equal?])
  (define (rcd xstream)
    (cond [(stream-empty? xstream) xstream]
          [else
           (stream-cons
            (stream-first xstream)
            (rcd (stream-skip (λ (x) (eqfn x (stream-first xstream)))
                              (stream-rest xstream))))]))
  (rcd (sequence->stream xs)))

;;; Do two closed intervals (sequences of endpoints) overlap?
;;; [Sequence-of Nat] [Sequence-of Nat] -> Boolean
(define (interval-overlap? i1 i2)
  (define left1 (for/first ([b i1]) b))
  (define right1 (for/last ([b i1]) b))
  (define left2 (for/first ([b i2]) b))
  (define right2 (for/last ([b i2]) b))
  (or (<= left1 left2 right1)
      (<= left1 right2 right1)
      (<= left2 left1 right2)
      (<= left2 right1 right2)))

;;; Find the smallest closed interval that completely covers the two given
;;; closed intervals
(define (interval-join i1 i2)
  (vector (min (for/first ([b i1]) b) (for/first ([b i2]) b))
          (max (for/last ([b i1]) b) (for/last ([b i2]) b))))

;;; Given a sequence of closed intervals, merge consecutive ranges that overlap
;;; to produce a sequence of disjoint intervals with the same union
;;; [Stream-of [Vector-of Nat]] -> [Stream-of [Vector-of Nat]]
(define (merge-intervals intervals)
  (define (merge* r)
    (cond [(stream-empty? r) r]
          [(stream-empty? (stream-rest r)) r]
          [(interval-overlap? (stream-ref r 0) (stream-ref r 1))
           (merge* (stream-cons
                    (interval-join (stream-ref r 0)
                                   (stream-ref r 1))
                    (stream-tail r 2)))]
          [else (stream-cons (stream-first r)
                             (merge* (stream-rest r)))]))
  (merge* (sequence->stream intervals)))

(module+ test
  (check-equal? (stream->list
                 (merge-intervals
                  (list #(0 2) #(1 5) #(6 8) #(10 11))))
                '(#(0 5) #(6 8) #(10 11))))

