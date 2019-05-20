#lang racket

(require "utils.rkt")
(module+ test (require rackunit))

(provide const? var? word?
         const-labels var-labels
         (struct-out ge-base)
         ge-base-clone
         const-base const-base? var-base?
         left-bound right-bound
         crosses-boundary?
         column? empty-col? indecomposable?
         ge-<= ge-min largest-leftmost)
 
;; A Const is a Nat
(define (const? n) (natural? n))
;; A Var is a Symbol
(define (var? n) (symbol? n))
;; A Word is a [List [U Const Var]]
(define word? (listof (or/c const? var?)))

(module+ test
  (for-each check-true
            (list (const? 0) (const? 9) (var? 'f)))
  (for-each check-false
            (list (const? -2) (const? 'f) (var? 0) (var? 9) (var? -2)))
  (check-true (word? '(1 s 4 w)))
  (check-false (word? '(6 a -4))))


;;; A Generalized Equation Base ("GE Base") is one of
;;; - (ge-base Const (list n n+1))
;;; - (ge-base Var [List-of Nat])  where the list is nondecreasing
;;;     and has length >= 2
(define-struct/contract ge-base
  ([label (or/c const? var?)]
   [boundaries (and/c (vectorof natural? #:immutable #f) nondecreasing?)])
  #:transparent)
(define (ge-base-clone base)
  (ge-base (ge-base-label base)
           (vector-copy (ge-base-boundaries base))))


;;; Construct a constant base without passing both n and n+1
(define (const-base c n) (ge-base c (vector n (add1 n))))

(module+ test (check-equal? (const-base 5 0) (ge-base 5 (vector 0 1))))


;;; Does this base have a constant label? variable lable?
(define (const-base? b) (and (ge-base? b) (const? (ge-base-label b))))
(define (var-base? b) (and (ge-base? b) (var? (ge-base-label b))))

(module+ test
  (check-true (const-base? (const-base 5 0)))
  (check-false (const-base? (ge-base 'v (vector 3 9))))
  (check-false (var-base? (const-base 5 0)))
  (check-true (var-base? (ge-base 'v (vector 3 9)))))


;;; Identify the outermost boundaries of a GE Base
(define (left-bound geb) (for/first ([b (ge-base-boundaries geb)]) b))
(define (right-bound geb) (for/last ([b (ge-base-boundaries geb)]) b))

(module+ test
  (check-equal? (left-bound (ge-base 'r (vector 3 5 8 13))) 3)
  (check-equal? (right-bound (ge-base 'r (vector 3 5 8 13))) 13))

;;; Does this GE base extend accross the specified boundary?
(define (crosses-boundary? base boundary)
  (< (left-bound base) boundary (right-bound base)))

(module+ test
  (check-true (crosses-boundary? (ge-base 'q (vector 4 8)) 5))
  (check-true (crosses-boundary? (ge-base 'q (vector 4 8)) 7))
  (check-false (crosses-boundary? (ge-base 'q (vector 4 8)) 4))
  (check-false (crosses-boundary? (ge-base 'q (vector 4 8)) 8))
  (check-false (crosses-boundary? (ge-base 'q (vector 4 8)) 2))
  (check-false (crosses-boundary? (ge-base 'q (vector 4 8)) 19)))

;;; A Column is a nondecreasing [List Nat Nat]
#;(define (geb->column geb) (list (left-bound geb) (right-bound geb)))
;;; Predicates for recognizing columns and particular kinds of columns
(define column? (vector/c natural? natural?))
(define empty-col? (and/c column? (λ (c) (= (first c) (second c)))))
(define indecomposable? (and/c column? (λ (c) (= (add1 (first c)) (second c)))))


;;; Extract just the constant labels from a list of GE Bases
(define (const-labels gebs)
  ;; Not sorting these because eventually "Const" definition may be broadened
  ;; beyond just natural numbers, to a point where equality is nontrivial
  (for/list ([base gebs]
             #:when (const? (ge-base-label base)))
            (ge-base-label base))
  #;(filter const? (map ge-base-label gebs)))
;;; Extract just the variable labels from a list of GE Bases
(define (var-labels gebs)
  (sort
   (for/list ([base gebs]
              #:when (var? (ge-base-label base)))
             (ge-base-label base))
   ;(filter var? (map ge-base-label gebs))
   symbol<?))

(module+ test
  (let ([LABEL-TEST-LIST (list (ge-base  3 (vector 0 1))
                               (ge-base 'a (vector 0 2))
                               (ge-base 'b (vector 1 5))
                               (ge-base  5 (vector 1 2))
                               (ge-base 'a (vector 3 5)))])
    (check-equal? (const-labels LABEL-TEST-LIST)
                  '(3 5))
    (check-equal? (var-labels LABEL-TEST-LIST)
                  '(a a b))))


;;; Positional order relation on GE Bases ("largest leftmost"): the lesser of
;;; two bases is the one which reaches further to the left, with ties broken
;;; by choosing the base with the higher right boundary as lesser.
(define (ge-<=/2 b1 b2)
  (cond [(< (left-bound b1) (left-bound b2)) #t]
        [(= (left-bound b1) (left-bound b2))
         (<= (right-bound b2) (right-bound b1))]
        [else #f]))
(define (ge-<= . bases)
  (cond [(<= (length bases) 1) #t]
        [(ge-<=/2 (first bases) (second bases)) (apply ge-<= (rest bases))]
        [else #f]))
(define (ge-min b1 b2)
  (if (ge-<=/2 b1 b2) b1 b2))
(define (largest-leftmost bases)
  (for/fold ([ll #f])
            ([base bases])
    (cond [(not ll) base]
          [else (ge-min ll base)])))

(module+ test
  (check-true (ge-<=/2 (ge-base 3 (vector 0 1)) (ge-base 4 (vector 0 1))))
  (check-true (ge-<=/2 (ge-base 3 (vector 0 1)) (ge-base 3 (vector 1 2))))
  (check-false (ge-<=/2 (ge-base 3 (vector 1 2)) (ge-base 3 (vector 0 1))))
  (check-true (ge-<=/2 (ge-base 'e (vector 1 4)) (ge-base 'f (vector 1 1))))
  (check-true (ge-<=/2 (ge-base 'e (vector 0 1)) (ge-base 4 (vector 0 1))))
  (check-false (ge-<=/2 (ge-base 'q (vector 0 1)) (ge-base 'q (vector 0 2))))
  (check-true (ge-<= (ge-base 3 (vector 0 1))
                     (ge-base 'e (vector 1 4))
                     (ge-base 3 (vector 1 2))
                     (ge-base 'w (vector 2 4))))
  (check-false (ge-<= (ge-base 3 (vector 0 1))
                      (ge-base 3 (vector 1 2))
                      (ge-base 'w (vector 2 4))
                      (ge-base 'e (vector 1 4))))
  (check-equal? (ge-min (ge-base 3 (vector 0 1)) (ge-base 4 (vector 0 1)))
                (ge-base 3 (vector 0 1)))
  (check-equal? (ge-min (ge-base 4 (vector 0 1)) (ge-base 3 (vector 0 1)))
                (ge-base 4 (vector 0 1)))
  (check-equal? (ge-min (ge-base 3 (vector 0 1)) (ge-base 3 (vector 1 2)))
                (ge-base 3 (vector 0 1)))
  (check-equal? (ge-min (ge-base 'q (vector 0 1)) (ge-base 'q (vector 0 2)))
                (ge-base 'q (vector 0 2)))
  (check-equal? (largest-leftmost (list (ge-base 3 (vector 0 1))
                                        (ge-base 3 (vector 1 2))
                                        (ge-base 'w (vector 2 4))
                                        (ge-base 'e (vector 1 4))))
                (ge-base 3 (vector 0 1)))
  (check-equal? (largest-leftmost (list (ge-base 3 (vector 1 2))
                                        (ge-base 'w (vector 2 4))
                                        (ge-base 'e (vector 1 4))))
                (ge-base 'e (vector 1 4))))
