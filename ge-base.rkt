#lang racket

(require "utils.rkt")
(module+ test (require rackunit))

(provide (struct-out svar)
         (struct-out gvar)
         gconst? generator? word?
         label-<
         gconst-labels svar-labels
         (struct-out ge-base)
         ge-base-clone
         gconst-base
         gconst-base? gvar-base? svar-base? generator-base?
         left-bound right-bound
         crosses-boundary?
         column? empty-col? indecomposable?
         ge-<= ge-min largest-leftmost)
 
;;; A GConst (generator constant) is a Nat
(define (gconst? n) (natural? n))
;;; A GVar (generator variable) is a (gvar symbol)
(define-struct/contract gvar
  ([name symbol?])
  #:transparent)
;;; A Generator is either a GConst or a GVar
(define (generator? x) (or (gconst? x) (gvar? x)))
;;; An SVar (sequence variable) is an (svar symbol)
(define-struct/contract svar
  ([name symbol?])
  #:transparent)
;;; Ordering on GConsts, GVars, and SVars.
;;; any GConst < any GVar < any SVar
;;; Within each class, ties are resolved by numeric or lexical comparison
(define (label-< x y)
  (cond [(and (gconst? x) (gconst? y))
         (< x y)]
        [(and (svar? x) (svar? y))
         (symbol<? (svar-name x) (svar-name y))]
        [(and (gvar? x) (gvar? y))
         (symbol<? (gvar-name x) (gvar-name y))]
        [(gconst? x) #t]
        [(gvar? x) (svar? y)]
        [else #f]))

;;; A Word is a [List [U GConst SVar]]
;;; Since this represents a fragment of an equation, we exclude GVars. They are
;;; only to be introduced into a generalized equation (generated after an
;;; alignment is chosen).
(define word? (listof (or/c gconst? svar?)))

(module+ test
  (for-each check-true
            (list (gconst? 0) (gconst? 9) (svar? (svar 'f))))
  (for-each check-false
            (list (gconst? -2) (gconst? (svar 'f)) (svar? 0) (svar? 9) (svar? -2)))
  (check-true (word? (list 1 (svar 's) 4 (svar 'w))))
  (check-false (word? (list 6 (svar 'a) -4)))
  (check-false (word? (list 1 (svar 's) 4 (gvar 'w)))))


;;; A Generalized Equation Base ("GE Base") is one of
;;; - (ge-base Const (list n n+1))
;;; - (ge-base Var [List-of Nat])  where the list is nondecreasing
;;;     and has length >= 2
(define-struct/contract ge-base
  ([label (or/c gconst? svar? gvar?)]
   [boundaries (and/c (vectorof natural? #:immutable #f) nondecreasing?)])
  #:transparent)
(define (ge-base-clone base)
  (ge-base (ge-base-label base)
           (vector-copy (ge-base-boundaries base))))


;;; Construct a constant base without passing both n and n+1
(define (gconst-base c n) (ge-base c (vector n (add1 n))))

(module+ test (check-equal? (gconst-base 5 0) (ge-base 5 (vector 0 1))))


;;; Does this base have a constant label? seq var label? gen var label?
(define (gconst-base? b) (and (ge-base? b) (gconst? (ge-base-label b))))
(define (svar-base? b) (and (ge-base? b) (svar? (ge-base-label b))))
(define (gvar-base? b) (and (ge-base? b) (gvar? (ge-base-label b))))
(define (generator-base? b) (or (gconst-base? b) (gvar-base? b)))


(module+ test
  (check-true (gconst-base? (gconst-base 5 0)))
  (check-false (gconst-base? (ge-base (svar 'v) (vector 3 9))))
  (check-false (svar-base? (gconst-base 5 0)))
  (check-true (svar-base? (ge-base (svar 'v) (vector 3 9)))))


;;; Identify the outermost boundaries of a GE Base
(define (left-bound geb) (leftmost (ge-base-boundaries geb))
  #;(for/first ([b (ge-base-boundaries geb)]) b))
(define (right-bound geb) (rightmost (ge-base-boundaries geb))
  #;(for/last ([b (ge-base-boundaries geb)]) b))

(module+ test
  (check-equal? (left-bound (ge-base (svar 'r) (vector 3 5 8 13))) 3)
  (check-equal? (right-bound (ge-base (svar 'r) (vector 3 5 8 13))) 13))

;;; Does this GE base extend accross the specified boundary?
(define (crosses-boundary? base boundary)
  (< (left-bound base) boundary (right-bound base)))

(module+ test
  (check-true (crosses-boundary? (ge-base (svar 'q) (vector 4 8)) 5))
  (check-true (crosses-boundary? (ge-base (svar 'q) (vector 4 8)) 7))
  (check-false (crosses-boundary? (ge-base (svar 'q) (vector 4 8)) 4))
  (check-false (crosses-boundary? (ge-base (svar 'q) (vector 4 8)) 8))
  (check-false (crosses-boundary? (ge-base (svar 'q) (vector 4 8)) 2))
  (check-false (crosses-boundary? (ge-base (svar 'q) (vector 4 8)) 19)))

;;; Predicates for recognizing columns and particular kinds of columns
(define column? (vector/c natural? natural?))
(define empty-col? (and/c column? (λ (c) (= (first c) (second c)))))
(define indecomposable? (and/c column? (λ (c) (= (add1 (first c)) (second c)))))


;;; Extract just the generator constant labels from a list of GE Bases
(define (gconst-labels gebs)
  ;; Not sorting these because eventually "Const" definition may be broadened
  ;; beyond just natural numbers, to a point where equality is nontrivial
  (for/list ([base gebs]
             #:when (gconst? (ge-base-label base)))
            (ge-base-label base)))
;;; Extract just the sequence variable labels from a list of GE Bases
(define (svar-labels gebs)
  (sort
   (for/list ([base gebs]
              #:when (svar? (ge-base-label base)))
             (ge-base-label base))
   (λ (l r) (symbol<? (svar-name l) (svar-name r)))))

(module+ test
  (let ([LABEL-TEST-LIST (list (ge-base 3 (vector 0 1))
                               (ge-base (svar 'a) (vector 0 2))
                               (ge-base (svar 'b) (vector 1 5))
                               (ge-base 5 (vector 1 2))
                               (ge-base (svar 'a) (vector 3 5)))])
    (check-equal? (gconst-labels LABEL-TEST-LIST)
                  '(3 5))
    (check-equal? (svar-labels LABEL-TEST-LIST)
                  (list (svar 'a) (svar 'a) (svar 'b)))))


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
  (check-true (ge-<=/2 (ge-base 3 (vector 0 1))
                       (ge-base 4 (vector 0 1))))
  (check-true (ge-<=/2 (ge-base 3 (vector 0 1))
                       (ge-base 3 (vector 1 2))))
  (check-false (ge-<=/2 (ge-base 3 (vector 1 2))
                        (ge-base 3 (vector 0 1))))
  (check-true (ge-<=/2 (ge-base (svar 'e) (vector 1 4))
                       (ge-base (svar 'f) (vector 1 1))))
  (check-true (ge-<=/2 (ge-base (svar 'e) (vector 0 1))
                       (ge-base 4 (vector 0 1))))
  (check-false (ge-<=/2 (ge-base (svar 'q) (vector 0 1))
                        (ge-base (svar 'q) (vector 0 2))))
  (check-true (ge-<= (ge-base 3 (vector 0 1))
                     (ge-base (svar 'e) (vector 1 4))
                     (ge-base 3 (vector 1 2))
                     (ge-base (svar 'w) (vector 2 4))))
  (check-false (ge-<= (ge-base 3 (vector 0 1))
                      (ge-base 3 (vector 1 2))
                      (ge-base (svar 'w) (vector 2 4))
                      (ge-base (svar 'e) (vector 1 4))))
  (check-equal? (ge-min (ge-base 3 (vector 0 1))
                        (ge-base 4 (vector 0 1)))
                (ge-base 3 (vector 0 1)))
  (check-equal? (ge-min (ge-base 4 (vector 0 1))
                        (ge-base 3 (vector 0 1)))
                (ge-base 4 (vector 0 1)))
  (check-equal? (ge-min (ge-base 3 (vector 0 1))
                        (ge-base 3 (vector 1 2)))
                (ge-base 3 (vector 0 1)))
  (check-equal? (ge-min (ge-base (svar 'q) (vector 0 1))
                        (ge-base (svar 'q) (vector 0 2)))
                (ge-base (svar 'q) (vector 0 2)))
  (check-equal? (largest-leftmost (list (ge-base 3 (vector 0 1))
                                        (ge-base 3 (vector 1 2))
                                        (ge-base (svar 'w) (vector 2 4))
                                        (ge-base (svar 'e) (vector 1 4))))
                (ge-base 3 (vector 0 1)))
  (check-equal? (largest-leftmost (list (ge-base 3 (vector 1 2))
                                        (ge-base (svar 'w) (vector 2 4))
                                        (ge-base (svar 'e) (vector 1 4))))
                (ge-base (svar 'e) (vector 1 4))))
