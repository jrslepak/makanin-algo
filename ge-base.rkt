#lang racket

(require "utils.rkt")
(module+ test (require rackunit))

(provide
 (contract-out
  (struct svar ([name symbol?]))
  (struct pvar ([name symbol?]))
  (var-name (-> (or/c svar? pvar?) symbol?))
  (gconst? contract?)
  (var? contract?)
  (word? contract?)
  (list->word (-> (listof (or/c gconst? symbol?)) word?))
  (label-< (-> (or/c gconst? svar?)
               (or/c gconst? svar?)
               boolean?))
  (gconst-labels (-> (listof ge-base?)
                     (listof gconst?)))
  (svar-labels (-> (listof ge-base?)
                   (listof svar?)))
  (struct ge-base ([label (or/c gconst? svar? pvar?)]
                   [boundaries (and/c (vectorof natural? #:immutable #f)
                                      nondecreasing?)]))
  (ge-base-clone (-> ge-base?
                     ge-base?))
  (ge-base-width (-> ge-base? natural?))
  (ge-base-name (-> (or/c svar-base? pvar-base?) symbol?))
  (gconst-base (-> gconst? natural?
                   ge-base?))
  (gconst-base? contract?)
  (svar-base? contract?)
  (pvar-base? contract?)
  (var-base? contract?)
  (erase (-> ge-base? ge-base?))
  (left-bound (-> ge-base?
                  natural?))
  (right-bound (-> ge-base?
                   natural?))
  (crosses-boundary? (-> ge-base? natural?
                         boolean?))
  (column? contract?)
  (empty-col? contract?)
  (indecomposable? contract?)
  (ge-<= (-> ge-base? ge-base?
             boolean?))
  (ge-min (-> ge-base? ge-base?
              ge-base?))
  (largest-leftmost (-> (sequence/c ge-base?)
                        (or/c ge-base? false?)))))
 
;;; A GConst (generator constant) is a Nat
(define (gconst? n) (natural? n))
;;; An SVar (sequence variable) is an (svar symbol)
(define-struct/contract svar
  ([name symbol?])
  #:transparent)
;;; When transport moves a sequence variable, leave a palimpsest variable (pvar)
;;; behind. This should not be eligible for transport, but it helps track which
;;; positions within a variable's column span must be which constants.
(define-struct/contract pvar
  ([name symbol?])
  #:transparent)
;;; Extract the name from any type of variable
(define (var-name v)
  (if (svar? v) (svar-name v) (pvar-name v)))
(define var? (or/c svar? pvar?))

;;; Ordering on GConsts, and SVars.
;;; any GConst < any SVar < any PVar
;;; Within each class, ties are resolved by numeric or lexical comparison
(define (label-< x y)
  (cond [(and (gconst? x) (gconst? y))
         (< x y)]
        [(and (svar? x) (svar? y))
         (symbol<? (svar-name x) (svar-name y))]
        [(and (pvar? x) (pvar? y))
         (symbol<? (pvar-name x) (pvar-name y))]
        [(gconst? x) #t]
        [(svar? x) (pvar? y)]
        [else #f]))

;;; A Word is a [List [U GConst SVar]]
;;; Since this represents a fragment of an equation, we exclude PVars. They are
;;; only to be introduced into a generalized equation during transport.
(define word? (listof (or/c gconst? svar?)))

;;; Convert a list of naturals and symbols into a Word. GConsts are kept as is,
;;; symbols are turned into sequence variables, and other elements are dropped.
(define (list->word xs)
  (for/list ([x xs] #:when (or (symbol? x) (gconst? x)))
            (if (symbol? x) (svar x) x)))

(module+ test
  (for-each check-true
            (list (gconst? 0) (gconst? 9) (svar? (svar 'f))))
  (for-each check-false
            (list (gconst? -2) (gconst? (svar 'f)) (svar? 0) (svar? 9) (svar? -2)))
  (check-true (word? (list 1 (svar 's) 4 (svar 'w))))
  (check-false (word? (list 6 (svar 'a) -4)))
  (check-false (word? (list 1 (svar 's) 4 (pvar 'w)))))


;;; A Generalized Equation Base ("GE Base") is one of
;;; - (ge-base Const (list n n+1))
;;; - (ge-base Var [List-of Nat])  where the list is nondecreasing
;;;     and has length >= 2
(define-struct/contract ge-base
  ([label (or/c gconst? svar? pvar?)]
   [boundaries (and/c (vectorof natural? #:immutable #f) nondecreasing?)])
  #:transparent)
(define (ge-base-clone base)
  (ge-base (ge-base-label base)
           (vector-copy (ge-base-boundaries base))))

;;; Find the number of columns a GE Base spans
(define (ge-base-width b)
  (- (right-bound b) (left-bound b)))

;;; Find the symbolic name of a sequence or palimpsest variable base
(define (ge-base-name b)
  (cond [(svar-base? b) (svar-name (ge-base-label b))]
        [(pvar-base? b) (pvar-name (ge-base-label b))]))

;;; Construct a constant base without passing both n and n+1
(define (gconst-base c n) (ge-base c (vector n (add1 n))))

(module+ test (check-equal? (gconst-base 5 0) (ge-base 5 (vector 0 1))))

;;; Convert a sequence variable base to a palimpsest base
(define (erase svb)
  (if (svar-base? svb)
      (ge-base (pvar (svar-name (ge-base-label svb))) (ge-base-boundaries svb))
      svb))

;;; Does this base have a constant label? seq var label?
;;; gen var label? palimpsest var label?
(define (gconst-base? b) (and (ge-base? b) (gconst? (ge-base-label b))))
(define (svar-base? b) (and (ge-base? b) (svar? (ge-base-label b))))
(define (pvar-base? b) (and (ge-base? b) (pvar? (ge-base-label b))))
(define (var-base? b) (or (svar-base? b) (pvar-base? b)))

(module+ test
  (check-true (gconst-base? (gconst-base 5 0)))
  (check-false (gconst-base? (ge-base (svar 'v) (vector 3 9))))
  (check-false (svar-base? (gconst-base 5 0)))
  (check-true (svar-base? (ge-base (svar 'v) (vector 3 9)))))


;;; Identify the outermost boundaries of a GE Base
(define (left-bound geb) (leftmost (ge-base-boundaries geb)))
(define (right-bound geb) (rightmost (ge-base-boundaries geb)))

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
        [(> (left-bound b1) (left-bound b2)) #f]
        [(< (right-bound b2) (right-bound b1)) #t]
        [(> (right-bound b2) (right-bound b1)) #f]
        [else (label-< (ge-base-label b1) (ge-base-label b2))]))
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
  (check-false (ge-<=/2 (ge-base (svar 'e) (vector 0 1))
                        (ge-base 4 (vector 0 1))))
  (check-true (ge-<=/2 (ge-base 4 (vector 0 1))
                       (ge-base (svar 'e) (vector 0 1))))
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
                (ge-base 3 (vector 0 1)))
  (check-equal? (ge-min (ge-base (pvar 'x) (vector 0 1))
                        (ge-base (svar 'x) (vector 0 1)))
                (ge-base (svar 'x) (vector 0 1)))
  (check-equal? (ge-min (ge-base 3 (vector 0 1))
                        (ge-base 3 (vector 1 2)))
                (ge-base 3 (vector 0 1)))
  (check-equal? (ge-min (ge-base (svar 'q) (vector 0 1))
                        (ge-base (svar 'q) (vector 0 2)))
                (ge-base (svar 'q) (vector 0 2)))
  (check-equal? (largest-leftmost '()) #f)
  (check-equal? (largest-leftmost (list (ge-base 3 (vector 0 1))
                                        (ge-base 3 (vector 1 2))
                                        (ge-base (svar 'w) (vector 2 4))
                                        (ge-base (svar 'e) (vector 1 4))))
                (ge-base 3 (vector 0 1)))
  (check-equal? (largest-leftmost (list (ge-base 3 (vector 1 2))
                                        (ge-base (svar 'w) (vector 2 4))
                                        (ge-base (svar 'e) (vector 1 4))))
                (ge-base (svar 'e) (vector 1 4))))
