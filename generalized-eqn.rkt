#lang racket

(require (for-syntax racket/list
                     syntax/parse
                     "ge-base.rkt"
                     "utils.rkt")
         "boundary-enum.rkt"
         "ge-base.rkt"
         "utils.rkt")
(module+ test (require rackunit))

(provide
 ge
 (contract-out
  [ge? (-> any/c boolean?)]
  [build-bases (->i ([components word?]
                     [bounds (components)
                             (and/c (listof natural?)
                                    nondecreasing?
                                    (λ (b)
                                      (= (length b)
                                         (add1 (length components)))))])
                    [result (listof ge-base?)])]
  [eqn->ge-list (-> word? word?
                    ge?)]
  [carrier (-> ge? ge-base?)]
  [critical-boundary (-> ge? natural?)]
  [transport-bases (-> ge? (listof ge-base?))]
  [earliest-duplicate (-> ge? ge-base?
                          ge-base?)]
  [base-shift-length (-> ge? natural?)]
  [base-shift! (-> ge? natural?
                   void?)]
  [transport! (-> ge? void?)]
  [geqn-contradiction? (-> ge? boolean?)]
  [geqn-solved? (-> ge? boolean?)]))

;;; A Generalized Equation ("GE") is a list of GE Bases in which
;;; each var is used as a label exactly twice, in bases with
;;; the same number of boundaries
;;; TODO: is there a good way to mandate "no aliasing" within the list?
;;; TODO: require at least two of each variable
(define (ge? l)
  (and ((listof ge-base?) l)
       (for/and ([sc (hash-values
                      (sym-counts/flat
                       (map ge-base-label l)))])
                (not (= 1 sc)))))

;;; Constructor notation for GE
;;; If we have literals everywhere, check at syntax time that the GE is
;;; well-formed -- 2 of each var, nondecreasing boundaries in each base.
(begin-for-syntax
  (define-syntax-class ge-label
    (pattern a:nat)
    (pattern (quote a:id))))
(define-syntax (ge stx)
  (syntax-parse stx
    ;; If we have only "literals"
    [(_ [label:ge-label (boundary:nat ...)] ...)
     (define labels
       (map (λ (geb-stx) (first (syntax->list geb-stx)))
            (rest (syntax->list stx))))
     (define vars (sort (map quoted->sym
                             (filter (compose var? quoted->sym)
                                     labels))
                        symbol<?))
     (define boundary-lists
       (map (λ (geb-stx) (second (syntax->list geb-stx)))
            (rest (syntax->list stx))))
     ;; Do we have two of each variable?
     (define wf-labels
       (begin ;(printf "vars: ~v\n" vars)
              #;(always-two? vars)
              #t))
     ;; Find decreasing boundary lists
     (define decreasing-bounds
       (filter (compose not nondecreasing? syntax->datum)
               boundary-lists))
     ;; Is every boundary list nondecreasing?
     (define wf-bounds
       (empty? decreasing-bounds))
     (cond [(and wf-labels wf-bounds)
            #'(list [ge-base label (vector boundary ...)] ...)]
           [wf-bounds
               (raise-syntax-error
                #f "All variable labels must appear twice" stx)]
           [else
            (raise-syntax-error
             #f "Generalized equation base has out-of-order boundaries"
             (first decreasing-bounds))])]
    [(_ [label (left right)] ...)
     #'(list (ge-base label (vector left right)) ...)]))

(module+ test
  (define GUTIERREZ-EXAMPLE-A
    (ge ['x (1 2)] [ 1 (2 3)] [ 2 (3 4)] ['y (4 6)]
        ['y (1 3)] [ 2 (3 4)] [ 1 (4 5)] ['x (5 6)]))
  (define GUTIERREZ-EXAMPLE-B
    (ge ['x (1 5)] [ 1 (5 6)] [ 2 (6 7)] ['y (7 8)]
        ['y (1 2)] [ 2 (2 3)] [ 1 (3 4)] ['x (4 8)]))
  (check-true (ge? GUTIERREZ-EXAMPLE-A))
  (check-true (ge? GUTIERREZ-EXAMPLE-B))
  (check-false (ge? (ge ['a (0 2)] [ 1 (2 3)]
                        [ 2 (0 1)] ['b (1 3)])))
  (check-true (ge? (ge ['a (0 2)] [ 1 (2 3)]
                       ['a (0 2)] ['b (1 3)]
                       [ 2 (0 1)] ['b (1 3)]))))


;;; Given a list of word components and a list of boundary locations, produce a
;;; list of GE Bases which place the components among the boundaries in order.
;;; Note: this requires (length bounds) = (add1 (length components))
;;; Word [List-of Nat] -> [List-of ge-base]
(define (build-bases components bounds)
  (cond
    ;; Error case: incompatible lengths
    [(not (= (length bounds) (add1 (length components))))
     (error "Mismatched bound/component list lengths")]
    ;; Base case: out of components
    [(empty? components) '()]
    ;; Inductive case: use the first two bounds to build base, but leave the
    ;; second bound on the list to start the next base
    [else (cons (ge-base (first components)
                         (for/vector #:length 2 ([b bounds]) b))
                (build-bases (rest components) (rest bounds)))]))

(module+ test
  (check-equal? (build-bases '() '(4)) '())
  (check-equal? (build-bases '(x y 2 z) '(0 3 5 6 9))
                (ge ['x (0 3)] ['y (3 5)] [2 (5 6)] ['z (6 9)]))
  (check-exn exn:fail? (λ () (build-bases '(x y 2 z) '(0 3 5 6 9 12))))
  (check-exn exn:fail? (λ () (build-bases '(x y 2 z) '(0 3 5 6)))))


;;; Given two words, represented as lists of components (generators and
;;; variables), and a list of boundary selections ('B, 'L, 'R), construct a list
;;; of generalized equations associating each component with its position among
;;; the boundaries. Note: each GE is itself a list of bases.
;;; TODO: Drop GEs which include an obviously invalid base, like a constant with
;;; non-unit length.
;;; Word Word -> [List-of GE]
(define (eqn->ge-list left right)
  (define possible-bound-lists (bounds (length left) (length right)))
  (stream-map (λ (bs) (append (build-bases left (left-bounds bs))
                              (build-bases right (right-bounds bs))))
              possible-bound-lists))

(module+ test
  ;; For testing, not going to be picky about exact order of GEs in the stream
  (check-equal? (list->set (stream->list (eqn->ge-list '(x 1) '(2 x))))
                ;; BBB, BLRB, BRLB
                (set (ge ['x (0 1)] [1 (1 2)] [2 (0 1)] ['x (1 2)])
                     (ge ['x (0 1)] [1 (1 3)] [2 (0 2)] ['x (2 3)])
                     (ge ['x (0 2)] [1 (2 3)] [2 (0 1)] ['x (1 3)]))))


;;; Identify the carrier base in a generalized equation -- the largest leftmost
;;; variable base. If there is no variable base (and therefore no carrier),
;;; return #f.
(define (carrier geqn)
  (largest-leftmost (for/list ([base geqn] #:when (var-base? base)) base)))

(module+ test
  (check-false (carrier '()))
  (check-equal? (carrier
                 (ge ['r (0 1)]
                     ['q (0 2)]
                     [1 (0 3)]
                     ['r (1 3)]
                     ['q (2 3)]
                     ['w (2 4)]))
                (ge-base 'q (vector 0 2)))
  (check-equal? (carrier GUTIERREZ-EXAMPLE-A) (ge-base 'y (vector 1 3)))
  (check-equal? (carrier GUTIERREZ-EXAMPLE-B) (ge-base 'x (vector 1 5))))


;;; Identify the critical boundary in a generalized equation -- the lowest left
;;; bound of any variable base which crosses the carrier's right boundary, or
;;; the carrier's right boundary itself if there is no such variable base.
(define (critical-boundary geqn)
  (for/fold ([cr (right-bound (carrier geqn))])
            ([vb geqn]
             #:when (and (var-base? vb)
                         (crosses-boundary? vb (right-bound (carrier geqn)))))
    (min cr (left-bound vb))))

(module+ test
  (check-equal? (critical-boundary GUTIERREZ-EXAMPLE-A) 3)
  (check-equal? (critical-boundary GUTIERREZ-EXAMPLE-B) 4))


;;; Identify transport bases in a generalized equation -- those which appear
;;; within the range of the carrier base but are not the carrier itself.
(define (transport-bases geqn)
  (for/list ([base geqn]
             #:when (and
                     (not (eq? base (carrier geqn)))
                     (or (and (<= (left-bound (carrier geqn)) (left-bound base))
                              (< (left-bound base) (critical-boundary geqn)))
                         (= (left-bound base)
                            (right-bound base)
                            (critical-boundary geqn)))))
            base))

(module+ test
  (check-equal? (transport-bases GUTIERREZ-EXAMPLE-A)
                (list (ge-base 'x (vector 1 2))
                      (ge-base 1 (vector 2 3))))
  (check-equal? (transport-bases GUTIERREZ-EXAMPLE-B)
                (list (ge-base 'y (vector 1 2))
                      (ge-base 2 (vector 2 3))
                      (ge-base 1 (vector 3 4))))
  ;; Make sure we skip the carrier but still include extra equivalent bases
  (check-equal? (transport-bases (ge ['x (1 3)] ['x (1 3)]))
                (list (ge-base 'x (vector 1 3)))))


;;; Given a variable base and a generalized equation, find another base with
;;; the same variable (if there isn't one, something has gone very wrong). If
;;; this variable appears twice in the same place, it's ok to return the
;;; duplicate occurrence, but do not produce an alias of the original base.
(define (earliest-duplicate orig geqn)
  (for/fold ([d #f])
            ([base geqn]
             #:when (and (equal? (ge-base-label orig)
                                 (ge-base-label base))
                         (not (eq? orig base))))
    (if d (ge-min d base) base)))

(module+ test
  (check-equal? (earliest-duplicate (first GUTIERREZ-EXAMPLE-A)
                              GUTIERREZ-EXAMPLE-A)
                (last GUTIERREZ-EXAMPLE-A))
  (check-equal? (earliest-duplicate (last GUTIERREZ-EXAMPLE-A)
                              GUTIERREZ-EXAMPLE-A)
                (first GUTIERREZ-EXAMPLE-A))
  (check-equal? (earliest-duplicate (fifth GUTIERREZ-EXAMPLE-A)
                              GUTIERREZ-EXAMPLE-A)
                (fourth GUTIERREZ-EXAMPLE-A))
  (let ([original  (ge-base 'x (vector 2 5))]
        [duplicate (ge-base 'x (vector 2 5))])
    (check-eq? (earliest-duplicate original (list original duplicate))
               duplicate)
    (check-eq? (earliest-duplicate original (list duplicate original))
               duplicate)))


;;; Determine the shift length -- how far must the carrier and transport bases
;;; be moved in order to meet the carrier's dual?
(define (base-shift-length geqn)
  (- (right-bound (earliest-duplicate (carrier geqn) geqn))
     (right-bound (carrier geqn))))

(module+ test
  (check-equal? (base-shift-length (ge ['z (0 3)]
                                       ['z (0 3)]))
                0)
  (check-equal? (base-shift-length (ge [ 4 (0 1)]
                                       ['z (1 2)]
                                       ['z (0 1)]
                                       [ 5 (1 2)]))
                1)
  (check-equal? (base-shift-length GUTIERREZ-EXAMPLE-A) 3)
  (check-equal? (base-shift-length GUTIERREZ-EXAMPLE-B) 3))


;;; Destructively shift a base right by the given distance (use negative
;;; distance for left shift).
(define (base-shift! base dist)
  (vector-map! (λ (bound) (+ bound dist)) (ge-base-boundaries base)))

(module+ test
  (let ([TEST-VAR-BASE (ge-base 'q (vector 0 3 7))])
    (check-equal? (left-bound TEST-VAR-BASE) 0)
    (check-equal? (right-bound TEST-VAR-BASE) 7)
    (base-shift! TEST-VAR-BASE 2)
    (check-equal? (left-bound TEST-VAR-BASE) 2)
    (check-equal? (right-bound TEST-VAR-BASE) 9)))


;;; Destructively ransport the largest of the leftmost variable bases to the
;;; same location as the other occurrence of the same variable, along with the
;;; other bases which overlap it. If there are only two occurrences of the
;;; carrier's variable in the generalized equation, remove both; otherwise,
;;; remove only the carrier.
(define (transport! geqn)
  (define carr (carrier geqn))
  (define dual (earliest-duplicate carr geqn))
  (define dist (base-shift-length geqn))
  (define tbs (transport-bases geqn))
  (for ([base tbs]) (base-shift! base dist))
  (if (= 2 (for/sum ([base geqn]
                     #:when (equal? (ge-base-label base) (ge-base-label carr)))
                    1))
      (for/list ([base geqn]
                 #:when (not (equal? (ge-base-label base) (ge-base-label carr))))
                base)
      (for/list ([base geqn] #:when (not (eq? base carr))) base)))

(module+ test
  (define G1 (map ge-base-clone GUTIERREZ-EXAMPLE-A))
  (define G1/t1 (transport! G1))
  (check-equal? (sort G1/t1 ge-<=)
                (sort (ge ['x (4 5)] [ 1 (5 6)] [ 2 (3 4)]
                          [ 2 (3 4)] [ 1 (4 5)] ['x (5 6)])
                      ge-<=))
  (define G1/t2 (transport! (map ge-base-clone G1/t1)))
  (check-equal? (sort G1/t2 ge-<=)
                (sort (ge [ 1 (5 6)] [ 2 (3 4)]
                          [ 2 (3 4)] [ 1 (5 6)])
                      ge-<=))

  (define G2 (map ge-base-clone GUTIERREZ-EXAMPLE-B))
  (define G2/t1 (transport! G2))
  (check-equal? (sort G2/t1 ge-<=)
                (sort (ge [ 1 (5 6)] [ 2 (6 7)] ['y (7 8)]
                          ['y (4 5)] [ 2 (5 6)] [ 1 (6 7)])
                      ge-<=)))


;;; Check whether a generalized equation has a contradiction: two constant
;;; bases in the same column with different labels.
(define (geqn-contradiction? geqn)
  (define const-bases
    (sort (for/list ([base geqn] #:when (const-base? base)) base) ge-<=))
  (define (overlap-conflict bases)
    (and (> (length bases) 1)
         (or (and (= (left-bound (first bases))
                     (left-bound (second bases)))
                  (not (equal? (ge-base-label (first bases))
                               (ge-base-label (second bases)))))
             (overlap-conflict (rest bases)))))
  (overlap-conflict const-bases))

(module+ test
  (check-true (geqn-contradiction? (ge [3 (0 1)] [4 (1 2)]
                                       [2 (0 1)] [4 (1 2)])))
  (check-false (geqn-contradiction? (ge ['a (0 1)] [4 (1 2)]
                                        [ 2 (0 1)] [4 (1 2)])))
  (check-false (geqn-contradiction? (ge ['a (0 1)] [4 (1 2)]
                                        ['b (0 1)] [4 (1 2)])))
  (check-false (geqn-contradiction? (ge ['a (0 1)] [ 4 (1 2)]
                                        [ 4 (0 1)] ['b (1 2)]))))


;;; Check whether a generalized equation is solved: no more variable bases.
(define (geqn-solved? geqn)
  (not (for/or ([base geqn]) (var-base? base))))

(module+ test
  (check-false (geqn-solved? G1/t1))
  (check-true (geqn-solved? G1/t2)))
