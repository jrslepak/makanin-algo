#lang racket

(require (for-syntax syntax/parse
                     "ge-base.rkt"
                     "utils.rkt")
         "enumerate.rkt"
         "ge-base.rkt"
         "utils.rkt")
(module+ test (require rackunit))

(provide
 ge S P
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
  [words->ge* (->* [word? word?]
                   [boolean?]
                   (stream/c ge?))]
  [lists->ge* (->* [(listof (or/c gconst? symbol?))
                    (listof (or/c gconst? symbol?))]
                   [boolean?]
                   (stream/c ge?))]
  [ge-bases/label (-> ge? any/c
                      ge?)]
  [ge-columns (-> ge? (listof natural?))]
  [svars (-> ge? (set/c svar?))]
  [pvars (-> ge? (set/c pvar?))]
  [vars (-> ge? (set/c var?))]
  [gconsts (-> ge? (set/c gconst?))]
  [carrier (-> ge? (or/c ge-base? false?))]
  [critical-boundary (-> ge? natural?)]
  [transport-bases (-> ge? (listof ge-base?))]
  [earliest-duplicate (-> ge-base? ge?
                          ge-base?)]
  [transport (-> ge? ge-base? ge-base? (-> natural? natural?)
                 ge?)]
  [ge-solved? (-> ge? boolean?)]))

;;; A Generalized Equation ("GE") is a list of GE Bases in which each sequence
;;; var is used as a label at least twice, in bases with the same number of
;;; boundaries (i.e., no single-use variables)
;;; TODO: is there a good way to mandate "no aliasing" within the list?
(define (ge? l)
  (and ((non-empty-listof ge-base?) l)
       (let ([seq-vars (for/list ([base l]
                                  #:when (svar-base? base))
                                 (svar-name (ge-base-label base)))])
         (for/and ([sc (hash-values (sym-counts/flat seq-vars))])
                  (not (= 1 sc))))))

;;; Constructor notation for GE
(define-syntax (S stx)
  (syntax-parse stx
    [(_ v:id) #'(svar 'v)]))
(define-syntax (P stx)
  (syntax-parse stx
    [(_ v:id) #'(pvar 'v)]))
(begin-for-syntax
  (define-syntax-class ge-label
    #:literals (S P)
    (pattern a:nat)
    (pattern [S a:id])
    (pattern [P a:id]))
  (define-syntax-class ge-base-literal
    (pattern [label:ge-label (boundary:nat ...)])))
(define-syntax (label->ge-label stx)
  (syntax-parse stx
    #:literals (S P)
    [(_ n:nat) #'n]
    [(_ [S v:id]) #'(svar (quote v))]
    [(_ [P v:id]) #'(pvar (quote v))]))
(define-syntax (literal->ge-base stx)
  (syntax-parse stx
    #:literals (S P)
    [(_ [l:ge-label (boundary:nat ...)])
     (if (nondecreasing? (syntax->datum #'(boundary ...)))
     #'(ge-base (label->ge-label l) (vector boundary ...))
     (raise-syntax-error
      #f "GE base has out-of-order boundaries"
      (syntax->datum #'(boundary ...))))]))
(define-syntax (ge stx)
  (syntax-parse stx
    ;; If we have a "literal"
    [(_ b:ge-base-literal more ...)
     #'(cons (literal->ge-base b) (ge more ...))]
    [(_ [label (left right)] more ...)
     #'(cons (ge-base label (vector left right)) (ge more ...))]
    [(_) #'(list)]))

(module+ test
  (define GUTIERREZ-EXAMPLE-A
    (ge [(S x) (1 2)] [1 (2 3)] [2 (3 4)] [(S y) (4 6)]
        [(S y) (1 3)] [2 (3 4)] [1 (4 5)] [(S x) (5 6)]))
  (define GUTIERREZ-EXAMPLE-B
    (ge [(S x) (1 5)] [1 (5 6)] [2 (6 7)] [(S y) (7 8)]
        [(S y) (1 2)] [2 (2 3)] [1 (3 4)] [(S x) (4 8)]))
  (check-true (ge? GUTIERREZ-EXAMPLE-A))
  (check-true (ge? GUTIERREZ-EXAMPLE-B))
  (check-false (ge? (ge [(S a) (0 2)] [1 (2 3)]
                        [2 (0 1)] [(S b) (1 3)])))
  (check-true (ge? (ge [(S a) (0 2)] [1 (2 3)]
                       [(S a) (0 2)] [(S b) (1 3)]
                       [2 (0 1)] [(S b) (1 3)]))))

;;; Select the GE bases that have a given label
;;; GE Any -> [Listof GE-base]
(define (ge-bases/label ge l)
  (for/list ([base ge] #:when (equal? l (ge-base-label base))) base))

;;; The columns of a GE are the unit-separated pairs of boundaries located
;;; between any GE base's leftmost and rightmost boundaries.
;;; A column is represented by its left boundary.
;;; GE -> [List-of natural]
(define (ge-columns ge)
  (define sorted-bases (sort ge ge-<=))
  (define base-spans (for/list ([b sorted-bases]) (ge-base-boundaries b)))
  (define covered-intervals
    (merge-intervals
     (remove-consecutive-duplicates
      base-spans
      (λ (x y) (= (leftmost x) (leftmost y))))))
  (apply append
         (for/list ([interval covered-intervals])
                   (stream->list (in-range (leftmost interval)
                                           (rightmost interval))))))
(module+ test
  (check-equal? (ge-columns (ge [(S a) (0 3)]))
                '(0 1 2))
  (check-equal? (ge-columns (ge [1 (2 3)] [4 (5 6)]))
                '(2 5))
  (check-equal? (ge-columns (ge [1 (2 3)] [4 (5 6)] [(S a) (2 6)]))
                '(2 3 4 5)))


;;; Identify which columns in a GE are not occupied by a generator base.
;;; GE -> [List-of natural]
(define (empty-columns ge)
  (define gconst-bases
    (for/list ([base ge] #:when (gconst-base? base)) base))
  (define all-columns (ge-columns ge))
  (define occupied-columns
    (sort (for/list ([gb gconst-bases]) (left-bound gb)) <))
  ;; Step through the two sorted lists of columns
  (define (empty-columns* all occupied)
    (cond [(empty? all)
           ;; Nothing left to include
           '()]
          [(empty? occupied)
           ;; No more exclusions, so keep everything that remains
           all]
          [(= (first all) (first occupied))
           ;; This column is marked for exclusion
           (empty-columns* (rest all) occupied)]
          [(< (first all) (first occupied))
           ;; Keep this column because it is farther left than
           ;; the left-most excluded column
           (cons (first all) (empty-columns* (rest all) occupied))]
          [(> (first all) (first occupied))
           ;; There might be a later exclusion which applies here,
           ;; so defer decision on this column
           (empty-columns* all (rest occupied))]))
  (empty-columns* all-columns occupied-columns))

(module+ test
  ;; Include columns only covered by a sequence variable
  (check-equal? (empty-columns (ge [(S a) (0 3)] [2 (4 5)]))
                '(0 1 2))
  ;; Exclude space between generator constants...
  (check-equal? (empty-columns (ge [1 (1 2)] [2 (4 5)]))
                '())
  ;; ... unless that space is covered by a sequence variable.
  (check-equal? (empty-columns (ge [1 (1 2)] [2 (4 5)] [(S q) (1 5)]))
                '(2 3))
  ;; When a GConst appears within an SVar, drop only that GConst's column
  (check-equal? (empty-columns (ge [(S a) (0 4)] [2 (4 5)] [1 (1 2)]))
                '(0 2 3)))

;;; Identify all ordinary sequence variables used in a GE.
(define (svars ge)
  (for/set ([base ge] #:when (svar-base? base)) (ge-base-label base)))

;;; Identify all palimpsest variables used in a GE.
(define (pvars ge)
  (for/set ([base ge] #:when (pvar-base? base)) (ge-base-label base)))

;;; Identify all variables used in a GE.
(define (vars ge)
  (set-union (pvars ge) (svars ge)))

;;; Identify all generator constants used in a GE.
(define (gconsts ge)
  (for/set ([base ge] #:when (gconst-base? base)) (ge-base-label base)))


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
  (check-equal? (build-bases (list (svar 'x) (svar 'y) 2 (svar 'z))
                             '(0 3 5 6 9))
                (ge [(S x) (0 3)] [(S y) (3 5)] [2 (5 6)] [(S z) (6 9)]))
  (check-exn exn:fail?
             (λ () (build-bases (list (svar 'x) (svar 'y) 2 (svar 'z))
                                '(0 3 5 6 9 12))))
  (check-exn exn:fail?
             (λ () (build-bases (list (svar 'x) (svar 'y) 2 (svar 'z))
                                '(0 3 5 6)))))

;;; If a list of ge-bases is malformed due to a sequence variable with only one
;;; occurrence, insert a copy of it as a dual.
;;; [List GE-Base] -> GE
(define (add-dummy-duals bases)
  (define var-partition (make-hash))
  (for ([b bases] #:when (svar-base? b))
       (define var (svar-name (ge-base-label b)))
       (hash-set! var-partition var
                  (cons b (hash-ref! var-partition var (list)))))
  (define copies
    (for/list ([(x b) var-partition] #:when (= 1 (length b))) (ge-base-clone (first b))))
  (append copies bases))

;;; Check whether a proposed boundary selection for a word would make a
;;; generator base span multiple columns or includes the wrong number of
;;; boundaries.
(define (alignable? word bounds)
  (cond [(not (= (length bounds) (add1 (length word)))) #f]
        [(empty? word) #t]
        [(gconst? (first word)) (and (= 1 (- (second bounds) (first bounds)))
                                     (alignable? (rest word) (rest bounds)))]
        [else (alignable? (rest word) (rest bounds))]))


;;; Given two lists of word components (sequence variables and generator
;;; constants), make a stream containing each generalized equation that can be
;;; produced by aligning components. In "picky" mode, exclude any result
;;; containing a generator base spanning multiple columns.
;;; Word Word -> [Stream GE]
(define (words->ge* left right [picky? #t])
  (for/stream
   ([bound-locs (bounds (length left) (length right))]
    ;; Exclude any GE which would have a generator stretch across
    ;; multiple columns.
    #:when (or (not picky?)
               (and (alignable? left (map add1 (left-bounds bound-locs)))
                    (alignable? right (map add1 (right-bounds bound-locs))))))
   (define next-ge
     (sort
      (add-dummy-duals
       (append (build-bases left (map add1 (left-bounds bound-locs)))
               (build-bases right (map add1 (right-bounds bound-locs)))))
      ge-<=))
   next-ge))
(module+ test
  (check-equal?
   (stream->list (words->ge* (list 1 (svar 'x)) (list (svar 'x) 1)))
   (list (ge [1 (1 2)] [(S x) (2 4)]
             [(S x) (1 3)] [1 (3 4)])
         (ge [1 (1 2)] [(S x) (2 3)]
             [(S x) (1 2)] [1 (2 3)])))
  (check-equal?
   (stream->list (words->ge* (list 1 (svar 'x)) (list (svar 'x) 1) #f))
   (list (ge [1 (1 2)] [(S x) (2 4)]
             [(S x) (1 3)] [1 (3 4)])
         (ge [1 (1 3)] [(S x) (3 4)]
             [(S x) (1 2)] [1 (2 4)])
         (ge [1 (1 2)] [(S x) (2 3)]
             [(S x) (1 2)] [1 (2 3)]))))

;;; Alternate version of words->ge* for use with simple quoted lists
(define (lists->ge* left right [picky? #t])
  (words->ge* (list->word left) (list->word right) picky?))


;;; Identify the carrier base in a generalized equation -- the largest leftmost
;;; variable base. If there is no variable base (and therefore no carrier),
;;; return #f.
(define (carrier geqn)
  (largest-leftmost (for/list ([base geqn] #:when (svar-base? base)) base)))

(module+ test
  (check-false (carrier '()))
  (check-equal? (carrier
                 (ge [(S r) (0 1)]
                     [(S q) (0 2)]
                     [1 (0 3)]
                     [(S r) (1 3)]
                     [(S q) (2 3)]
                     [(S w) (2 4)]))
                (ge-base (svar 'q) (vector 0 2)))
  (check-equal? (carrier GUTIERREZ-EXAMPLE-A) (ge-base (svar 'y) (vector 1 3)))
  (check-equal? (carrier GUTIERREZ-EXAMPLE-B) (ge-base (svar 'x) (vector 1 5))))


;;; Identify the critical boundary in a generalized equation -- the lowest left
;;; bound of any variable base which crosses the carrier's right boundary, or
;;; the carrier's right boundary itself if there is no such variable base.
(define (critical-boundary geqn)
  (for/fold ([cr (right-bound (carrier geqn))])
            ([vb geqn]
             #:when (and (svar-base? vb)
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
                (list (ge-base (svar 'x) (vector 1 2))
                      (ge-base 1 (vector 2 3))))
  (check-equal? (transport-bases GUTIERREZ-EXAMPLE-B)
                (list (ge-base (svar 'y) (vector 1 2))
                      (ge-base 2 (vector 2 3))
                      (ge-base 1 (vector 3 4))))
  ;; Make sure we skip the carrier but still include extra equivalent bases
  (check-equal? (transport-bases (ge [(S x) (1 3)] [(S x) (1 3)]))
                (list (ge-base (svar 'x) (vector 1 3)))))


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
  (let ([original  (ge-base (svar 'x) (vector 2 5))]
        [duplicate (ge-base (svar 'x) (vector 2 5))])
    (check-eq? (earliest-duplicate original (list original duplicate))
               duplicate)
    (check-eq? (earliest-duplicate original (list duplicate original))
               duplicate)))


;;; Path-specified version of Makanin's `transport' procedure: instead of
;;; automatically discovering the carrier/dual bases, takes the carrier base
;;; and dual as arguemnts, along with a function which either maps from the
;;; carrier's interval to the dual's interval (if the dual is at least as wide
;;; as the carrier) or expands the dual's interval (if the dual is narrower than
;;; the carrier).
;;; Since this does not modify the GE in place, it may benefit from a fancier
;;; persistent data structure.
;;; GE GE-Base GE-Base [Natural -> Natural] -> GE
(define (transport ge carrier dual relabel-cols)
  ;; Construct a moved version of a base
  (define (move base fn)
    (ge-base (ge-base-label base)
             (vector-map fn (ge-base-boundaries base))))
  ;; Relabel the columns so that the carrier and dual both span the same number
  ;; of columns.
  (define widened-ge (for/list ([base ge]) (move base relabel-cols)))
  (define widened-carrier (move carrier relabel-cols))
  (define widened-dual (move dual relabel-cols))
  ;; Shift a transport base from the carrier zone to the dual zone.
  (define (shift base)
    (move base (λ (c) (+ c (- (left-bound widened-dual)
                              (left-bound widened-carrier))))))
  ;; Check whether a base is still live and entirely inside the carrier zone.
  (define (shiftable? base)
    (and (not (pvar-base? base))
         (<= (left-bound widened-carrier)
             (left-bound base)
             (right-bound base)
             (right-bound widened-carrier))))
  ;; Should only the carrier be left out of the result, or the dual too?
  (define carrier-var-count
    (for/sum ([base ge]
              #:when (equal? (ge-base-label base)
                             (ge-base-label widened-carrier)))
             1))
  ;; The carrier is going to be "erased" so that it is not considered for future
  ;; transport rounds. If that would leave the dual as the only live occurrence,
  ;; erase the dual as well.
  (define erasable?
    (if (= 2 carrier-var-count)
        (λ (b) (or (equal? b widened-carrier)
                   (equal? b widened-dual)))
        (λ (b) (equal? b widened-carrier))))
  (define new-ge
    (sort (flatten (for/list ([base widened-ge])
                             (cond [(erasable? base) (erase base)]
                                   [(shiftable? base) (list (erase base)
                                                            (shift base))]
                                   [else base])))
          ge-<=))
  new-ge)

(module+ test
  (define GUTIERREZ-EXAMPLE-PG8 (ge [(S u) (1 3)]
                                    [(S x) (5 8)]
                                    [(S x) (1 5)]
                                    [(S u) (6 8)]
                                    [(S y) (3 7)]
                                    [(S y) (2 5)]))
  (let* ([c (carrier GUTIERREZ-EXAMPLE-PG8)]
         [d (earliest-duplicate c GUTIERREZ-EXAMPLE-PG8)]
         [fns (monotonic-maps/fn
               (left-bound d) (right-bound d)
               (left-bound d) (+ (left-bound d)
                                 (ge-base-width c)))])
    (check-equal? (transport GUTIERREZ-EXAMPLE-PG8 c d
                             (stream-ref fns 2))
                  (ge [(P x) (1 5)]
                      [(P u) (1 3)]
                      [(P y) (2 5)]
                      [(S y) (3 7)]
                      [(P x) (5 9)]
                      [(S u) (5 7)]
                      [(S u) (6 9)]
                      [(S y) (6 9)])))
  (define weird-example
    (ge [(S x) (1 4)] [(S y) (4 6)] [(S x) (6 10)]
        [(S y) (1 2)] [1 (2 3)] [(S z) (3 5)] [(S z) (5 7)]
        [(S z) (7 9)] [1 (9 10)]))
  (let* ([c (carrier weird-example)]
         [d (earliest-duplicate c weird-example)])
    (for ([fn (monotonic-maps/fn (left-bound c) (right-bound c)
                                 (left-bound c) (+ (left-bound c)
                                                   (ge-base-width d)))]
          [expected (list (ge [(P x) (1 5)] [(P y) (1 3)] [1 (3 4)]
                              [(S z) (4 6)] [(S y) (5 7)] [(S z) (6 8)]
                              [(P x) (7 11)]
                              [(S y) (7 9)] [(S z) (8 10)]
                              [1 (9 10)] [1 (10 11)])
                          (ge [(P x) (1 5)] [(P y) (1 2)] [1 (2 4)]
                              [(S z) (4 6)] [(S y) (5 7)] [(S z) (6 8)]
                              [(P x) (7 11)]
                              [(S y) (7 8)] [1 (8 10)]
                              [(S z) (8 10)] [1 (10 11)])
                          (ge [(P x) (1 5)] [(P y) (1 2)] [1 (2 3)]
                              [(S z) (3 6)] [(S y) (5 7)] [(S z) (6 8)]
                              [(P x) (7 11)]
                              [(S y) (7 8)] [(S z) (8 10)]
                              [1 (8 9)] [1 (10 11)]))])
         (check-equal? (transport weird-example c d fn) expected)))
  (define reversed-example
    (ge [(S x) (1 6)] [(S y) (6 8)] [(S x) (8 10)]
        [(S y) (1 2)] [1 (2 3)] [(S z) (3 5)] [(S z) (5 7)]
        [(S z) (7 9)] [1 (9 10)]))
  (let* ([c (carrier reversed-example)]
         [d (earliest-duplicate c reversed-example)])
    (for
     ([fn (monotonic-maps/fn
           (left-bound d) (right-bound d)
           (left-bound d) (+ (left-bound d)
                             (ge-base-width c)))]
      [expected (list (ge [(P x) (1 6)] [(P y) (1 2)] [1 (2 3)] [(P z) (3 5)]
                          [(S z) (5 7)] [(S y) (6 8)] [(S z) (7 12)]
                          [(P x) (8 13)]
                          [(S y) (8 9)] [1 (9 10)] [(S z) (10 12)] [1 (12 13)])
                      (ge [(P x) (1 6)] [(P y) (1 2)] [1 (2 3)] [(P z) (3 5)]
                          [(S z) (5 7)] [(S y) (6 8)] [(S z) (7 11)]
                          [(P x) (8 13)]
                          [(S y) (8 9)] [1 (9 10)] [(S z) (10 12)] [1 (11 13)])
                      (ge [(P x) (1 6)] [(P y) (1 2)] [1 (2 3)] [(P z) (3 5)]
                          [(S z) (5 7)] [(S y) (6 8)] [(S z) (7 10)]
                          [(P x) (8 13)]
                          [(S y) (8 9)] [1 (9 10)]  [1 (10 13)] [(S z) (10 12)])
                      (ge [(P x) (1 6)] [(P y) (1 2)] [1 (2 3)] [(P z) (3 5)]
                          [(S z) (5 7)] [(S y) (6 8)] [(S z) (7 9)]
                          [(P x) (8 13)]
                          [(S y) (8 9)] [1 (9 13)] [1 (9 10)] [(S z) (10 12)]))])
     (check-equal? (transport reversed-example c d fn) expected))))


;;; Check whether a generalized equation is solved: no more variable bases.
(define (ge-solved? geqn)
  (not (for/or ([base geqn]) (svar-base? base))))

(module+ test
  (check-false (ge-solved? (ge [(S x) (1 2)] [1 (2 3)]
                               [1 (1 2)] [(S x) (2 3)])))
  (check-true (ge-solved? (ge [(P x) (1 2)] [1 (2 3)]
                              [1 (1 2)] [(P x) (2 3)]))))

