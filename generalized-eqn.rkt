#lang racket

(require (for-syntax syntax/parse
                     "ge-base.rkt"
                     "utils.rkt")
         "boundary-enum.rkt"
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
  [eqn->ge-list (-> word? word?
                    ge?)]
  [ge-bases/label (-> ge? any/c
                      ge?)]
  [ge-columns (-> ge? (listof natural?))]
  [svars (-> ge? (set/c svar?))]
  [gconsts (-> ge? (set/c gconst?))]
  [new-gvars (-> ge? (hash/c symbol? natural?))]
  [carrier (-> ge? (or/c ge-base? false?))]
  [critical-boundary (-> ge? natural?)]
  [transport-bases (-> ge? (listof ge-base?))]
  [earliest-duplicate (-> ge-base? ge?
                          ge-base?)]
  [base-shift-length (-> ge? natural?)]
  [base-shift! (-> ge? natural?
                   void?)]
  [transport! (-> ge? void?)]
  [transport (-> ge? ge-base? ge-base? (-> natural? natural?)
                 ge?)]
  [ge-contradiction? (-> ge? boolean?)]
  [ge-solved? (-> ge? boolean?)]
  [generators-by-column (-> ge?
                            (hash/c natural?
                                    (listof generator?)))]))

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
    [(_ v:id) #'(svar v)]))
(define-syntax (P stx)
  (syntax-parse stx
    [(_ v:id) #'(pvar v)]))
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
  (define generator-bases
    (for/list ([base ge] #:when (generator-base? base)) base))
  (define all-columns (ge-columns ge))
  (define occupied-columns
    (sort (for/list ([gb generator-bases]) (left-bound gb)) <))
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

;;; Identify all sequence variables used in a GE.
(define (svars ge)
  (for/set ([base ge] #:when (svar-base? base)) (ge-base-label base)))

;;; Identify all generator constants used in a GE.
(define (gconsts ge)
  (for/set ([base ge] #:when (gconst-base? base)) (ge-base-label base)))



;;; Given a GE, construct GVar entries (up to one per column) such that every
;;; column will have at least one GVar or GConst base. Construct a hash which
;;; associates each new GVar entry with its original column location.
;;; GE -> [Hash-of Symbol Natural]
(define (new-gvars ge)
  (define worklist (empty-columns ge))
  (for/hash ([column worklist])
            ;; For debugging, it might be helpful to have a name that reflects
            ;; which column this generator variable is meant to cover.
            (define new-name
              (gensym (string-append "col_" (number->string column) "_")))
            (values new-name column)))

(module+ test
  ;; Extract the debug-friendly base that was used to generate the GVar's name
  (define (collapse-gvar g)
    (gvar (string->symbol
           (first
            (regexp-match
             #rx"col_[0-9]*"
             (symbol->string (gvar-name g)))))))
  
  (define NEWVARS-A (new-gvars GUTIERREZ-EXAMPLE-A))
  (check-equal? (sort (hash-values NEWVARS-A) <)
                '(1 5))
  (define NEWVARS-B (new-gvars GUTIERREZ-EXAMPLE-B))
  (check-equal? (sort (hash-values NEWVARS-B) <)
                '(1 4 7)))


;;; Append a collection of GVars specified in a hash to an existing GE.
;;; [Hash-of Symbol Natural] GE -> GE
(define (add-gvars vs ge)
  (append
   (sort (for/list ([(var col) vs])
                   (ge-base (gvar var) (vector col (add1 col))))
         ge-<=)
   ge))

(module+ test
  (define (collapse-gvar-bases ge)
    (for/list ([base ge])
              (if (gvar-base? base)
                  (ge-base (collapse-gvar (ge-base-label base))
                           (ge-base-boundaries base))
                  base)))
  
  (define PADDED-A (add-gvars NEWVARS-A GUTIERREZ-EXAMPLE-A))
  (check-equal? (collapse-gvar-bases PADDED-A)
                (ge [(gvar 'col_1) (1 2)]
                    [(gvar 'col_5) (5 6)]
                    [(S x) (1 2)] [1 (2 3)] [2 (3 4)] [(S y) (4 6)]
                    [(S y) (1 3)] [2 (3 4)] [1 (4 5)] [(S x) (5 6)]))
  (define PADDED-B (add-gvars NEWVARS-B GUTIERREZ-EXAMPLE-B))
  (check-equal? (collapse-gvar-bases PADDED-B)
                (ge [(gvar 'col_1) (1 2)]
                    [(gvar 'col_4) (4 5)]
                    [(gvar 'col_7) (7 8)]
                    [(S x) (1 5)] [1 (5 6)] [2 (6 7)] [(S y) (7 8)]
                    [(S y) (1 2)] [2 (2 3)] [1 (3 4)] [(S x) (4 8)])))


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
  (check-equal? (list->set (stream->list
                            (eqn->ge-list (list (svar 'x) 1)
                                          (list 2 (svar 'x)))))
                ;; BBB, BLRB, BRLB
                (set (ge [(S x) (0 1)] [1 (1 2)] [2 (0 1)] [(S x) (1 2)])
                     (ge [(S x) (0 1)] [1 (1 3)] [2 (0 2)] [(S x) (2 3)])
                     (ge [(S x) (0 2)] [1 (2 3)] [2 (0 1)] [(S x) (1 3)]))))


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


;;; Determine the shift length -- how far must the carrier and transport bases
;;; be moved in order to meet the carrier's dual?
(define (base-shift-length geqn)
  (- (right-bound (earliest-duplicate (carrier geqn) geqn))
     (right-bound (carrier geqn))))

(module+ test
  (check-equal? (base-shift-length (ge [(S z) (0 3)]
                                       [(S z) (0 3)]))
                0)
  (check-equal? (base-shift-length (ge [4 (0 1)]
                                       [(S z) (1 2)]
                                       [(S z) (0 1)]
                                       [5 (1 2)]))
                1)
  (check-equal? (base-shift-length GUTIERREZ-EXAMPLE-A) 3)
  (check-equal? (base-shift-length GUTIERREZ-EXAMPLE-B) 3))


;;; Destructively shift a base right by the given distance (use negative
;;; distance for left shift).
(define (base-shift! base dist)
  (vector-map! (λ (bound) (+ bound dist)) (ge-base-boundaries base)))

(module+ test
  (let ([TEST-VAR-BASE (ge-base (svar 'q) (vector 0 3 7))])
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
;;; Note: This makes the sometimes unsafe assumption that the carrier and target
;;; bases cover the same number of columns.
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
                 #:when (not (equal? (ge-base-label base)
                                     (ge-base-label carr))))
                base)
      (for/list ([base geqn] #:when (not (eq? base carr))) base)))

(module+ test
  (define G1 (map ge-base-clone GUTIERREZ-EXAMPLE-A))
  (define G1/t1 (transport! G1))
  (check-equal? (sort G1/t1 ge-<=)
                (sort (ge [(S x) (4 5)] [1 (5 6)] [2 (3 4)]
                          [2 (3 4)] [1 (4 5)] [(S x) (5 6)])
                      ge-<=))
  (define G1/t2 (transport! (map ge-base-clone G1/t1)))
  (check-equal? (sort G1/t2 ge-<=)
                (sort (ge [1 (5 6)] [2 (3 4)]
                          [2 (3 4)] [1 (5 6)])
                      ge-<=))

  (define G1A (map ge-base-clone PADDED-A))
  (define G1A/t1 (transport! G1A))
  

  (define G2 (map ge-base-clone GUTIERREZ-EXAMPLE-B))
  (define G2/t1 (transport! G2))
  (check-equal? (sort G2/t1 ge-<=)
                (sort (ge [1 (5 6)] [2 (6 7)] [(S y) (7 8)]
                          [(S y) (4 5)] [2 (5 6)] [1 (6 7)])
                      ge-<=))

  (define G2A (map ge-base-clone PADDED-A)))


;;; Path-specified replacement for `transport!' procedure: instead of
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
  (sort (flatten (for/list ([base widened-ge])
                           (cond [(erasable? base) (erase base)]
                                 [(shiftable? base) (list (erase base)
                                                          (shift base))]
                                 [else base])))
        ge-<=))

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


;;; Check whether a generalized equation has a contradiction: two constant
;;; bases in the same column with different labels.
(define (ge-contradiction? geqn)
  (define const-bases
    (sort (for/list ([base geqn] #:when (gconst-base? base)) base) ge-<=))
  (define (overlap-conflict bases)
    (and (> (length bases) 1)
         (or (and (= (left-bound (first bases))
                     (left-bound (second bases)))
                  (not (equal? (ge-base-label (first bases))
                               (ge-base-label (second bases)))))
             (overlap-conflict (rest bases)))))
  (overlap-conflict const-bases))

(module+ test
  (check-true (ge-contradiction? (ge [3 (0 1)] [4 (1 2)]
                                       [2 (0 1)] [4 (1 2)])))
  (check-false (ge-contradiction? (ge [(S a) (0 1)] [4 (1 2)]
                                        [2 (0 1)] [4 (1 2)])))
  (check-false (ge-contradiction? (ge [(S a) (0 1)] [4 (1 2)]
                                        [(S b) (0 1)] [4 (1 2)])))
  (check-false (ge-contradiction? (ge [(S a) (0 1)] [4 (1 2)]
                                        [4 (0 1)] [(S b) (1 2)]))))


;;; Check whether a generalized equation is solved: no more variable bases.
(define (ge-solved? geqn)
  (not (for/or ([base geqn]) (svar-base? base))))

(module+ test
  (check-false (ge-solved? G1/t1))
  (check-true (ge-solved? G1/t2)))


;;; Given a solved generalized equation, identify which bases are located at
;;; each column.
;;; The GBC hash of a GE's initial state can be used to construct the form of
;;; each sequence variable's solution. The GBC of a GE after it has been solved
;;; via transport! identifies the generator constant each generator must stand
;;; for (if there are multiple distinct generators, we have a contradiction).
;;; GE -> [Hash Natural [List-of Generator]]
(define (generators-by-column ge)
  (for/hash ([col (ge-columns ge)])
            (values col
                    (for/list ([base ge]
                               #:when (and (= col (left-bound base))
                                           (generator-base? base)))
                              (ge-base-label base)))))

(module+ test
  (define (summarize-gbc h)
    (sort (for/list ([(k v) h])
             (list k (sort (map (λ (x) (if (gvar? x) (collapse-gvar x) x)) v)
                           label-<)))
         (λ (x y) (< (first x) (first y)))))
  (check-equal? (summarize-gbc (generators-by-column PADDED-A))
   `([1 (,(gvar 'col_1))]
     [2 (1)]
     [3 (2 2)]
     [4 (1)]
     [5 (,(gvar 'col_5))]))
  (check-equal? (summarize-gbc (generators-by-column PADDED-B))
   `([1 (,(gvar 'col_1))]
     [2 (2)]
     [3 (1)]
     [4 (,(gvar 'col_4))]
     [5 (1)]
     [6 (2)]
     [7 (,(gvar 'col_7))])))

