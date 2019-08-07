#lang racket

(require data/union-find
         racket/hash
         "generalized-eqn.rkt"
         "enumerate.rkt"
         "diophantine.rkt"
         "ge-base.rkt"
         "utils.rkt")

(provide
 (contract-out
  [solution? contract?]
  [eqv-reln/c (-> contract? contract?)]
  [monoid-results (parametric->/c
                   [T]
                   (-> (listof (or/c symbol? gconst?))
                       (listof (or/c symbol? gconst?))
                       (-> ge? T)
                       (stream/c T)))]
  [solve-monoid-eqn* (->* [(listof (or/c symbol? gconst?))
                           (listof (or/c symbol? gconst?))]
                          [(-> ge? boolean?)]
                          (stream/c solution?))]
  [solve-monoid-eqn (->* [(listof (or/c symbol? gconst?))
                          (listof (or/c symbol? gconst?))]
                         [(-> ge? boolean?)]
                         (or/c solution? false?))]
  [solve-monoid-eqn*/t (-> (listof (or/c symbol? gconst?))
                           (listof (or/c symbol? gconst?))
                           (stream/c (list/c solution? (eqv-reln/c gconst?))))]
  [semigroup-results (parametric->/c
                      [T]
                      (-> (listof (or/c symbol? gconst?))
                          (listof (or/c symbol? gconst?))
                          (-> ge? T)
                          (stream/c T)))]
  [solve-semigroup-eqn* (->* [(listof (or/c symbol? gconst?))
                              (listof (or/c symbol? gconst?))]
                             [(-> ge? boolean?)]
                             (stream/c solution?))]
  [solve-semigroup-eqn (->* [(listof (or/c symbol? gconst?))
                             (listof (or/c symbol? gconst?))]
                            [(-> ge? boolean?)]
                            (or/c solution? false?))]
  [solve-semigroup-eqn*/t (-> (listof (or/c symbol? gconst?))
                              (listof (or/c symbol? gconst?))
                              (stream/c (list/c solution? (eqv-reln/c gconst?))))]
  [solve-ge* (->* [ge?] [(-> ge? boolean?)]
                  (stream/c solution?))]
  [solve-ge (->* [ge?] [(-> ge? boolean?)]
                 (or/c solution? false?))]
  [ge-sat? (-> ge? boolean?)]
  [transport* (->* [ge?] [(-> ge? boolean?)]
                   (stream/c ge?))]))

;;; Given a generalized equation, produce a stream of all possible final results
;;; of using `transport' on the GE. If the carrier and dual have multiple
;;; possible alignments, all of them should be tried.
;;; However, if there are multiple candidates for carrier, only use one.
;;; TODO: Cut off search depth when a GE is known to be wider than the
;;; length-minimum solution.
;;; GE [Optional: GE -> Boolean] -> [Stream-of GE]
(define (transport* ge [prune admissible?])
  ;; Identify the carrier and dual (if none, return singleton stream)
  (define c (carrier ge))
  (cond [(not c) (stream ge)]
        ;; Exclude this result if any generator base spans multiple columns
        [(for/or ([base ge])
                 (and (gconst-base? base)
                      (not (= 1 (ge-base-width base)))))
         (stream)]
        ;; Exclude this result if an associated linear Diophantine equation
        ;; system has no solution.
        [(not (prune ge)) (stream)]
        [else
         (let* ([d (earliest-duplicate c ge)]
                ;; Enumerate the possible column-relabeling functions
                ;; - if carrier is shorter than dual,
                ;;     enumerate fns : carrier range -> dual range
                ;; - if carrier is longer than dual, 
                ;;     enumerate fns : dual range -> expanded dual range
                [relabelers
                 (if (<= (ge-base-width c)
                         (ge-base-width d))
                     ;; Add new boundaries in the carrier's zone
                     (monotonic-maps/fn (left-bound c) (right-bound c)
                                        (left-bound c) (+ (left-bound c)
                                                          (ge-base-width d)))
                     ;; Add new boundaries in the dual's zone
                     (monotonic-maps/fn (left-bound d) (right-bound d)
                                        (left-bound d) (+ (left-bound d)
                                                          (ge-base-width c))))]
                ;; Build stream of results of single transport step
                ;; Recur on each element of single-step result stream
                [new-geqns (for/stream ([r relabelers])
                                       (transport ge c d r))])
           (for/fold ([completed-geqns (stream)])
                     ([stepped new-geqns])
             (stream-append completed-geqns (transport* stepped prune))))]))

;;; Is this generalized equation solvable?
;;; GE [Optional: GE -> Boolean] -> Boolean
(define (ge-sat? ge [prune admissible?])
  (not (stream-empty? (transport* ge prune))))

;;; Interpret a solution provided by Inez.
;;; String -> [Hash Natural [GeneratorConstant U #f]] U #f
(define (interpret-soln result)
  (if (string-prefix? result "unsat") #f
      (for/hash ([line (string-split result "\n")]
                 #:when (regexp-match #rx"col_[0-9]+_[0-9]+ -> 1" line))
                (match (regexp-match* #rx"[0-9]+" line)
                  [(list column value one) (values (string->number column)
                                                   (string->number value))]))))

;;; A Solution for a generalized equation is a
;;;   [Hash Symbol [Vector [GeneratorConstant U #f]]]
;;; The hash maps symbols (the names of sequence variables) to vectors of
;;; generator constants, except with #f appearing in positions where the GE does
;;; not require any specific constant.
(define solution? (hash/c symbol? (vector/c (or/c gconst? false?))))

;;; An EqvReln on some datatype T is a
;;;   [Listof [Set T]]
;;; where no T appears in multiple sets.
(define (eqv-reln/c T?) (listof (set/c T?)))

;;; After all rounds of transport are done, every base with a given variable
;;; should have the same column width, so every column in the GE can be
;;; associated with a particular column within variables whose bases include
;;; that table column. Accumulate a hash from variables to mutable vectors of
;;; sequence generators by traversing the GE and using the contents of variable
;;; bases' covered columns.
;;; If any position in a result variable is #f at the end of this procedure,
;;; that position is underdetermined by the generalized equation and can be
;;; any sequence generator.
;;; GE [Hash Natural GeneratorConstant] -> Solution
(define (var-soln ge col-soln)
  ;; Determine the column widths of all sequence variables appearing in a GE
  ;; (there had better be only one width per var), and initialize a hash to map
  ;; each var to a mutable vector of corresponding width containing all #f.
  (define soln (for/hash ([base ge] #:when (var-base? base))
                         (values (ge-base-name base)
                                 (make-vector (ge-base-width base) #f))))
  ;; For each var base in the GE, update the corresponding solution vector
  ;; with the corresponding column values.
  (for ([base ge] #:when (var-base? base))
       (let ([soln-vec (hash-ref soln (ge-base-name base))])
         (for ([ge-col (in-range (left-bound base) (right-bound base))]
               [var-col (in-range (right-bound base))])
              (vector-set! soln-vec var-col
                           (or (vector-ref soln-vec var-col)
                               (hash-ref col-soln ge-col #f))))))

  soln)

;;; Produce all transport-derived solutions for a generalized equation.
;;; GE [Optional: GE -> Boolean] -> [Stream Solution]
(define (solve-ge* ge [prune admissible?])
  (define transport-results (transport* ge prune))
  (define inez-solutions
    (for/stream ([ge* transport-results])
                (inez-check (merged-LDE-system ge* #t))))
  (for/stream ([soln inez-solutions]
               [ge* transport-results]
               #:when (not (string-prefix? soln "unsat")))
              (var-soln ge* (interpret-soln soln))))
;;; Variant: produce any solution for a GE, or #f if there is none.
(define (solve-ge ge [prune admissible?])
  (for/first ([s (solve-ge* ge prune)]) s))
;;; Variant: produces the minimal equivalence relation which makes each
;;; candidate solution acceptable.
(define (solve-ge*/t ge)
  (define ((canonicalize eqv-reln) base)
    (if (gconst-base? base)
        (for/first ([eqv-class eqv-reln]
                    #:when (set-member? eqv-class (ge-base-label base)))
                   (ge-base (set-first eqv-class)
                            (ge-base-boundaries base)))
        base))
  (define transport-results (transport* ge singleton-alphabet-admissible?))
  (define eqv-relns
    (for/stream ([ge* transport-results])
                (define meqv (minimal-equiv ge*))
                meqv))
  (define inez-solutions
    (for/stream ([ge* transport-results]
                 [eqv-reln eqv-relns])
                (define soln
                  (inez-check
                   (merged-LDE-system (map (canonicalize eqv-reln) ge*) #t)))
                soln))
  (for/stream ([soln inez-solutions]
               [ge* transport-results]
               [eqv-reln eqv-relns]
               #:when (not (string-prefix? soln "unsat")))
              (list (var-soln ge* (interpret-soln soln))
                    eqv-reln)))


;;; Given a free semigroup equation, consider the generalized equations which
;;; can be produced from it (i.e., all possible alignments of its components),
;;; and process each with the passed-in solver procedure. This is the core
;;; solution-collecting logic for handling semigroup equations.
;;; Since this procedure is specifically for a free semigroup, it is assumed
;;; that no variable stands for the empty sequence.
;;; [List [GConst U Symbol]] [List [GConst U Symbol]] [GE -> T] -> [Stream T]
(define (semigroup-results left right ge->solns)
  (for/fold ([all-solns (stream)])
            ([ge (lists->ge* left right)])
    (stream-append all-solns (ge->solns ge))))
;;; Produce a stream of all solutions.
;;; [List [GConst U Symbol]] [List [GConst U Symbol]] [Optional: GE -> Boolean]
;;; -> [Stream Solution]
(define (solve-semigroup-eqn* left right [prune admissible?])
  (semigroup-results left right (λ (ge) (solve-ge* ge prune))))
;;; Produce any solution for a free semigroup equation (#f if none).
;;; [List [GConst U Symbol]] [List [GConst U Symbol]] [Optional: GE -> Boolean]
;;; -> Solution
(define (solve-semigroup-eqn left right [prune admissible?])
  (for/first ([s (solve-semigroup-eqn* left right prune)]) s))
;;; Produce a stream of solutions, each accompanied by the minimal equivalence
;;; relation that makes the solution acceptable.
;;; [List [GConst U Symbol]] [List [GConst U Symbol]]
;;; -> [Stream [List Solution [EqvReln GConst]]]
(define (solve-semigroup-eqn*/t left right)
  (semigroup-results left right solve-ge*/t))


;;; Given a free monoid equation, consider all possible semigroup equations that
;;; might represent solutions to it. Each free semigroup equation comes from
;;; dropping some subset of the sequence variables from the free monoid equation
;;; and assuming they stand for the empty sequence.
;;; [List [GConst U Symbol]] [List [GConst U Symbol]]
;;; [[List [GConst U Symbol]] [List [GConst U Symbol]] -> [Stream T]]
;;; [T Solution -> T]
;;; -> [Stream T]
(define (monoid-results left right semigroup-eqn->solns merge)
  (define vars (set-union (for/set ([x left] #:when (symbol? x)) x)
                          (for/set ([x right] #:when (symbol? x)) x)))
  (define semigroup-solns   ; [Stream T]
    (for/fold ([all-solns (stream)])
              ([empties (subsets vars)])
      (define more-solns    ; [Stream T]
        (semigroup-eqn->solns
         (for/list ([x left]  #:when (not (set-member? empties x))) x)
         (for/list ([x right] #:when (not (set-member? empties x))) x)))
      (define empties-soln  ; Solution
        (for/hash ([x empties])
                  (values x (vector))))
      (stream-append (for/stream ([s more-solns] #:when s)
                                 (merge s empties-soln))
                     all-solns)))
  ;; TODO: old code explicitly filtered #f entries out of this stream -- why?
  semigroup-solns)
;;; Produce a stream of solutions.
;;; [List [GConst U Symbol]] [List [GConst U Symbol]] [Optional: GE -> Boolean]
;;; -> [Stream Solution]
(define (solve-monoid-eqn* left right [prune admissible?])
  (monoid-results left right (λ (l r) (solve-semigroup-eqn* l r prune)) hash-union))
;;; Produce any solution for a free monoid equation (#f if none).
;;; [List [GConst U Symbol]] [List [GConst U Symbol]] [Optional: GE -> Boolean]
;;; -> Solution
(define (solve-monoid-eqn left right [prune admissible?])
  (for/first ([s (solve-monoid-eqn* left right prune)]) s))
;;; Produce a stream of solutions, each accompanied by the associated minimal
;;; equivalence relation.
;;; [List [GConst U Symbol]] [List [GConst U Symbol]]
;;; -> [Stream [List Solution [EqvReln GConst]]]
(define (solve-monoid-eqn*/t left right)
  (monoid-results left right solve-semigroup-eqn*/t
                  (λ (soln/eqv empties)
                    (list (hash-union (first soln/eqv) empties)
                          (second soln/eqv)))))

;;; Given a GE with all transport steps completed, identify the minimal
;;; equivalence relation on generators which would make the GE solvable.
;;; GE -> [Listof [Setof GConst]]
(define (minimal-equiv ge) ; [Hash Symbol GE-base]
  ;; Pick a "canonical" occurrence of each variable
  (define last-occurrences
    (for/hash ([base ge] #:when (var-base? base))
              (values (ge-base-name base) base)))
  ;; Which columns are aliased due to appearing at the same internal position
  ;; in two bases labeled with the same variable?
  (define column-aliases (make-hash)) ; [Hash Natural [Set Natural]]
  (for ([col (ge-columns ge)])
       (hash-extend! column-aliases col col))
  (for ([base ge] #:when (var-base? base))
       (for ([offset (ge-base-width base)])
            (define here (+ offset (left-bound base)))
            (define there
              (+ offset (left-bound
                         (hash-ref last-occurrences (ge-base-name base)))))
            (hash-extend! column-aliases here there)
            (hash-extend! column-aliases there here)))
  ;; Which generators appear in which columns?
  (define column-contents (make-hash)) ; [Hash Natural [Set GConst]]
  (for ([base ge]
        #:when (gconst-base? base))
       (for ([c (hash-ref column-aliases (left-bound base))])
        (hash-extend! column-contents c (ge-base-label base))))
  ;; Any two generators that appear in the same column must be equated.
  (define uf-sets
    (for/hash ([c (gconsts ge)])
              (values c (uf-new c))))
  (for ([(column contents) column-contents])
       (define fst (set-first contents))
       (for ([another contents]) (uf-union! (hash-ref uf-sets fst)
                                            (hash-ref uf-sets another))))
  ;; Construct the equivalence classes from the union-find sets
  (define eqv-classes (make-hash))
  (for ([(label ufs) uf-sets])
       (hash-extend! eqv-classes
                     (uf-find (hash-ref uf-sets label))
                     label))
  (for/list ([(k v) eqv-classes]) v))
