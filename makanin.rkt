#lang racket

(require racket/hash
         "generalized-eqn.rkt"
         "enumerate.rkt"
         "diophantine.rkt"
         "ge-base.rkt")


;;; Given a generalized equation, produce a stream of all possible final results
;;; of using `transport' on the GE. If the carrier and dual have multiple
;;; possible alignments, all of them should be tried.
;;; However, if there are multiple candidates for carrier, only use one.
;;; TODO: Cut off search depth when a GE is known to be wider than the
;;; length-minimum solution.
;;; GE -> [Stream-of GE]
(define (transport* ge)
  ;; Identify the carrier and dual (if none, return singleton stream)
  (define c (carrier ge))
  (cond [(not c) (stream ge)]
        ;; Exclude this result if an associated linear Diophantine equation
        ;; system has no solution.
        [(not (admissible? ge)) (stream)]
        ;; Exclude this result if any generator base spans multiple columns
        [(for/or ([base ge])
                 (and (generator-base? base)
                      (not (= 1 (ge-base-width base)))))
         (stream)]
        [else
         (let* ([d (earliest-duplicate c ge)]
                ;; Enumerate the possible column-relabeling functions
                ;; - if carrier is shorter than dual,
                ;;     enumerate functions from carrier range to dual range
                ;; - if carrier is longer than dual, 
                ;;     enumerate functions from dual range to expanded dual range
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
             (stream-append completed-geqns (transport* stepped))))]))

;;; Is this generalized equation solvable?
;;; GE -> Boolean
(define (ge-sat? ge)
  (stream-empty? (transport* ge)))

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
(define (svar-soln ge col-soln)
  ;; Determine the column widths of all sequence variables appearing in a GE
  ;; (there had better be only one width per var), and initialize a hash to map
  ;; each svar to a mutable vector of corresponding width containing all #f.
  (define soln (for/hash ([base ge] #:when (or (svar-base? base)
                                               (pvar-base? base)))
                         (values (ge-base-name base)
                                 (make-vector (ge-base-width base) #f))))
  ;; For each svar base in the GE, update the corresponding solution vector
  ;; with the corresponding column values.
  (for ([base ge] #:when (or (svar-base? base)
                             (pvar-base? base)))
       (let ([soln-vec (hash-ref soln (ge-base-name base))])
         (for ([ge-col (in-range (left-bound base) (right-bound base))]
               [svar-col (in-range (right-bound base))])
              (vector-set! soln-vec svar-col
                           (or (vector-ref soln-vec svar-col)
                               (hash-ref col-soln ge-col #f))))))

  soln)

;;; Produce all transport-derived solutions for a generalized equation.
;;; GE -> [Stream Solution]
(define (solve*-ge ge)
  (define transport-results (transport* ge))
  (define inez-solutions
    (for/stream ([ge* transport-results])
                (inez-check (merged-LDE-system ge*))))
  (for/stream ([soln inez-solutions]
               [ge* transport-results]
               #:when (not (string-prefix? soln "unsat")))
              (svar-soln ge* (interpret-soln soln))))
;;; Variant: produce any solution for a GE, or #f if there is none.
(define (solve-ge ge)
  (for/first ([s (solve*-ge ge)]) s))

;;; Given a free semigroup equation, consider the generalized equations which
;;; can be produced from it (i.e., all possible alignments of its components),
;;; and generate a stream containing a solution for each solvable GE. If none
;;; are solvable, the resulting stream will be empty.
;;; Since this procedure is specifically for a free semigroup, it is assumed
;;; that no variable stands for the empty sequence.
;;; [List [GConst U Symbol]] [List [GConst U Symbol]] -> [Stream Solution]
(define (solve*-semigroup-eqn left right)
  (for/fold ([all-solns (stream)])
            ([ge (lists->ge* left right)])
    (stream-append all-solns (solve*-ge ge))))
;;; Variant: produce any solution for a free semigroup equation (#f if none).
(define (solve-semigroup-eqn left right)
  (for/first ([s (solve*-semigroup-eqn left right)]) s))

;;; Given a free monoid equation, consider all possible semigroup equations that
;;; might represent solutions to it. Each free semigroup equation comes from
;;; dropping some subset of the sequence variables from the free monoid equation
;;; and assuming they stand for the empty sequence.
(define (solve*-monoid-eqn left right)
  (define vars (set-union (for/set ([x left] #:when (symbol? x)) x)
                          (for/set ([x right] #:when (symbol? x)) x)))
  (define semigroup-solns
    (for/fold ([all-solns (stream)])
              ([empties (subsets vars)])
      (define more-solns
        (solve*-semigroup-eqn
         (for/list ([x left]  #:when (not (set-member? empties x))) x)
         (for/list ([x right] #:when (not (set-member? empties x))) x)))
      (define empties-soln
        (for/hash ([x empties])
                  (values x (vector))))
      (stream-append (for/stream ([s more-solns] #:when s)
                                 (hash-union s empties-soln))
                     all-solns)))
  (for/stream ([soln semigroup-solns] #:when soln) soln))
;;; Variant: produce any solution for a free monoid equation (#f if none).
(define (solve-monoid-eqn left right)
  (for/first ([s (solve*-monoid-eqn left right)]) s))