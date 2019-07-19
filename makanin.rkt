#lang racket

(require "generalized-eqn.rkt"
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
         #;
         (printf "\nHandling the base ~v\n" base)
         (for ([ge-col (in-range (left-bound base) (right-bound base))]
               [svar-col (in-range (right-bound base))])
              #;
              (printf "Updating position ~v in ~v with ~v\n"
                      svar-col
                      soln-vec
                      (hash-ref col-soln ge-col #f))
              (vector-set! soln-vec svar-col
                           (or (vector-ref soln-vec svar-col)
                               (hash-ref col-soln ge-col #f))))))

  soln)
