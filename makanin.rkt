#lang racket

(require "generalized-eqn.rkt"
         "boundary-enum.rkt"
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
        [(not (admissible? ge)) (stream)]
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
