#lang racket

(provide
 (contract-out
  [bounds (-> natural? natural?
              (stream/c (listof (one-of/c 'B 'L 'R))))]
  [locate* (parametric->/c
            [T]
            (->* [(-> T boolean?) (sequence/c T)] [natural?]
                 (listof natural?)))]
  [left-bounds (-> (sequence/c (one-of/c 'B 'L 'R))
                   (listof natural?))]
  [right-bounds (-> (sequence/c (one-of/c 'B 'L 'R))
                    (listof natural?))]
  [monotonic-maps/fn (->i ([lo1 natural?]
                           [hi1 natural?]
                           [lo2 natural?]
                           [hi2 natural?])
                          #:pre (lo1 hi1 lo2 hi2)
                          (and (<= lo1 hi1) (<= lo2 hi2))
                          [result (stream/c (-> natural? natural?))])]
  [partitions (-> natural?
                  (stream/c (listof (listof natural?))))]
  [subsets (-> sequence? (stream/c set?))
           ;; Actually want something like this, but set/c doesn't seem to play
           ;; nice with parametric contracts.
           #;(parametric->/c
              [T]
              (-> (sequence/c T)
                  (stream/c (set/c T))))]))


;;;; How can two sides of an equation can be put in alignment?

;;; If we have l and r symbols on the left and right sides,
;;; there are l+1 and r+1 boundaries to place for the respective sides.
;;; The boundary sequence must start and end with 'B since the two equated
;;; words must start and end at the same time.
;;; A more sophisticated boundary enumerator should treat (1,1) as the base
;;; case -- returning '((B)) -- and choose 'B for the start of all sequences.
(define (bounds left-len right-len)
  ;; bounds : Nat Nat -> [Stream-of [List-of Bound]]
  ;; Given the number of boundaries on left and right, enumerate the orderings
  ;; of left- and right-boundaries. At each point, use one of:
  ;;  - 'L
  ;;  - 'R
  ;;  - 'B
  (define (bounds* left right)
    (define (use-left)
      (stream-map (λ (b) (cons 'L b)) (bounds* (sub1 left) right)))
    (define (use-right)
      (stream-map (λ (b) (cons 'R b)) (bounds* left (sub1 right))))
    (define (use-both)
      (stream-map (λ (b) (cons 'B b)) (bounds* (sub1 left) (sub1 right))))
    (cond
      [(and (<= left 1) (<= right 1)) (stream '(B))]
      [(<= left 1) (use-right)]
      [(<= right 1) (use-left)]
      [else (stream-append (use-left) (use-right) (use-both))]))
  (stream-map (λ (b) (cons 'B b))
       (bounds* left-len right-len)))


;;; Identify positions in a list that have acceptable values
;;; [T -> Bool] [Sequence-of T] Nat? -> [List-of Nat]
(define (locate* f bs [loc 0])
  (for/list ([b bs]
             [i (length bs)]
             #:when (f b))
            i))

;;; Identify which locations in a boundary list have a left boundary
;;; [Sequence-of [U 'B 'L 'R]] -> [List-of Nat]
(define (left-bounds b) (locate* (λ (sym) (member sym '(B L))) b))

;;; Identify which locations in a boundary list have a right boundary
;;; [Sequence-of [U 'B 'L 'R]] -> [List-of Nat]
(define (right-bounds b) (locate* (λ (sym) (member sym '(B R))) b))


;;;; If we're moving bases from a narrow carrier zone to a wider dual zone,
;;;; how can we map carrier-zone boundaries to dual-zone boundaries in a way
;;;; that maps endpoints to endpoints and preserves ordering?
;;;;   or equivalently...
;;;; If we're moving bases from a wider carrier zone to a narrower dual zone,
;;;; how can we widen the dual zone by inserting new boundaries so that it
;;;; matches the carrier's width?

;;; Enumerate end-preserving monotonic injections f from [0,m] to [0,n],
;;; that is, f(0)=0 and f(m)=n (note: if m>n, there are no such functions)
;;; Give each result as a list whose ith element is f(i)
;;; Natural Natural -> [Stream-of [List-of Natural]]
(define (monotonic-maps/list m n)
  (for/stream ([c (combinations (- n 2) (- n m))])
              (combination->monotonic-map c)))


;;; Enumerate end-preserving monotonic injections from [lo1,hi1] to [lo2,hi2],
;;; representing them as Racket procedures.
;;; Natural Natural Natural Natural -> [Stream-of [Natural -> Natural]]
(define (monotonic-maps/fn lo1 hi1 lo2 hi2)
  (for/stream ([xs (monotonic-maps/list (+ (- hi1 lo1) 1) (+ (- hi2 lo2) 1))])
              ;; Generalize the mapping specified by the destination list by
              ;; having everything left of lo1 map equally far left of lo2 and
              ;; everything right of hi1 map equally far right of hi2.
              (λ (n) (cond [(< n lo1) (+ n (- lo2 lo1))]
                           [(> n hi1) (+ n (- hi2 hi1))]
                           [else (+ lo2 (list-ref xs (- n lo1)))]))))


;;; Convert a list of match/skip marks ('M and 'S) with m matches and n skips
;;; into a monotonic injection from [0,m+2) to [0,m+n+2) (list of outputs).
;;; [List-of [U 'M 'S]] -> [List-of Natural]
(define (combination->monotonic-map c)
  ;; We actually wanted the combination listing as the core of an
  ;; endpoint-preserving function, so add the endpoinds in here.
  (define big-c (append '(M) c '(M)))
  (define skip-locs (for/list ([sym big-c]
                               [n (in-naturals)]
                               #:when (symbol=? sym 'S))
                              n))
  (define range (+ (length c) 2))
  (for/list ([n (in-range range)]
             #:when (not (member n skip-locs)))
            n))


;;; Enumerate combinations of r elements from a list of length n.
;;; Give each result as a length-n list, with r occurrences of 'S and
;;; n-r occurrences of 'M.
;;; Natural Natural -> [Stream-of [List-of [U 'M 'S]]]
(define (combinations n r)
  ;; [Stream-of [List-of [U 'M 'S]]] -> [Stream-of [List-of [U 'M 'S]]]
  (define (cons-to-all sym cstrm) (stream-map (λ (x) (cons sym x)) cstrm))
  ;; Natural Natural -> [Stream-of [List-of [U 'M 'S]]]
  (define (c* matches skips)
    (cond
      ;; The "overdrawn budget" case indicates that we're asking for things that
      ;; don't exist (and the empty combination is not one of them).
      [(or (< matches 0) (< skips 0)) empty-stream]
      ;; Proper base case: fully spent our budget of both matches and skips
      [(and (<= matches 0) (<= skips 0)) (stream '())]
      [(= 0 matches) (cons-to-all 'S (c* matches (sub1 skips)))]
      [(= 0 skips) (cons-to-all 'M (c* (sub1 matches) skips))]
      [else (stream-append (cons-to-all 'S (c* matches (sub1 skips)))
                           (cons-to-all 'M (c* (sub1 matches) skips)))]))
  (c* (- n r) r))


;;; Enumerate partitions of a set of n elements, representing a partition as a
;;; list of lists of naturals in which each of {1, ..., n} appears once.
;;; Natural -> [Stream-of [List-of [List-of Natural]]]
(define (partitions n)
  (cond [(= 0 n) (stream '())]
        [else
         (for/fold ([updated-partitions (stream)])
                   ([p (partitions (sub1 n))])
           (stream-append updated-partitions (add-to-partitions n p)))]))
;;; Given a partition of some finite set, represented as a list of lists,
;;; generate all possible ways a new thing could be added to the partition.
;;; ∀ T. T [List-of [List-of T]] -> [Stream-of [List-of [List-of T]]]
(define (add-to-partitions new p)
  (stream-cons
   (cons (list new) p)
   (for/stream ([expansion (length p)])
               ;; The ith iteration adds the new element to the ith section
               (for/list ([section p]
                          [pos (length p)])
                         (if (= pos expansion) (cons new section) section)))))

;;; Enumerate subsets of the given finite sequence with unique elements.
;;; [Sequence T] -> [Stream [Set T]]
(define (subsets s)
  (for/fold ([all-subsets (list (set))])
            ([elt s])
    (stream-append all-subsets
                   (for/stream ([subset all-subsets]) (set-add subset elt)))))
