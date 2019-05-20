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
                    (listof natural?))]))

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

