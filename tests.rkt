#lang racket

(require rackunit)
(require "solve.rkt")

(define (check-sat left right)
  (check solve-monoid-eqn left right))
(define (check-unsat left right)
  (check (negate solve-monoid-eqn) left right))


(check-unsat '(x 1) '(x x x))

(check-sat '(x 1 2 y) '(y z))
