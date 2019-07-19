#lang racket

(require "ge-base.rkt"
         "generalized-eqn.rkt")

(provide
 (contract-out
  [LDE? contract?]
  [LDE-system? contract?]
  [LDE-systems (-> ge? (listof LDE-system?))]
  [LDE-system (-> ge? gconst? LDE-system?)]
  [merged-LDE-system (-> ge? LDE-system?)]
  [admissible? (-> ge? boolean?)]
  [inez-check (-> LDE-system? string?)]
  [inez-sat? (-> LDE-system? boolean?)]))

(module+ test (require rackunit)
  (define SIMPLE-SAT (ge [(S x) (1 3)] [1 (3 4)]
                         [1 (1 2)] [(S x) (2 4)]))
  (define SIMPLE-UNSAT (ge [(S x) (1 3)] [1 (3 4)]
                           [2 (1 2)] [(S x) (2 4)]))
  (define GUTIERREZ-EXAMPLE-A
    (ge [(S x) (1 2)] [1 (2 3)] [2 (3 4)] [(S y) (4 6)]
        [(S y) (1 3)] [2 (3 4)] [1 (4 5)] [(S x) (5 6)]))
  (define GUTIERREZ-EXAMPLE-B
    (ge [(S x) (1 5)] [1 (5 6)] [2 (6 7)] [(S y) (7 8)]
        [(S y) (1 2)] [2 (2 3)] [1 (3 4)] [(S x) (4 8)]))
  (define GUTIERREZ-EXAMPLE-PG8 (ge [(S u) (1 3)]
                                    [(S x) (5 8)]
                                    [(S x) (1 5)]
                                    [(S u) (6 8)]
                                    [(S y) (3 7)]
                                    [(S y) (2 5)]))
  (define WEIRD-EXAMPLE
    (ge [(S x) (1 4)] [(S y) (4 6)] [(S x) (6 10)]
        [(S y) (1 2)] [1 (2 3)] [(S z) (3 5)] [(S z) (5 7)]
        [(S z) (7 9)] [1 (9 10)])))

;;;; Each Generalized Equation is associated with a collection of systems of
;;;; linear Diophantine equations, one system for each character used in the GE
;;;; itself. That LDE system for a particular character encodes the claim that
;;;; all occurrences of any one sequence variable can agree as to how many
;;;; occurrences of that character appear in the sequence variable's meaning.

;;;; For example, we want to rule out string equations like XaY = YX. The two
;;;; possible GE representations of that equation correspond to the two possible
;;;; places for the LHS's "a": the end of the RHS's "Y" or the beginning of the
;;;; RHS's "X". Either option aligns an "X" from one side exactly in line with a
;;;; "Y" from the other, while also lining up the other "X" and "Y" in a way
;;;; that also includes an extra "a". Reasoning based on linear arithmetic says
;;;; each "X" occurrence and each "Y" occurrence must have the same number of
;;;; "a" occurrences (since alignment forces X=Y), but that the extra "a" also
;;;; means one must have one extra occurrence -- a contradiction which implies
;;;; that the string equation is unsolvable.


;;; Represent a linear Diophantine equation (LDE) as a list of the equated sums,
;;; with each sum represented as a list of summands, which may themselves be
;;; symbols (LDE variables) or naturals.
;;; For example, x+y = a+3+q = 2x is represented as '((x y) (a 3 q) (x x)).
(define (summand? x) (or (natural? x) (symbol? x)))
(define LDE? (listof (listof summand?)))
(define LDE-system? (listof LDE?))

;;; A Generalized Equation is admissible if every associated system of linear
;;; Diophantine equations is solvable.
;;; GE -> Boolean
(define (admissible? ge)
  (for/and ([ldes (LDE-systems ge)]) (inez-sat? ldes)))
(module+ test
  (check-true (admissible? SIMPLE-SAT))
  (check-false (admissible? SIMPLE-UNSAT)))

;;; Construct the LDE systems for every constant appearing in a GE.
;;; GE -> [Listof LDE-system]
(define (LDE-systems ge)
  (for/list ([c (gconsts ge)]) (LDE-system ge c)))

;;; Construct the LDE system associated with the given GE and constant. If the
;;; chosen constant does not actually appear in the GE, the resulting system
;;; will be trivially solvable.
;;; GE GeneratorConstant -> LDE-system
(define (LDE-system ge c)
  (append (svar-LDEs ge)
          (gconst-LDEs ge c)))

;;; Construct the LDEs associated with sequence variable bases in a GE. For
;;; each sequence variable used in a GE, equate the sums of the LDE variables
;;; associated with eachinterval of columns some base with that sequence
;;; variable spans.
;;; GE -> [Listof LDE]
(define (svar-LDEs ge)
  ;; Sorting the svar worklist is not necessary but makes testing easier
  (for/list ([svar (sort (set->list (svars ge))
                         (λ (x y) (symbol<? (svar-name x) (svar-name y))))])
            (for/list ([base (ge-bases/label ge svar)])
                      (span->LDE-sum (left-bound base)
                                     (right-bound base)))))
(module+ test
  (check-equal? (svar-LDEs SIMPLE-SAT)
                '([(col_1 col_2) (col_2 col_3)]))
  (check-equal? (svar-LDEs SIMPLE-UNSAT) (svar-LDEs SIMPLE-SAT))
  (check-equal? (svar-LDEs GUTIERREZ-EXAMPLE-PG8)
                '([(col_1 col_2) (col_6 col_7)]
                  [(col_5 col_6 col_7) (col_1 col_2 col_3 col_4)]
                  [(col_3 col_4 col_5 col_6) (col_2 col_3 col_4)])))

;;; Construct a single LDE that merges all single-constant LDEs.
;;; Once transport is finished, use this to construct a solution. The solution,
;;; if one exists, gives values for variables whose names have the form
;;; col_<C>_<N>. Assigning 1 means column C must contain the generator N. No
;;; column will have multiple different generators assigned because the presence
;;; of one generator base in a column produces an "=0" constraint for all other
;;; generators at that column.
;;; A single-generator system can be seen as a candidate for an unsatisfiable
;;; core of this larger system (though likely not a *minimal* one).
;;; GE -> LDE
(define (merged-LDE-system ge)
  ;; Like map, but apply the function to every atom in a nested list
  (define (map* f xs)
    (cond [(empty? xs) '()]
          [(list? (first xs)) (cons (map* f (first xs)) (map* f (rest xs)))]
          [else (cons (f (first xs)) (map* f (rest xs)))]))
  ;; Append the given tag string onto a string or symbol, but leave anything
  ;; else untouched.
  (define ((tag-var t) x)
    (cond [(string? x) (string-append x t)]
          [(symbol? x) (string->symbol (string-append (symbol->string x) t))]
          [else x]))
  (define single-LDEs
    (for/list ([c (gconsts ge)])
              (map* (tag-var (string-append "_" (number->string c)))
                    (LDE-system ge c))))
  ;; Require the sum of each column's generator variables to be 1
  (define col-sums
    (for/list ([col (ge-columns ge)])
              (list '(1)
                    (for/list ([gc (gconsts ge)])
                              ((tag-var (string-append "_" (number->string gc)))
                               (col->LDE-var col))))))
  (apply append col-sums single-LDEs))

;;; Construct the LDEs associated with a particular constant in a GE.
;;; GE GeneratorConstant -> [Listof LDE]
(define (gconst-LDEs ge c)
  (for/list ([base ge]
             #:when (gconst-base? base))
            `[(,(col->LDE-var (left-bound base)))
              (,(if (equal? c (ge-base-label base)) 1 0))]))
(module+ test
  (check-equal? (gconst-LDEs SIMPLE-UNSAT 1)
                '([(col_3) (1)] [(col_1) (0)]))
  (check-equal? (gconst-LDEs SIMPLE-UNSAT 2)
                '([(col_3) (0)] [(col_1) (1)])))

;;; Make a list of the column-associated variables in a particular column span,
;;; representing their sum in an LDE.
(define (span->LDE-sum l r)
  (for/list ([col (in-range l r)])
            (col->LDE-var col)))
(module+ test
  (check-equal? (span->LDE-sum 3 6) '(col_3 col_4 col_5))
  (check-equal? (span->LDE-sum 2 2) '())
  (check-equal? (span->LDE-sum 3 2) '()))

;;; What LDE variable corresponds to this column?
;;; Natural -> Symbol
(define (col->LDE-var col)
  (string->symbol (string-append "col_" (number->string col))))


;;; Invoke Inez on a system of linear Diophantine equations to determine whether
;;; the system is solvable.
;;; LDE-system -> String
(define (inez-check ldes)
  (define script-file (make-temporary-file "Inez_~a.ml"))
  (define script-port (open-output-file script-file
                                        #:exists 'truncate))
  (display (LDE-system->inez ldes) script-port)
  (close-output-port script-port)
  (define-values (inez-process inez-stdout inez-stdin inez-stderr)
    (subprocess #f #f #f
                (find-executable-path "inez.opt")
                script-file))
  (define inez-result (port->string inez-stdout))
  #;(printf "Inez result:\n~a\n\n" inez-result)
  inez-result)

;;; Does Inez say this LDE system is satisfiable?
;;; LDE-system -> Boolean
(define (inez-sat? ldes)
  (not (string-prefix? (inez-check ldes) "unsat")))
(module+ test
  (check-true (inez-sat? (LDE-system SIMPLE-SAT 1)))
  (check-false (inez-sat? (LDE-system SIMPLE-UNSAT 1)))
  (check-false (inez-sat? (LDE-system SIMPLE-UNSAT 2))))

;;; Convert a system of LDEs into an Inez script
;;; LDE-system -> String
(define (LDE-system->inez ldes)
  (string-append "open Script ;;\n\n"
                 (declare-vars ldes)
                 "\n\n"
                 (string-join (map LDE->inez ldes) "\n"
                              #:after-last "\n\n")
                 "solve_print_result() ;;\n"
                 (print-soln ldes)))

;;; Build Inez logic-variable declarations for all variables mentioned in a sum,
;;; LDE, or system of LDEs
;;; [LDE or LDE-system] -> String
(define (declare-vars l)
  (define vars (for/set ([e (flatten l)] #:when (symbol? e)) e))
  (define decls (for/list ([var vars])
                          (string-append "let "
                                         (symbol->string var)
                                         " = fresh_int_var () ;;")))
  (string-join decls "\n"))

;;; Generate Inez code that prints the solution for each variable in an LDE
;;; or LDE system (if there is a solution)
(define (print-soln l)
  (define vars (for/set ([e (flatten l)] #:when (symbol? e)) e))
  (define prints (for/list ([var vars])
                           (string-append "ideref_printf \""
                                          (symbol->string var)
                                          " -> %d\\n\" "
                                          (symbol->string var)
                                          " ;;")))
  (string-join prints "\n"))

;;; Turn an LDE into a constraint in Inez syntax
;;; LDE -> String
(define (LDE->inez lde)
  ;;; Focus on the case where there are at least two equated things
  (define (nontrivial-LDE->inez lde)
    (define lhs (sum->inez (first lde)))
    (define eqns
      (for/list ([rhs* (rest lde)])
                (string-append "(" lhs " = " (sum->inez rhs*) ")")))
    (string-join eqns " && "
                 #:before-first "constrain (~logic ("
                 #:after-last ")) ;;"))
  (if (<= (length lde) 1) "(* trivial constraint eliminated *)"
      (nontrivial-LDE->inez lde)))


;;; Convert an LDE sum into Inez syntax
;;; [Listof summand] -> String
(define (sum->inez sum)
  (string-join (for/list ([s sum])
                         (if (symbol? s)
                             (symbol->string s)
                             (number->string s)))
   " + "
   #:before-first "("
   #:after-last ")"))
