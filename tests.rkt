#lang racket/base
(require "spaces.rkt" "shared.rkt" "transform.rkt" "concrete.rkt"
         racket/pretty)

(define (rule-lookup rules name)
  (for/or ([rule (in-list rules)] #:when (equal? name (Rule-name rule))) rule))

(define CESK-lang
  (Language
   'LC/CESK
   (hash
    'Variable (External-Space symbol? (λ (e) 1) #f #f)
    'Env (User-Space (list (Map (Space-reference 'Variable) (Address-Space 'bindings))) #f)
    'Expr (User-Space (list (Variant 'Ref (vector (Space-reference 'Variable)))
                            (Variant 'App (vector (Space-reference 'Expr)
                                                (Space-reference 'Expr)))
                            (Space-reference 'Pre-value))
                      #t)
    'Pre-value (User-Space (list (Variant 'Lam (vector (Space-reference 'Variable)
                                                     (Space-reference 'Expr))))
                           #t)
    'Value (User-Space (list (Variant 'Closure
                                      (vector (Space-reference 'Pre-value)
                                            (Space-reference 'Env))))
                       #f)
    'Frame (User-Space (list (Variant 'Ar (vector (Space-reference 'Expr) (Space-reference 'Env)))) #f)
    'Kont (User-Space (list (Variant 'mt #())
                            (Variant 'Kcons (vector (Space-reference 'Frame)
                                                  (Space-reference 'Kont))))
                      #f))))

(define CESK-reduction
  (list
   (Rule 'variable-lookup
         (Variant 'State
                  (vector
                   (Variant 'Closure (vector (Variant 'Ref (vector (Avar 'x)))
                                             (Avar 'ρ)))
                   (Avar 'κ)))
         (Variant 'State
                  (vector (Rvar 'v)
                          (Rvar 'κ)))
         (list (Binding (Avar 'v) (Store-lookup (Map-lookup 'ρ (Term (Rvar 'x)) #f #f)))))
   (Rule 'application
         (Variant 'State
                  (vector
                   (Variant 'Closure (vector (Variant 'App (vector (Avar 'e0) (Avar 'e1)))
                                           (Avar 'ρ)))
                   (Avar 'κ)))
         (Variant 'State
                  (vector (Variant 'Closure (vector (Rvar 'e0) (Rvar 'ρ)))
                        (Variant 'Kcons
                                 (vector (Variant 'Ar (vector (Rvar 'e1) (Rvar 'ρ)))
                                       (Rvar 'κ)))))
         '())
   (Rule 'argument-eval
         (Variant 'State
                  (vector (Bvar 'v 'Value)
                        (Variant 'Kcons (vector (Variant 'Ar (vector (Avar 'e) (Avar 'ρ)))
                                              (Avar 'κ)))))
         (Variant 'State
                  (vector (Variant 'Closure (vector (Rvar 'e) (Rvar 'ρ)))
                        (Variant 'Kcons (vector (Variant 'Fn (vector (Rvar 'v)))
                                              (Rvar 'κ)))))
         '())
   (Rule 'function-eval
         (Variant 'State
                  (vector (Bvar 'v 'Value)
                        (Variant 'Kcons
                                 (vector (Variant 'Fn
                                                (vector (Variant 'Closure
                                                               (vector (Variant 'Lam (vector (Avar 'x) (Avar 'e)))
                                                                     (Avar 'ρ)))))
                                       (Avar 'κ)))))
         (Variant 'State
                  (vector (Variant 'Closure (vector (Rvar 'e) (Rvar 'ρ*)))
                          (Rvar 'κ)))
         (list (Binding (Avar 'a) (Alloc))
               (Binding (Avar 'ρ*) (Map-extend 'ρ (Term (Rvar 'x)) (Term (Rvar 'a)) #f))
               (Store-extend (Term (Rvar 'a)) (Term (Rvar 'v)) #f)))))

(let-values ([(abs-lang rec-addrs abstract-spaces) (abstract-language CESK-lang)])
  (pretty-print abs-lang)
  (pretty-print rec-addrs)
  (pretty-print abstract-spaces)
  (when #f
    (pretty-print (for/list ([rule (in-list CESK-reduction)])
                    (abstract-rule abs-lang rec-addrs #hash() rule))))
  (when #t
    (pretty-print (abstract-rule abs-lang rec-addrs #hash() (rule-lookup CESK-reduction 'argument-eval)))))

(define (inject L e)
  (define term (sexp-to-dpattern/check e 'Expr L))
  (mk-State (Variant 'State (vector (Variant 'Closure (vector term #hash()))
                                    (Variant 'mt '())))))
(define (run L expr)
  ((c/apply-reduction-relation* CESK-lang CESK-reduction #hash()) (inject L expr)))

(run CESK-lang '(App (Lam x (Ref x))
                     (Lam y (Ref y))))