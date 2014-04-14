#lang racket/base
(require "spaces.rkt" "shared.rkt" "transform.rkt" "concrete.rkt"
         (for-syntax syntax/parse racket/base)
         racket/pretty racket/set racket/match)

(define-syntax log-thread
  (syntax-parser
    [(_ kind (~optional (~seq #:file path:expr (~bind [port (λ (p body)
                                                               #`(call-with-output-file*
                                                                  path
                                                                  (λ (#,p) #,body)
                                                                  #:exists 'replace))]))
                        #:defaults ([port (λ (p body) #`(let ([#,p (current-output-port)]) #,body))])))
     #`(let ([lr (make-log-receiver (current-logger) kind)])
         (thread (λ () 
                    #,((attribute port)
                       #'p
                       #'(let loop () (define vs (sync lr)) (write vs p) (newline p) (loop))))))]))

(define (rule-lookup rules name)
  (for/or ([rule (in-list rules)] #:when (equal? name (Rule-name rule))) rule))

(define vref (Variant 'Ref (vector (Space-reference 'Variable))))
(define vapp (Variant 'App (vector (Space-reference 'Expr)
                                   (Space-reference 'Expr))))
(define vlam (Variant 'Lam (vector (Space-reference 'Variable)
                                   (Space-reference 'Expr))))
(define vclo (Variant 'Closure (vector (Space-reference 'Expr) (Space-reference 'Env))))
;;; REFINEMENT 
(define vclov (Variant 'Closure (vector (Space-reference 'Pre-value)
                                       (Space-reference 'Env))))
(define vkar (Variant 'Ar (vector (Space-reference 'Expr) (Space-reference 'Env))))
(define vkfn (Variant 'Fn (vector (Space-reference 'Value))))
(define vmt (Variant 'mt #()))
(define vkcons (Variant 'Kcons (vector (Space-reference 'Frame)
                                       (Space-reference 'Kont))))
(define vstate (Variant 'State (vector (Space-reference 'With-env) (Space-reference 'Kont))))
(define CESK-lang
  (Language
   'LC/CESK
   (hash
    'Variable (External-Space symbol? (λ (e) 1) #f #f)
    'Env (User-Space (list (Map (Space-reference 'Variable) (Address-Space 'bindings))) #f)
    'Expr (User-Space (list vref vapp (Space-reference 'Pre-value)) #t)
    'With-env (User-Space (list vclo) #f)
    'Pre-value (User-Space (list vlam) #t)
    'Value (User-Space (list vclov) #f)
    'Frame (User-Space (list vkar vkfn) #f)
    'Kont (User-Space (list vmt vkcons) #f)
    'States (User-Space (list vstate) #f))))

(define CESK-reduction
  (list
   (Rule 'variable-lookup
         (variant vstate
                  (vector
                   (variant vclo (vector (variant vref (vector (Avar 'x)))
                                         (Avar 'ρ)))
                   (Avar 'κ)))
         (variant vstate (vector (Rvar 'v) (Rvar 'κ)))
         (list (Binding (Avar 'v) (Store-lookup (Map-lookup 'ρ (Term (Rvar 'x)) #f #f)))))
   (Rule 'application
         (variant vstate
                  (vector
                   (variant vclo (vector (variant vapp (vector (Avar 'e0) (Avar 'e1)))
                                         (Avar 'ρ)))
                   (Avar 'κ)))
         (variant vstate
                  (vector (variant vclo (vector (Rvar 'e0) (Rvar 'ρ)))
                          (variant vkcons
                                   (vector (variant vkar (vector (Rvar 'e1) (Rvar 'ρ)))
                                           (Rvar 'κ)))))
         '())
   (Rule 'argument-eval
         (variant vstate
                  (vector (Bvar 'v 'Value)
                          (variant vkcons (vector (variant vkar (vector (Avar 'e) (Avar 'ρ)))
                                                  (Avar 'κ)))))
         (variant vstate
                  (vector (variant vclo (vector (Rvar 'e) (Rvar 'ρ)))
                          (variant vkcons (vector (variant vkfn (vector (Rvar 'v)))
                                                  (Rvar 'κ)))))
         '())
   (Rule 'function-eval
         (variant vstate
                  (vector (Bvar 'v 'Value)
                          (variant vkcons
                                 (vector (variant vkfn
                                                (vector (variant vclov
                                                                 (vector (variant vlam (vector (Avar 'x) (Avar 'e)))
                                                                         (Avar 'ρ)))))
                                         (Avar 'κ)))))
         (variant vstate
                  (vector (variant vclo (vector (Rvar 'e) (Rvar 'ρ*)))
                          (Rvar 'κ)))
         (list (MAlloc 'a)
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
  (mk-State (variant vstate (vector (variant vclo (vector term #hash()))
                                    (variant vmt #())))))
(define (run L expr)
  ((c/apply-reduction-relation* CESK-lang CESK-reduction #hash()) (inject L expr)))
(parameterize ([current-logger (make-logger 'match-info)])
 (log-thread 'info)
 (for/list ([out (in-set (run CESK-lang '(App (Lam x (Ref x))
                                              (Lam y (Ref y)))))])
   (match-define (State tm store-spaces) out)
   (printf "(State ~a ~a)~%" (dpattern->sexp tm) store-spaces)
   out))
(sleep 2)