#lang racket/base
(require "spaces.rkt" "shared.rkt" "transform.rkt" "concrete.rkt" "abstract.rkt"
         (for-syntax syntax/parse racket/base)
         racket/unit
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
                       #'(let loop () (define vs (sync lr)) (write vs p) (newline p) (newline p) (loop))))))]))

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
(define vspace (User-Space (list vclov) #f #t))
(define CESK-lang
  (Language
   'LC/CESK
   (hash
    'Variable (External-Space symbol? (λ (e) 1) #f #f)
    'Env (User-Space (list (Map (Space-reference 'Variable) (Address-Space 'bindings))) #f #f)
    'Expr (User-Space (list vref vapp (Space-reference 'Pre-value)) #t #f)
    'With-env (User-Space (list vclo) #f #f)
    'Pre-value (User-Space (list vlam) #t #f)
    'Value vspace
    'Frame (User-Space (list vkar vkfn) #f #f)
    'Kont (User-Space (list vmt vkcons) #f #f)
    'States (User-Space (list vstate) #f #f))
   (set (list 'Pre-value 'Expr))))

(define-unit CESK-conc-parms@
  (import)
  (export language-parms^)
  (define alloc gensym)
  (define Ξ #hash()) ;; No meta-functions in simple CESK.
  (define L CESK-lang)
  (define (trace-update state choices τ̂) τ̂))

(define-unit CESK-abs-parms@
  (import)
  (export language-parms^)
  (define alloc
    (λ (ς meta-ρ [hint #f])
       (match-define
        (Abs-State (variant (== vstate eq?)
                            (vector (variant (Variant 'Closure _) (vector e ρ)) κ)) σ μ τ̂)
        ς)
       (match hint
         [`(application ,(Variant-field 'State 1) ,(Variant-field 'Kcons 1))
          (cons e hint)]
         [`(argument-eval ,(Variant-field 'State 1) ,(Variant-field 'Kcons 1))
          ;; should be an address
          (hash-ref meta-ρ 'κ (λ () (error 'alloc "Expected to be called with env containing κ ~a" meta-ρ)))]
         [`(function-eval (Let-binding 0))
          (cons (hash-ref meta-ρ 'x (λ () (error 'alloc "Expected to be called with env containing x ~a" meta-ρ)))
                hint)]
         [_ (error 'alloc "Bad hint ~a" hint)])))
  (define (trace-update ς choices τ̂) τ̂)
  (define Ξ #hash())
  (define L CESK-lang))

(define-values/invoke-unit/infer
  (export language-impl^)
  #;
  (export (rename language-impl^
                  [c/expression-eval expression-eval]
                  [c/rule-eval rule-eval]
                  [c/mf-eval mf-eval]))
  (link CESK-abs-parms@ abstract-semantics@))

(define CESK-reduction
  (list
   (Rule 'variable-lookup
         (variant vstate
                  (vector
                   (variant vclo (vector (variant vref (vector (Avar 'x)))
                                         (Avar 'ρ)))
                   (Avar 'κ)))
         (variant vstate (vector (Rvar 'v) (Rvar 'κ)))
         (list (Binding (Avar 'v) (Store-lookup read (Map-lookup pure 'ρ (Term pure (Rvar 'x)) #f #f))))
         read)
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
         '()
         pure)
   (Rule 'argument-eval
         (variant vstate
                  (vector (Bvar 'v vspace)
                          (variant vkcons (vector (variant vkar (vector (Avar 'e) (Avar 'ρ)))
                                                  (Avar 'κ)))))
         (variant vstate
                  (vector (variant vclo (vector (Rvar 'e) (Rvar 'ρ)))
                          (variant vkcons (vector (variant vkfn (vector (Rvar 'v)))
                                                  (Rvar 'κ)))))
         '()
         pure)
   (Rule 'function-eval
         (variant vstate
                  (vector (Bvar 'v vspace)
                          (variant vkcons
                                 (vector (variant vkfn
                                                (vector (variant vclov
                                                                 (vector (variant vlam (vector (Avar 'x) (Avar 'e)))
                                                                         (Avar 'ρ)))))
                                         (Avar 'κ)))))
         (variant vstate
                  (vector (variant vclo (vector (Rvar 'e) (Rvar 'ρ*)))
                          (Rvar 'κ)))
         (list (Binding (Avar 'a) (MAlloc allocs 'bindings))
               (Binding (Avar 'ρ*) (Map-extend pure 'ρ (Term pure (Rvar 'x)) (Term pure (Rvar 'a)) #f))
               (Store-extend (Term pure (Rvar 'a)) (Term pure (Rvar 'v)) #f))
         write/alloc)))

(define-values (abs-lang rec-addrs abstract-spaces)
  (abstract-language CESK-lang))
(printf "Abstract language:~%") (pretty-print abs-lang)
(printf "Recursive positions:~%") (pretty-print rec-addrs)
(printf "Abstract spaces:~%") (pretty-print abstract-spaces)
(newline)
(define abs-semantics
  (for/list ([rule (in-list CESK-reduction)])
    (abstract-rule abs-lang rec-addrs #hash() rule)))
(when #t
  (pretty-print abs-semantics))
(define-values (hint-fn hint-stx) (alloc-skeleton abs-semantics #hash()))
(displayln (syntax->datum hint-stx))

(define (c/apply-reduction-relation rules)
  (apply-reduction-relation rule-eval rules))
(define (c/apply-reduction-relation* rules)
  (apply-reduction-relation*/memo rule-eval rules))

(define (inject L e)
  (define term (sexp-to-dpattern/check e 'Expr L))
  (mk-Abs-State (variant vstate (vector (variant vclo (vector term #hash()))
                                        (variant vmt #())))
                '()))
(define (run L expr)
  ((c/apply-reduction-relation* CESK-reduction) (inject L expr)))
(define (a/run L expr)
  ((c/apply-reduction-relation* abs-semantics) (inject L expr)))
(parameterize ([current-logger (make-logger 'match-info)])
  (log-thread 'info)
  (define seq (box #f))
  (collect-garbage)
  (collect-garbage)
  (collect-garbage)
  (time (set-box! seq (in-set (a/run CESK-lang '(App (Lam x (Ref x))
                                                     (Lam y (Ref y)))))))
  (for/list ([out (unbox seq)])
    (match-define (Abs-State tm store-spaces μ τ̂) out)
    (printf "(Abs-State ~a ~a ~a ~a)~%" (dpattern->sexp tm) store-spaces μ τ̂)
    out))
(sleep 1)
