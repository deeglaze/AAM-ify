#lang racket/base

#|
This module defines the concrete semantics of reduction for languages written
in the spaces.rkt format.
|#

(require racket/match racket/set racket/dict racket/promise
         racket/list
         "spaces.rkt"
         "shared.rkt")
(provide c/apply-reduction-relation
         c/apply-reduction-relation*)

;; c/match : Language → Pattern DPattern Map[Symbol, DPattern] → Option[Map[Symbol, DPattern]]
;; Concrete match. References' ∀? component does not matter.
;; There is at most one match.
;; If there is a match, the result is the binding environment. Otherwise #f.
(define ((c/match L) pattern data ρ)
  (let c/match ([pattern pattern] [data data] [ρ ρ])
    (match* (pattern data)
      [((Bvar x Space-name) d)
       (match (dict-ref ρ x -unmapped)
         [(== -unmapped eq?)
          (and (if Space-name (in-space? d L Space-name) #t)
               (dict-set ρ x d))]
         [other (if (equal? other d)
                    ρ
                    #f)])]
      [((Variant name comps) (Variant name data))
       (let recur ([comps comps] [data data] [ρ ρ])
         (match* (comps data)
           [('() '()) ρ]
           [((cons comp comps) (cons d data))
            (define ρop (c/match comp d ρ))
            (and ρop (recur comps data ρop))]
           [(_ _) #f]))]
      [(Rvar x) (error 'c/match "Unexpected reference in match pattern ~a" x)]
      [(atom atom) ρ]
      [(_ _) #f])))

;; c/expression-eval : Language Expression Map[Symbol,DPattern] Map[Symbol,Meta-function] → ℘(DPattern)
;; Concrete evaluation of expressions. Returns entire set of possible evaluations
;; due to Choose expressions.
(define (c/expression-eval* L e ρ Ξ)
  (define Lmatch (c/match L))
  (let c/expression-eval* ([e e] [ρ ρ])
    (define (eval* e) (c/expression-eval* e ρ))
    (match e
      [(Map-lookup* m kexpr default? dexpr)
       (define ks (eval* kexpr ρ))
       (define map (hash-ref ρ m (unbound-map-error 'map-ref m)))
       (define lazy-default ;; avoid allocating if no default
         (and default? (delay (eval* dexpr))))
       (for/fold ([res ∅]) ([k (in-set ks)])
         (match (hash-ref map k -unmapped)
           [(== -unmapped eq?)
            (if default?
                (set-union res (force lazy-default))
                (error 'map-ref "Key unmapped in map ~a: ~a" m k))]
           [v (set-add res v)]))]
      [(Map-extend* m kexpr vexpr trust-strong?)
       (define mv (hash-ref ρ m (unbound-map-error 'map-ext m)))
       (define ks (eval* kexpr))
       (define vs (eval* vexpr))
       (for*/set ([k (in-set ks)]
                  [v (in-set vs)])
         (hash-set mv k v))]

      ;; Shortcut for (Map-lookup* m (Term kpat) default? (Term dpat))
      [(Map-lookup m kpat default? dpat)
       (define k (pattern-eval kpat ρ))
       (set
        (hash-ref (hash-ref ρ m (unbound-map-error 'map-ref m))
                  k
                  (if default?
                      (λ () (pattern-eval dpat ρ))
                      (λ () (error 'map-ref "Key unmapped in map ~a: ~a" m k)))))]
      ;; Shortcut for (Map-extend* m (Term kpat) (Term vpat) trust-strong?)
      [(Map-extend m kpat vpat trust-strong?)
       (define mv (hash-ref ρ m (unbound-map-error 'map-ext m)))
       (define k (pattern-eval kpat ρ))
       (define v (pattern-eval vpat ρ))
       (set (hash-set mv k v))]

      [(Meta-function-call f arg)
       ;; meta-functions also have non-deterministic choice.
       (c/meta-function-eval L
                             (hash-ref Ξ f (λ () (error "Unknown meta-function ~a" f)))
                             (pattern-eval arg ρ))]
      [(If g t e)
       (define guard (eval* g))
       (cond [(set-member? guard #f)
              (if (= (set-count guard) 1)
                  (eval* e)
                  (set-union (eval* e)
                             (eval* t)))]
             [(set-empty? guard) guard]
             [else (eval* t)])]
      [(Equal l r)
       (for*/set ([lv (in-set (eval* l))]
                  [rv (in-set (eval* r))])
         (equal? lv rv))]

      ;; Really let with non-linear pattern weirdness.
      [(Let '() bexpr) (eval* bexpr)]
      [(Let (cons binding bindings) bexpr)
       (define-values (pat cexpr)
         (match binding
           [(PBinding pat rpat) (values pat (Term rpat))]
           [(EBinding pat cexpr) (values pat cexpr)]))
       (for*/union ([cv (in-set (eval* cexpr))]
                    [ρ* (in-value (Lmatch pat cv ρ))]
                    #:when ρ*)
         (c/expression-eval* (Let bindings bexpr) ρ*))]

      [(Alloc _) (set (Address (gensym)))]

      [(Term pat) (set (pattern-eval pat ρ))]

      [(Set-union exprs)
       (for/set ([args (in-set (list-of-sets→set-of-lists
                                             (map eval* exprs)))])
         ;; XXX: Probably shouldn't be an error
         (unless (andmap set? args)
           (error 'expression-eval "Cannot union non-set ~a" args))
         (apply set-union args))]
      [(Set-Add* set-expr exprs)
       (for/set ([args (in-set (list-of-sets→set-of-lists
                                             (map eval* (cons set-expr exprs))))])
         (define setv (first args))
         ;; XXX: Probably shouldn't be an error
         (unless (set? setv) (error 'expression-eval "Cannot add to non-set ~a" setv))
         (set-add* setv (rest args)))]
      [(Set-In set-expr expr)
       (for*/set ([setv (in-set (eval* set-expr))]
                  #:when (set? setv)
                  [v (in-set (eval* expr))])
         (set-member? setv v))]
      [(Empty-set) ∅]

      ;; We get a set of results from expr. We expect these results to be sets.
      ;; We want to embody any (all) choices from these sets, so we flatten them into
      ;; a set of possible results.
      [(Choose expr) (for/union ([res-set (in-set (eval* expr))]) res-set)]

      [bad (error 'expr-eval "Bad expression ~a" bad)])))



;; c/rule-eval* : Rule Map[Symbol,DPattern] DPattern Map[Symbol,Meta-function] → ℘(DPattern)
;; Evaluate a rule on some concrete term and return possible RHSs.
(define (c/rule-eval* L rule d Ξ)
  (define Lmatch (c/match L))
  (match-define (Rule name lhs rhs binding-side-conditions) rule)
  (match (Lmatch lhs d ρ₀)
    [#f ∅]
    [ρ (let bind-and-check ([bscs binding-side-conditions] [ρ ρ])
         (match bscs
           [(cons bsc bscs)
            (match bsc
              [(EBinding lhs* rhs*)
               (for*/union ([rv (in-set (c/expression-eval* L rhs* ρ Ξ))]
                            [ρop (in-value (Lmatch lhs* rv ρ))]
                            #:when ρop)
                 (bind-and-check bscs ρop))]
              ;; An alias for EBinding lhs* (Term rhs*)
              [(PBinding lhs* rhs*)
               (match (Lmatch lhs* (pattern-eval rhs* ρ) ρ)
                 [#f ∅]
                 [ρ* (bind-and-check bscs ρ*)])]
              ;; Anything else is considered an expression that must be truish to continue.
              [expr
               (define v (c/expression-eval* L expr ρ Ξ))
               ;; If only #f is a possibility, stop. Otherwise keep going.
               (if (and (= (set-count expr) 1)
                        (set-member? expr #f))
                   ∅
                   (bind-and-check bscs ρ))])]
           ;; Finished binding and checking side conditions. Evaluate right-hand-side.
           ['() (set (pattern-eval rhs ρ))]))]))

;; TODO?: Add ability to do safety checks on input/output belonging to a
;;        specified Space.

(define (c/meta-function-eval L mf argd Ξ)
  (match-define (Meta-function name rules trust/conc _) mf)
  (if trust/conc
      (trust/conc argd)
      ;; Use the first rule that matches.
      (for/or ([rule (in-list rules)]) (c/rule-eval* L rule argd Ξ))))

(define (c/apply-reduction-relation L rules term Ξ)
  (for/union ([rule (in-list rules)]) (c/rule-eval* L rule term Ξ)))

(define (c/apply-reduction-relation* L rules term Ξ)
  (define outs (c/apply-reduction-relation L rules term Ξ))
  (if (set-empty? outs)
      (set term)
      (for/union ([term* (in-set outs)])
        (c/apply-reduction-relation* L rules term* Ξ))))