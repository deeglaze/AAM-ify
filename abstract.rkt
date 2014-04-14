#lang racket/base
(require "spaces.rkt" "shared.rkt" "ternary-counting.rkt"
         (only-in racket/bool implies)
         racket/match racket/dict racket/set racket/list
         racket/unit)
(provide abstract-semantics@)
#|
The abstract semantics differs from the concrete semantics in the following ways:
- equality matching is uncertain and is aided by cardinality analysis
- map lookup is uncertain and is aided by cardinality analysis
- meta-function evaluation must be done via fixed point computation
- Map-extend in maps with "abstract" domain change to weak updates (range already is lifted to ℘)
|#

;; classify-external : Language Any → Option[(external external-space Any)]
;; Find the first external space in L whose pred v satisfies.
(define (classify-external L v)
  (for/or ([space (in-dict-values (language-spaces L))]
           #:when (and (External-Space? space)
                       ((External-Space-pred space) v)))
    (external space v)))

(define (∣γ∣>1 v μ)
  (let aliased? ([v v])
    (match v
      [(variant var data)
       (for/or ([d (in-vector data)]) (aliased? d))]
      ;; INVARIANT/ASSUMPTION: abstract-ffuns do not have distinct keys that are a/equal?=#t
      [(or (abstract-ffun map) (discrete-ffun map))
       (for/or ([(k v) (in-dict map)])
         (or (aliased? k) (aliased? v)))]
      [(? dict? map) (for/or ([v (in-dict-values map)]) (aliased? v))]
      [(or (Address-Structural a) (Address-Egal a)) (eq? (hash-ref μ a 0) 'ω)]
      [(? set? vs) (for/or ([v (in-set vs)]) (aliased? v))]
      [atom #f])))

(define-unit abstract-semantics@
  (import language-parms^)
  (export language-impl^)

;; Takes language to get access to external spaces' cardinality analyses.
(define (a/equal? d₀ d₁ store-spaces μ)
  (define/match (egal-equal? a₀ a₁)
    [((Address-Egal space a) (Address-Egal space a))
     (match (hash-ref μ a₀ 'ω)
       [1 #t]
       ['ω 'b.⊤]
       [0 (error 'a/match "Live address with count 0: ~a (Counts ~a) (Store ~a)" a₀ μ store-spaces)])]
    [(_ _) #f])

  (define (ffun-equal? f₀ f₁)
    (if abs?
        (b∧ (ffun-⊑? f₀ f₁)
            (ffun-⊑? f₁ f₀))
        (concrete-ffun-equal? f₀ f₁)))

  ;; Slow path: linearly look for a key "equal" to k with "equal" values.
  (define (slow-equal k v f)
    (for/b∨ ([(k₁ v₁) (in-dict f)])
            (b∧ (a/equal? k k₁)
                (a/equal? v v₁))))

  (define (ffun-⊑? dom f₀ f₁)
    (for/b∧ ([(k v) (in-dict f₀)])
            (match (dict-ref f₁ k -unmapped)
              [(== -unmapped eq?) (slow-equal k v f₁)]
              [v₁ ;; fast path: check the structurally equal key
               (b∨ (a/equal? v₀ v₁)
                   (slow-equal k v f₁))])))

  (define (concrete-ffun-equal? m₀ m₁)
    (and (= (dict-count m₀) (dict-count m₁))
         (for/b∧ ([(k₀ v₀) (in-dict m₀)])
                 (match (dict-ref m₁ k₀ -unmapped)
                   ;; Concrete domains w/o structural equality are actually abstract.
                   ;; Note this is different from the concrete semantics.
                   [(== -unmapped eq?) #f]
                   ;; Note we don't use b∨ with the slow path
                   [v₁ (a/equal? v₀ v₁)]))))

  (define (discrete-ffun-equal? m₀ m₁)
    (and (= (dict-count m₀) (dict-count m₁))
         (for/b∧ ([(k₀ v₀) (in-dict m₀)])
                 (match (dict-ref m₁ k₀ -unmapped)
                   [(== -unmapped eq?) #f]
                   [v₁ (b∧
                        ;; Discrete maps get structural equality on keys, but can only be 
                        ;; truly equal if the key has cardinality 1.
                        (if (∣γ∣>1 k₀ μ) 'b.⊤ #t)
                        (a/equal? v₀ v₁))]))))

  (define (equal-step d₀ d₁)
    (match* (d₀ d₁)
      [((variant v ds₀) (variant v ds₁))
       (for/b∧ ([d₀ (in-vector ds₀)]
                [d₁ (in-vector ds₁)])
               (a/equal? d₀ d₁))]

      ;; Addresses are the same if they have cardinality 1. Distinct addresses don't overlap.
      [((? Address-Egal?) (? Address-Egal?))
       (egal-equal? d₀ d₁)]

      [((? Address-Structural? a₀) (? Address-Structural? a₁))
       (if (eq? (egal-equal? a₀ a₁) #t)
           #t
           ;; INVARIANT: not possible to be -unmapped since there must be
           ;; at least one value mapped in a store's address.
           (for*/bδ ([d₀ (in-set (store-ref store-spaces a₀))]
                     [d₁ (in-set (store-ref store-spaces a₁))])
                    (a/equal? d₀ d₁)))]

      [((? dict? m₀) (? dict? m₁)) (concrete-ffun-equal? m₀ m₁)]

      ;; If at least one map has qualification, we can check the other with the expectation of the same.
      ;; We log the incident for future debugging, since it seems like we shouldn't get this far.
      [((? dict? m₀) (abstract-ffun m₁))
       (log-info (format "Qualified/unqualified dictionary equality check ~a ~a" d₀ d₁))
       (ffun-equal? m₀ m₁)]
      [((abstract-ffun m₀) (? dict? m₁))
       (log-info (format "Qualified/unqualified dictionary equality check ~a ~a" d₀ d₁))
       (ffun-equal? m₀ m₁)]
      [((abstract-ffun m₀) (abstract-ffun m₁)) (ffun-equal? m₀ m₁)]
      ;; Discrete cases
      [((discrete-ffun m₀) (? dict? m₁))
       (log-info (format "Qualified/unqualified (discrete) dictionary equality check ~a ~a" d₀ d₁))
       (discrete-ffun-equal? m₀ m₁)]
      [((? dict? m₀) (discrete-ffun m₁))
       (log-info (format "Qualified/unqualified (discrete) dictionary equality check ~a ~a" d₀ d₁))
       (discrete-ffun-equal? m₀ m₁)]
      [((discrete-ffun m₀) (discrete-ffun m₁))
       (discrete-ffun-equal? m₀ m₁)]

      ;; OPT-OP: This has no information on discrete abstractions, thus n²logn instead of sometimes nlogn
      [((? set? s₀) (? set? s₁))
       (define (⊆? s₀ s₁)
         (for/b∧ ([v (in-set s₀)])
                 (for/b∨ ([v* (in-set s₁)])
                         (a/equal? v v*))))
       (b∧ (⊆? s₀ s₁) (⊆? s₁ s₀))]

      [(atom atom) #t]

      [((external ex v₀) (external ex v₁))
       (match-define (External-Space _ card precision special-equality) ex)
       (if special-equality
           (special-equality v₀ v₁ μ #;a/equal?)
           (match precision
             ['concrete (equal? v₀ v₁)]
             ['discrete-abstraction (b∧ (equal? v₀ v₁) (implies (eq? (card v₀ μ)) 'b.⊤))]
             ['abstract (error 'a/match "Cannot have non-discrete abstraction of external values without a custom equality relation ~a" d₀)]))]
      [(_ _) #f]))

  ;; Circular addresses are possible
  ;; OPT-OP?: Racket impl of equal? uses union-find instead of Map[_,Set[_]].
  ;;          Is that applicable here?
  (define seen (make-hasheq))
  (define (a/equal? d₀ d₁)
    (define checked-against (hash-ref! seen d₀ mutable-seteq))
    ;; already checked ⇒ assume equal
    ;; XXX: should this be #t or 'b.⊤?
    (or (set-member? checked-against d₁)
        (begin (set-add! checked-against d₁)
               (equal-step d₀ d₁))))

  (a/equal? d₀ d₁))

(define (a/match pattern data store-spaces ρ μ)
  ;; inner returns the quality of the match and the updated map.
  (define (inner pattern data ρ)
    (match* (pattern data)
      [((Bvar x Space) d)
       (match (dict-ref ρ x -unmapped)
         [(== -unmapped eq?)
          (define (do-update) (values #t (dict-set ρ x d)))
          (cond
           [Space ;; Space provided ⇒ check if in space.
            (if (in-space? L Space d)
                (do-update)
                (values #f #f))]
           [else (do-update)])]
         [other (values (a/equal? other d store-spaces μ) ρ)])]
         
      [((variant v comps) (variant v data))
       (for/fold ([b #t] [ρ ρ])
           ([comp (in-vector comps)]
            [d (in-vector data)])
         (define-values (b* ρ*) (inner comp d ρ))
         (define b** (b∧ b b*))
         #:final (not b**) ;; short-circuit on absolute non-match
         (values b** ρ*))]

      ;; Wildcard/don't-care
      [((? Anything?) d) (values #t ρ)]
      ;; TODO: Add better syntax checking to rule this out before interpretation.
      [((? Rvar?) x) (error 'a/match "Unexpected reference in match pattern ~a" x)]

      [(a₀ a₁) (values (a/equal? a₀ a₁ store-spaces μ) ρ)]))

  ;; TODO?: get rid of May and Must and just use multiple values
  (let-values ([(b ρ) (inner pattern data ρ)])
    (match b
      [#t (Must ρ)]
      [#f #f]
      ['b.⊤ (May ρ)])))

(define (expression-eval e store-spaces ρ μ)
  (let a/expression-eval* ([e e] [ρ ρ])
    (define (eval* e) (a/expression-eval* e ρ))
    (match e
      [(Store-lookup kexpr)
       (for/set ([kv (in-set (eval* kexpr))])
         (store-ref store-spaces kv))]
      
      [(Map-lookup m kexpr default? dexpr)
       (define ks (eval* kexpr))
       (define lazy-default ;; avoid allocating if no default
         (and default? (delay (eval* dexpr))))
       (match (hash-ref ρ m (unbound-map-error 'map-ref m))
         [(abstract-ffun map)
          (define-values (res found?)
            (for/fold ([res ∅]) ([k (in-set ks)])
              (define-values (res* found?)
                (for/fold ([res res] [found? found?])
                    ([(k* v) (in-dict map)])
                  (match (a/equal? k k* store-spaces μ)
                    [#f res]
                    [#t (set-add res v)]
                    ['b.⊤
                     (log-info (format "map-ref: Key may not be present in map ~a: ~a" m k))
                     ;; XXX: emit log entry detailing possible miss?
                     (set-union (set-add res v) (force lazy-default))])))
              (if found?
                  res*
                  (set-union res* (force lazy-default)))))]
         [(discrete-ffun map)
          (for/fold ([res ∅]) ([k (in-set ks)])
            (match (hash-ref map k -unmapped)
              [(== -unmapped eq?)
               (cond
                [default? (set-union res (force lazy-default))]
                [else
                 (log-info (format "map-ref: Key unmapped in map ~a: ~a" m k))
                 ∅])]
              [v (cond
                  [(∣γ∣>1 k μ)
                   (log-info (format "map-ref: Key may not be present in map ~a: ~a" m k))
                   ;; XXX: emit log entry detailing possible miss?
                   (set-union (set-add res v) (force lazy-default))]
                  [else
                   (set-add res v)])]))]
         [(? dict? map) ;; concrete domain map. Do same as concrete semantics.
          (for/fold ([res ∅]) ([k (in-set ks)])
            (match (hash-ref map k -unmapped)
              [(== -unmapped eq?)
               (if default?
                   (set-union res (force lazy-default))
                   (error 'map-ref "Key unmapped in map ~a: ~a" m k))]
              [v (set-add res v)]))])]

      [(Map-extend m kexpr vexpr trust-strong?)
       (define ks (eval* kexpr))
       (define vs (eval* vexpr))
       (define setter (if trust-strong? (λ (h k v) (hash-set h k (set v))) hash-add))
       (match (hash-ref ρ m (unbound-map-error 'map-ext m))
         [(abstract-ffun map)
          (for*/fold ([acc ∅]) ([k (in-set ks)]
                                [v (in-set vs)])
            ;; TODO: This explosion of nastiness is begging for a plug-in widening.
            ;; this may be the form of abstract-ffun having an (optional) extra function
            ;; that takes 〈map,trust-strong?, ks, vs, store-spaces, μ〉 and produces a set of maps
            ;; such that there is a galois connection between that set and the set this fallback produces.
            
            ;; Build two sets for keys that are strongly present or weakly (possibly) present.
            ;; Strongly present keys are in all possible maps. The rest have an exponential blowup.
            ;; OPT: we cut out the intermediate step and build the base map with strongly present keys.
            (define-values (base-map weakly)
              (for/fold ([base-map map] [weakly ∅]) ([k* (in-dict-keys map)])
                (match (a/equal? k k* store-spaces μ)
                  [#t (values (setter base-map v) weakly)]
                  [#f (values base-map weakly)]
                  ['b.⊤ (values base-map (set-add weakly k*))])))
            ;; Each key adds to possible maps
            (set-union acc
                       (for*/fold ([maps (set base-map)]) ([k* (in-set weakly)]
                                                           [map (in-set maps)])
                         (set-add maps (setter map k* v)))))]
         [(discrete-ffun map)
          ;; ASSUMPTION: abstract finite functions have a ℘ co-domain,
          ;; and values extended are elements of the set, not the type of the co-domain itself.
          ;; This should be weakened for better customizability in the future.
          ;; TODO?: allow non-determinism in vexpr to be absorbed into the abstract co-domain as a widening.
          (for*/set ([k (in-set ks)]
                     [v (in-set vs)])
            (setter map k v))]
         [(? dict? map)
          (for*/set ([k (in-set ks)]
                     [v (in-set vs)])
            (hash-set mv k v))])]

      [(Meta-function-call f arg)
       ;; meta-functions also have non-deterministic choice.
       (mf-eval store-spaces
                μ
                (hash-ref Ξ f (λ () (error "Unknown meta-function ~a" f)))
                (pattern-eval arg ρ))]
      [(If g t e)
       (define guard (eval* g))
       (cond [(set-member? guard #f)
              (if (= (set-count guard) 1)
                  (eval* e)
                  (set-union (eval* e)
                             (eval* t)))]
             [(set-empty? guard) ∅]
             [else (eval* t)])]
      [(Equal l r) (⦃b⦄ (a/equal? l r store-spaces μ))]

      ;; Really match-let
      [(Let '() bexpr) (eval* bexpr)]
      [(Let (cons binding bindings) bexpr)
       (match binding
         [(Binding pat cexpr)
          (for*/union ([cv (in-set (eval* cexpr))]
                       [ρ* (in-value (a/match pat cv ρ store-spaces))]
                       #:when ρ*)
            (define ρ**
              (match ρ*
                [(Must ρ) ρ]
                [(May ρ)
                 (log-info (format "Possible failed match in let ~a ~a" binding cv))
                 ρ]))
            (a/expression-eval* (Let bindings bexpr) ρ**))]
         [(Store-extend kexpr vexpr trust-strong?)
          ???])
       (match-define (Binding pat cexpr) binding)
       ]

      [(SAlloc) (Address-Structural (alloc ς))]
      [(QSAlloc hint) (Address-Structural (alloc ς hint))]
      [(MAlloc) (Address-Egal (alloc ς))]
      [(QMAlloc hint) (Address-Egal (alloc ς hint))]

      ;; ASSUMPTION: pat has been pre-transformed so that recursive constructions
      ;; are routed through the store(s)
      [(Term pat) (set (pattern-eval pat ρ))]

      [(In-Dom m kexpr)
       (define ks (eval* kexpr))
       (match (hash-ref ρ m (unbound-map-error 'map-ext m))
         [(abstract-ffun map)
          (⦃b⦄
           (for*/b∨ ([k (in-set ks)]
                     [k* (in-dict-keys map)])
                    (a/equal? k k* store-spaces μ)))]
         [(discrete-ffun map)
          (⦃b⦄
           (for/bδ ([kv (in-set ks)])
                   (b∧ (dict-has-key? map kv)
                       (implies (∣γ∣>1 kv μ) 'b.⊤))))]
         [(? dict? map)
          (for/set ([kv (in-set ks)])
            (dict-has-key? mv kv))])]

      [(Set-Union exprs)
       (for/set ([args (in-set (list-of-sets→set-of-lists
                                             (map eval* exprs)))]
                 #:when (or
                         (andmap set? args)
                         ;; HACK to log bad args without much extra code.
                         (not (log-info (format "Cannot union non-set ~a" args)))))
         (apply set-union args))]
      [(Set-Add* set-expr exprs)
       (for*/set ([args (in-set (list-of-sets→set-of-lists
                                              (map eval* (cons set-expr exprs))))]
                  [setv (in-value (first args))]
                  #:when (or (set? setv)
                             (not ;; HACK (same as above)
                              (log-info (format "Set-add* possibly given non-set ~a" setv)))))
         (set-add* setv (rest args)))]
      [(In-Set set-expr expr)
       (for*/set ([setv (in-set (eval* set-expr))]
                  #:when (or (set? setv)
                             ;; HACK
                             (not (log-info (format "In-set given non-set ~a" setv))))
                  [v (in-set (eval* expr))])
         (set-member? setv v))]
      [(Empty-set) ⦃∅⦄]

      ;; We get a set of results from expr. We expect these results to be sets.
      ;; We want to embody any (all) choices from these sets, so we flatten them into
      ;; a set of possible results.
      [(Choose expr) (for/union ([res-set (in-set (eval* expr))]) res-set)]

      [bad (error 'expr-eval "Bad expression ~a" bad)])))

(define (rule-eval rule store-spaces d)
  (match-define (Rule name lhs rhs binding-side-conditions) rule)
  (match-define (Abs-State d store-spaces μ) st)
  (match (a/match lhs d ρ₀ store-spaces μ)
    [#f ∅]
    [ρ (let bind-and-check ([bscs binding-side-conditions]
                            [ρ ρ]
                            [store-spaces store-spaces])
         (match bscs
           [(cons bsc bscs)
            (match bsc
              [(Binding lhs* rhs*)
               (for*/union ([rv (in-set (Leval rhs* store-spaces ρ μ))]
                            [ρop (in-value (a/match lhs* rv ρ store-spaces μ))]
                            #:when ρop)
                 (define ρ*
                   (match ρop
                     [(Must ρ) ρ]
                     [(May ρ)
                      (log-info (format "Possible misfire of rule due to imprecise match ~a ~a ~a" rule bsc rv))
                      ρ]))
                 (bind-and-check bscs ρ* store-spaces))]
              [(Store-extend key-expr val-expr trust-strong?)
               (define kvs (Leval key-expr store-spaces ρ μ))
               (define vvs (Leval val-expr store-spaces ρ μ))
               ;; TODO?: make trust-strong? 3 valued. Trust/strong-when-safe/monotonic.
               ;; We use cardinality analysis to determine safety of strong updates.
               (define setter (if trust-strong?
                                  (λ (k v) (store-set store-spaces k (set v)))
                                  store-add))
               (for*/union ([kv (in-set kvs)]
                            [vv (in-set vvs)])
                 (bind-and-check bscs ρ (setter kv vv)))]
              ;; Anything else is considered an expression that must be truish to continue.
              [expr
               (define v (Leval expr store-spaces ρ μ))
               ;; If only #f is a possibility, stop. Otherwise keep going.
               (if (and (= (set-count expr) 1)
                        (set-member? expr #f))
                   ∅
                   (bind-and-check bscs ρ store-spaces))])]

           ;; Finished binding and checking side conditions. Evaluate right-hand-side.
           ['() (set (Abs-State (pattern-eval rhs ρ) store-spaces μ))]))]))

(define (a/binding-eval* L alloc Ξ)
  ())

(define (a/meta-function-eval L mf argd store-spaces Ξ [μ #f])
  (error 'a/meta-function-eval)))