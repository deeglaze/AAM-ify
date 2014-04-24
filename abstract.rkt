#lang racket/base
(require "spaces.rkt" "shared.rkt" "ternary-counting.rkt"
         (only-in racket/bool implies)
         (only-in racket/function identity const)
         (for-syntax syntax/parse racket/base racket/match racket/syntax
                     (only-in racket/string string-join))
         racket/match racket/dict racket/set racket/list
         racket/unit
         racket/trace)
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
  (for/or ([space (in-dict-values (Language-spaces L))]
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
      [(or (Address-Structural space a) (Address-Egal space a)) (eq? (hash-ref μ a 0) 'ω)]
      [(? set? vs) (for/or ([v (in-set vs)]) (aliased? v))]
      [atom #f])))

(define (term-⊔ v₀ v₁)
  (match* (v₀ v₁)
    [(v v) v]
    [((Abs-Data payload₀) (Abs-Data payload₁))
     (Abs-Data (set-union payload₀ payload₁))]
    [((Abs-Data payload) v)
     (Abs-Data (set-add payload v))]
    [(v (Abs-Data payload))
     (Abs-Data (set-add payload v))]))

(define (in-data v)
  (match v
    [(Abs-Data S) (in-set S)]
    [singleton (in-value singleton)]))

(define absb.⊤ (Abs-Data (⦃b⦄ 'b.⊤)))
(define (to-data v)
  (if (eq? v 'b.⊤)
      absb.⊤
      v))

;; An answer is a map from a list of choices to a Abs-Result/effect.
(define answer⊥ #hash())
(define (answer-⊔ ans₀ ans₁)
  (if (eq? ans₀ ans₁)
      ans₀
      (for/fold ([ans ans₀]) ([(choice res) (in-hash ans₁)])
        (match (hash-ref ans₀ choice -unmapped)
          [(== -unmapped eq?)
           (hash-set ans choice res)]
          [res* (hash-set ans choice (result-⊔ res res*))]))))

(define (answer-⊔1 ans choice res)
  (match (hash-ref ans choice -unmapped)
    [(== -unmapped eq?) (hash-set ans choice res)]
    [res* (hash-set ans choice (result-⊔ res* res))]))

(define/match (result-⊔ res₀ res₁)
  [((Abs-Result/effect certain?₀ v₀ σ₀ μ₀) (Abs-Result/effect certain?₁ v₁ σ₁ μ₁))
   (Abs-Result/effect (and certain?₀ certain?₁) (term-⊔ v₀ v₁)
                      (store-space-⊔ σ₀ σ₁) (μ⊔ μ₀ μ₁))])

;; XXX: Plug in custom ⊔ here.
(define (store-space-⊔ σ₀ σ₁)
  (if (eq? σ₀ σ₁)
      σ₀
      (for/fold ([σ σ₀]) ([(space store) (in-hash σ₁)])
        (hash-set σ space (hash-join store (hash-ref σ₀ space #hash()))))))

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
       [0 (error 'a/equal? "Live address with count 0: ~a (Counts ~a) (Store ~a)" a₀ μ store-spaces)])]
    [(_ _) #f])

  (define (ffun-equal? f₀ f₁)
    (b∧ (ffun-⊑? f₀ f₁)
        (ffun-⊑? f₁ f₀)))

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
               (b∨ (a/equal? v v₁)
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
      ;; We match on name instead of identity due to Variant refinements
      [((variant (Variant name _) ds₀) (variant (Variant name _) ds₁))
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

      ;; OPT-OP: This has no information on discrete abstractions,
      ;;         thus n²logn instead of sometimes nlogn
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
           (special-equality v₀ v₁ μ) ;;a/equal?
           (match precision
             ['concrete (equal? v₀ v₁)]
             ['discrete-abstraction (b∧ (equal? v₀ v₁) (implies (eq? (card v₀ μ)) 'b.⊤))]
             ['abstract (error 'a/equal? "Cannot have non-discrete abstraction of external values without a custom equality relation ~a" d₀)]))]
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

(define (a/match pattern data ρ store-spaces μ)
  ;; inner returns the certainty of the match and the updated map.
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
         
      [((variant (Variant name _) comps) (variant (Variant name _) data))
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
(trace inner)
  (inner pattern data ρ))
(trace a/match)

;; Evaluation is marked with a "certain?" to determine if the results follow a side-condition or pattern-match
;; that "may" fail. This qualification is to reuse evaluation for the semantics of meta-functions,
;; which use the "first" rule that matches. When a rule "may" match, we have to try the next one to be safe.
;; If a rule exactly matches, we can stop.
;; A failed map lookup is simply stuck; it does not affect the certainty of a match.

;; incoming-certain? is for when e is evaluated following another expression's evaluation.
(define (slow-expression-eval ς e ρ store-spaces μ incoming-choices incoming-certain?)
  (let inner ([e e] [ρ ρ] [store-spaces store-spaces] [μ μ]
              [choices incoming-choices] [certain? incoming-certain?])
    (match e
;;; Always pure expressions
      [(Empty-set _) (hash choices (Abs-Result/effect certain? ∅ store-spaces μ))]

      ;; ASSUMPTION: pat has been pre-transformed so that recursive constructions
      ;; are routed through the store(s)
      [(Term _ pat)
       (hash choices (Abs-Result/effect certain? (pattern-eval pat ρ) store-spaces μ))]

;;; Always reads? expressions
      ;; reads? is true
      [(Store-lookup _ kexpr)
       (for/hash ([(choice kres) (in-hash (inner kexpr ρ store-spaces μ choices certain?))])
         (match-define (Abs-Result/effect kcertain? kv store-spaces* μ*) kres)
         (values choice (Abs-Result/effect kcertain? (store-ref store-spaces kv) store-spaces* μ*)))]

;;; allocs? is true
      ;; XXX: Should unqualified alloc forms be allowed?
      [(SAlloc _ space)
       (define addr (alloc ς ρ))
       (hash choices (Abs-Result/effect certain?
                                    (Address-Structural space addr)
                                    store-spaces
                                    (μ+ μ addr 1)))]
      [(QSAlloc _ space hint)
       (define addr (alloc ς ρ hint))
       (hash choices (Abs-Result/effect certain?
                                    (Address-Structural space addr)
                                    store-spaces
                                    (μ+ μ addr 1)))]
      [(MAlloc _ space)
       (define addr (alloc ς ρ))
       (hash choices (Abs-Result/effect certain?
                                    (Address-Egal space addr)
                                    store-spaces
                                    (μ+ μ addr 1)))]
      [(QMAlloc _ space hint)
       (define addr (alloc ς ρ hint))
       (hash choices (Abs-Result/effect certain?
                                        (Address-Egal space addr)
                                        store-spaces
                                        (μ+ μ addr 1)))]

;;; Depend on others
      ;; We get a set of results from expr. We expect these results to be sets.
      ;; We want to embody any (all) choices from these sets, so we flatten them into
      ;; a set of possible results.
      ;; The semantics of choice is makes match-failure /local/ to choices, and not the
      ;; entire expression. Thus, if we choose from {1,2} and have a condition of even?,
      ;; we will always continue with 2, instead of consider the entire match to fail given 1.
      [(Choose _ label expr)
       (for/fold ([acc answer⊥])
           ([(choice res-set) (in-hash (inner expr ρ store-spaces μ choices certain?))])
         (match-define (Abs-Result/effect rcertain? vset store-spaces* μ*) res-set)
         (cond
          [(set? vset)
           (for/fold ([acc acc]) ([v (in-set vset)])
             (hash-set acc
                       (cons (Choice label v) choice)
                       (Abs-Result/effect rcertain? v store-spaces* μ*)))]
          [else
           (log-info (format "May have chosen from non-set ~a" vset))
           acc]))]

      ;; cards? true
      [(Equal _ l r)
       (for/fold ([acc answer⊥])
           ([(lchoice lres) (in-hash (inner l ρ store-spaces μ choices certain?))])
         (match-define (Abs-Result/effect lcertain? lv store-spaces* μ*) lres)
         (for/fold ([acc acc]) ([(rchoice rres)
                                 (in-hash (inner r ρ store-spaces* μ* lchoice lcertain?))])
           (match-define (Abs-Result/effect rcertain? rv store-spaces** μ**) rres)
           (define equalv (a/equal? lv rv store-spaces** μ**))
           (hash-set acc rchoice
                     (Abs-Result/effect rcertain? (to-data equalv)
                                        store-spaces** μ**))))]

      ;; depending of mf analysis, the interaction can be anything
      [(Meta-function-call _ f arg)
       ;; meta-functions also have non-deterministic choice.
       (for/hash ([(choice res)
                   (in-hash
                    (mf-eval ς
                             store-spaces
                             (hash-ref Ξ f (λ () (error "Unknown meta-function ~a" f)))
                             (pattern-eval arg ρ)
                             μ))])
         (values (append choice choices) res))]
      
      [(Map-lookup _ m kexpr default? dexpr)
       (define ks (inner kexpr ρ store-spaces μ choices certain?))
       (define do-default
         (if default?
             (λ (store-spaces μ outgoing-choices outgoing-certain? [if-bad #f])
                (inner dexpr ρ store-spaces μ outgoing-choices outgoing-certain?))
             (λ (store-spaces μ outgoing-choices outgoing-certain? [if-bad #f])
                (when (procedure? if-bad) (if-bad))
                answer⊥)))
       (match (hash-ref ρ m (unbound-map-error 'map-ref m))
         [(abstract-ffun map)
          (define-values (res found?)
            (for/fold ([res answer⊥]) ([(choice kres) (in-set ks)])
              (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
              (define-values (res* found?)
                (for*/fold ([choice-res -unmapped] [found? #f])
                    ([k (in-data k)]
                     [(k* v) (in-dict map)])
                  (match (a/equal? k k* store-spaces* μ*)
                    [#f (values choice-res found?)]
                    [#t
                     (define res (Abs-Result/effect kcertain? v store-spaces* μ*))
                     (values (if (eq? choice-res -unmapped)
                                 res
                                 (result-⊔ choice-res res))
                             #t)]
                    ['b.⊤
                     (define res (Abs-Result/effect kcertain? v store-spaces* μ*))
                     ;; TODO?: Log entry
                     (values
                      (if (eq? choice-res -unmapped)
                          res
                          (result-⊔ choice-res res))
                      (b∨ found? 'b.⊤))])))
              (match found?
                [#t (hash-set res choice res*)]
                [_
                 (answer-⊔
                  (hash-set res choice res*)
                  (do-default store-spaces* μ* choice certain?))])))
          res]
         [(discrete-ffun map)
          (for/fold ([res answer⊥]) ([(choice kres) (in-hash ks)])
            (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
            (for/fold ([res res]) ([k (in-data k)])
              (match (hash-ref map k -unmapped)
                [(== -unmapped eq?)
                 (answer-⊔
                  res
                  (do-default
                   store-spaces* μ*
                   choice
                   certain?
                   (λ () (log-info (format "map-ref: Key unmapped in map ~a: ~a" m k)))))]
                [v (cond
                    [(∣γ∣>1 k μ)
                     (log-info (format "map-ref: Key may not be present in map ~a: ~a" m k))
                     ;; XXX: emit log entry detailing possible miss?
                     (answer-⊔
                      (hash-set res choice (Abs-Result/effect kcertain? v store-spaces* μ*))
                      (do-default store-spaces* μ* choice certain?))]
                    [else (answer-⊔1 res choice (Abs-Result/effect kcertain? v store-spaces* μ*))])])))]
         [(? dict? map) ;; concrete domain map. Do same as concrete semantics.
          (for/fold ([res answer⊥]) ([(choice kres) (in-hash ks)])
            (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
            (for/fold ([res res]) ([k (in-data k)])
             (match (hash-ref map k -unmapped)
               [(== -unmapped eq?)
                (answer-⊔
                 res
                 (do-default store-spaces* μ* choice kcertain?
                             (λ () (log-info (format "Key unmapped in map ~a: ~a" m k)))))]
               [v (answer-⊔1 res choice (Abs-Result/effect kcertain? v store-spaces* μ*))])))]
         [other (error 'map-lookup "Bad map ~a" other)])]

      ;; XXX: needs special threading
      [(Map-extend _ m kexpr vexpr trust-strong?)
       (define ks (inner kexpr ρ store-spaces μ choices certain?))
       (define setter (if trust-strong? strong-update-with-data weak-update-with-data))
       (match (hash-ref ρ m (unbound-map-error 'map-ext m))
         [(abstract-ffun map)
          (for/fold ([acc answer⊥]) ([(kchoice kres) (in-hash ks)])
            (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
            (for/fold ([acc acc]) ([(vchoice vres)
                                    (in-hash (inner vexpr ρ store-spaces* μ* kchoice kcertain?))])
              (match-define (Abs-Result/effect vcertain? v store-spaces** μ**) vres)
              ;; TODO: This explosion of nastiness is begging for a plug-in widening.
              ;; this may be the form of abstract-ffun having an (optional) extra function
              ;; that takes 〈map,trust-strong?, ks, vs, store-spaces, μ〉 and produces a set of maps
              ;; such that there is a galois connection between that set and the set this fallback produces.
            
              ;; Build two sets for keys that are strongly present or weakly (possibly) present.
              ;; Strongly present keys are in all possible maps. The rest have an exponential blowup.
              ;; OPT: we cut out the intermediate step and build the base map with strongly present keys.
              (define-values (base-map weakly)
                (for*/fold ([base-map map] [weakly ∅]) ([k (in-data k)]
                                                        [k* (in-dict-keys map)])
                  (match (a/equal? k k* store-spaces μ)
                    [#t (values (setter base-map v) weakly)]
                    [#f (values base-map weakly)]
                    ['b.⊤ (values base-map (set-add weakly k*))])))
              ;; Each key adds to possible maps
              (answer-⊔1
               acc
               vchoice
               (Abs-Result/effect vcertain?
                (Abs-Data
                 (for*/fold ([maps (set base-map)])
                     ([k* (in-set weakly)]
                      [map (in-set maps)])
                   (set-add maps (setter (Abs-Result/effect-term map) k* v))))
                store-spaces** μ**))))]
         [(discrete-ffun map)
          ;; ASSUMPTION: abstract finite functions have a ℘ co-domain,
          ;; and values extended are elements of the set, not the type of the co-domain itself.
          ;; This should be weakened for better customizability in the future.
          ;; TODO?: allow non-determinism in vexpr to be absorbed into the abstract co-domain as a widening.
          (for/fold ([acc answer⊥]) ([(kchoice kres) (in-hash ks)])
            (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
            (for*/fold ([acc acc]) ([(vchoice vres)
                                     (in-hash (inner vexpr ρ store-spaces* μ* kchoice kcertain?))]
                                    [k (in-data k)])
              (match-define (Abs-Result/effect vcertain? v store-spaces** μ**) vres)
              (answer-⊔1 acc vchoice (Abs-Result/effect vcertain? (setter map k v) store-spaces** μ**))))]
         [(? dict? map)
          (for/fold ([acc answer⊥]) ([(kchoice kres) (in-hash ks)])
            (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
            (for*/fold ([acc acc]) ([(vchoice vres)
                                     (in-hash (inner vexpr ρ store-spaces* μ* kchoice kcertain?))]
                                    [k (in-data k)])
              (match-define (Abs-Result/effect vcertain? v store-spaces** μ**) vres)
              (match v
                [(Abs-Data S)
                 (Abs-Result/effect vcertain? (Abs-Data (for/set ([v (in-set S)])
                                                          (hash-set map k v)))
                                    store-spaces** μ**)]
                [v
                 (answer-⊔1 acc vchoice
                          (Abs-Result/effect vcertain? (hash-set map k v) store-spaces** μ**))])))]
         [other (error 'map-extend "Bad map? ~a" other)])]

      [(If _ g t e)
       ;; NOTE: Like When, the uncertainty of g only matters if it evaluates to different values.
       ;; If cert
       (define gress (inner g ρ store-spaces μ choices certain?))
       (for/fold ([acc answer⊥]) ([(gchoice gres) (in-set gress)])
         (match-define (Abs-Result/effect gcertain? g store-spaces* μ*) gres)
         (define (then) (inner t ρ store-spaces* μ* gchoice gcertain?))
         (define (else) (inner e ρ store-spaces* μ* gchoice gcertain?))
         (answer-⊔1 acc
                  gchoice
                  (match g
                    [(Boolean _ b) (if b (then) (else))]
                    [(Abs-Data data)
                     (if (set-member? data #f)
                         (if (= (set-count data) 1)
                             (else)
                             (answer-⊔ (then) (else)))
                         (then))]
                    ;; Everything else truish.
                    [_ (then)])))]
      
      ;; Really match-let
      [(Let _ bindings bexpr)
       (expr-eval-bindings
        ς bindings ρ store-spaces μ choices certain?
        (λ (ρ store-spaces μ choices certain?)
           (inner bexpr ρ store-spaces μ choices certain?)))]

      [(In-Dom _ m kexpr)
       (define ks (inner kexpr ρ store-spaces μ choices certain?))
       (match (hash-ref ρ m (unbound-map-error 'map-ext m))
         [(abstract-ffun map)
          (for/hash ([(kchoice kres) (in-hash ks)])
            (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
            (define domv
              (for/bδ ([k (in-data k)])
                      (for/b∨ ([k* (in-dict-keys map)])
                              (a/equal? k k* store-spaces* μ*))))
            (values kchoice (Abs-Result/effect kcertain?
                                               (to-data domv)
                                               store-spaces* μ*)))]
         [(discrete-ffun map)
          (for/hash ([(kchoice kres) (in-hash ks)])
            (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
            (define domv
              (for/bδ ([k (in-data k)])
                      (b∧ (dict-has-key? map k)
                          (implies (∣γ∣>1 k μ) 'b.⊤))))
            (values kchoice (Abs-Result/effect kcertain? (to-data domv) store-spaces* μ*)))]
         [(? dict? map)
          (for/hash ([(kchoice kres) (in-hash ks)])
            (match-define (Abs-Result/effect kcertain? kv store-spaces* μ*) kres)
            (values kchoice (Abs-Result/effect kcertain? (for/bδ ([k (in-data kv)])
                                                            (dict-has-key? map kv))
                                               store-spaces* μ*)))]
         [other (error 'slow-expression-eval "Bad map? ~a" other)])]

      [(Set-Union _ exprs)
       (define logged (mutable-set))
       (let ev-all ([choices choices]
                    [certain? certain?]
                    [exprs exprs]
                    [cur-set ∅]
                    [store-spaces store-spaces]
                    [μ μ])
         (match exprs
           ['() (hash choices (Abs-Result/effect certain? cur-set store-spaces μ))]
           [(cons expr exprs)
            (for/fold ([results answer⊥])
                ([(rchoice res) (in-hash (inner expr ρ store-spaces μ choices certain?))])
              (match-define (Abs-Result/effect vcertain? v store-spaces* μ*) res)
              (for/fold ([results results]) ([v (in-data v)])
                (cond 
                 [(set? v)
                  (answer-⊔
                   results
                   (ev-all rchoice vcertain?
                           exprs (set-union cur-set v) store-spaces* μ*))]
                 [else
                  (unless (set-member? logged v)
                    (log-info (format "Cannot union non-set ~a" v))
                    (set-add! logged v))
                  results])))]
           [_ (error 'set-union "bad exprs ~a" exprs)]))]

      [(Set-Add* _ set-expr exprs)
       (for/fold ([results answer⊥])
           ([(schoice setres) (in-hash (inner set-expr ρ store-spaces μ choices certain?))])
         (match-define (Abs-Result/effect scertain? setv store-spaces* μ*) setres)
         (for/fold ([results results]) ([setv (in-data setv)])
           (cond
            [(set? setv)
             (let ev-all ([choices schoice]
                          [certain? scertain?]
                          [exprs exprs]
                          [cur-set setv]
                          [store-spaces store-spaces*]
                          [μ μ*])
               (match exprs
                 ['() (hash choices (Abs-Result/effect certain? cur-set store-spaces μ))]
                 [(cons expr exprs)
                  (for/fold ([results results])
                      ([(echoice res) (in-hash (inner expr ρ store-spaces μ choices certain?))])
                    (match-define (Abs-Result/effect vcertain? v store-spaces* μ*) res)
                    (for/fold ([results results]) ([v (in-data v)])
                      (answer-⊔ results
                                (ev-all echoice vcertain? exprs
                                        (set-add cur-set v)
                                        store-spaces* μ*))))]
                 [_ (error 'set-add* "Bad exprs ~a" exprs)]))]
            [else
             (log-info (format "Cannot add to non-set ~a" setv))
             results])))]

      ;; OPT-OP: if we know what abstractions a set contains (e.g. all discrete),
      ;; we can use set-member? instead of linear search.
      [(In-Set _ set-expr expr)
       (for/fold ([results answer⊥])
           ([(schoice setres) (in-hash (inner set-expr ρ store-spaces μ choices certain?))])
         (match-define (Abs-Result/effect scertain? setv store-spaces* μ*) setres)
         (for/fold ([results results]) ([setv (in-data setv)])
           (cond
            [(set? setv)
             (for/fold ([results results])
                 ([(vchoice vres) (in-hash (inner expr ρ store-spaces* μ* schoice scertain?))])
               (match-define (Abs-Result/effect vcertain? v store-spaces** μ**) vres)
               (for/fold ([results results]) ([v (in-data v)])
                 (define equalv
                   (for/b∨ ([sv (in-set setv)])
                           (a/equal? sv v store-spaces** μ**)))
                 (answer-⊔1 results vchoice
                          (Abs-Result/effect vcertain? (to-data equalv) store-spaces** μ**))))]
            [else
             (log-info (format "In-Set given non-set ~a" setv))
             results])))]

      [(Boolean _ b) (hash choices (Abs-Result/effect certain? b store-spaces μ))]

      [bad (error 'expr-eval "Bad expression ~a" bad)])))
(trace slow-expression-eval)

;; Binding/Store-extend/When are side-effecting statements (local/global/control).
;; They are available at the top level and in Let expressions.
;; Returns set of results and Boolean (#t iff there is a b.⊤ certain? result).
(define-syntax-rule (mk-slow-eval-bindings name out⊥ combine)
  (define (name ς bindings ρ store-spaces μ incoming-choices incoming-certain? kont)
    (let proc-bindings ([choices incoming-choices] [certain? incoming-certain?]
                        [bindings bindings] [ρ ρ] [store-spaces store-spaces] [μ μ])
      (match bindings
        ['() (kont ρ store-spaces μ choices certain?)]
        [(cons binding bindings)
         (match binding
           [(Binding pat cexpr)
            (for/fold ([acc out⊥])
                ([(cchoice cvres)
                  (in-hash (slow-expression-eval ς cexpr ρ store-spaces μ choices certain?))])
              (match-define (Abs-Result/effect ccertain? cv store-spaces* μ*) cvres)
              (for/fold ([acc acc]) ([cv (in-data cv)])
                (match/values (a/match pat cv ρ store-spaces* μ)
                  [(#f _) acc]
                  [(#t ρ*)
                   (combine acc (proc-bindings cchoice ccertain? bindings ρ* store-spaces* μ*))]
                  [('b.⊤ ρ*)
                   (log-info (format "Possible failed match in let ~a ~a" binding cv))
                   (combine acc (proc-bindings cchoice 'b.⊤ bindings ρ* store-spaces* μ*))]
                  [(b♯ _) (error 'proc-bindings "Bad boolean♯ ~a" b♯)])))]
;;; Always writes?
           ;; TODO: allow approximation that stores evaluation of val-expr directly into store.
           [(Store-extend key-expr val-expr trust-strong?)
            ;; TODO?: make trust-strong? 3 valued. Trust/strong-when-safe/monotonic.
            ;; We use cardinality analysis to determine safety of strong updates.
            (define setter (if trust-strong? store-set store-add))
            (for/fold ([results out⊥])
                ([(kchoice kres)
                  (in-hash (slow-expression-eval ς key-expr ρ store-spaces μ choices certain?))])
              (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
              (for*/fold ([results results])
                  ([(vchoice vres)
                    (in-hash (slow-expression-eval ς val-expr ρ store-spaces* μ* kchoice kcertain?))]
                   [k (in-data k)])
                (match-define (Abs-Result/effect vcertain? v store-spaces** μ**) vres)
                (combine results
                         (proc-bindings vchoice vcertain? bindings ρ (setter store-spaces** k v) μ**))))]
           [(When expr)
            (define condres (slow-expression-eval ς expr ρ store-spaces μ choices certain?))
            (for/fold ([results out⊥]) ([(vchoice vres) (in-hash condres)])
              (match-define (Abs-Result/effect vcertain? v store-spaces* μ*) vres)
              (define (pass certain?)
                (proc-bindings vchoice certain? bindings ρ store-spaces* μ*))
              (match v
                [(Abs-Data S)
                 (if (set-member? S #f)
                     (if (= (set-count S) 1)
                         results
                         (combine results (pass 'b.⊤)))
                     ;; No #f possible here, so we're as certain as before.
                     (combine results (pass certain?)))]
                [#f results]
                [truish (combine results (pass certain?))]))]
           [_ (error 'proc-bindings "Bad binding ~a" binding)])]
        [_ (error 'proc-bindings "Bad bindings ~a" bindings)]))))
(mk-slow-eval-bindings expr-eval-bindings answer⊥ answer-⊔)
(mk-slow-eval-bindings set-eval-bindings ∅ set-union)

(define (slow-rule-eval rule ς)
  (match-define (Rule name lhs rhs binding-side-conditions store-interaction) rule)
  (match-define (Abs-State d store-spaces μ τ̂) ς)
  (match/values (a/match lhs d ρ₀ store-spaces μ)
    [(#f _) ∅]
    [(b♯ ρ)
     (set-eval-bindings ς
      binding-side-conditions ρ store-spaces μ '() #t
      (λ (ρ store-spaces μ choices certain?)
         (unless certain?
           (log-info
            (format "Possible misfire of rule due to imprecise match Rule: ~a Env: ~a Choices: ~a"
                    rule ρ choices)))
         (set (Abs-State (pattern-eval rhs ρ) store-spaces μ (trace-update ς choices τ̂)))))]))

#|
To run mutually-recursively but as a fixed-point computation, we need a 
/dynamically/ scoped memo-table, or a global memo-table (too space-inefficient).
At the top level, a meta-function starts evaluating and sets up the memo table.
If an entry is present:
  Entry is #f: we have hit an infinite loop; thus memoize to ∅.
  Entry is a set: the meta-function has fully evaluated and these are all its results.
If not present, set entry to #f and evaluate to all results. Then set entry to the set.

TODO: mf's given a "trust recursion" tag to not do this space-intensive memoization.
|#
;; Hasheq[Meta-function,Hash[(List State Store-Spaces Abs-Count DPattern),Set[Abs-Result/effect]]
(define mf-memo (make-parameter #f))
(define (slow-meta-function-eval ς store-spaces mf argd μ)
  (match-define (Meta-function name rules _ _ trusted-implementation/abs) mf)
  (define (do-mf-eval table)
    (define mf-table (hash-ref! table mf make-hash))
    (define key (list ς store-spaces μ argd))
    (match (hash-ref mf-table key -unmapped)
      [#f ;; infinite loop. Reached same key.
       (hash-set! mf-table key answer⊥)
       answer⊥]
      [(== -unmapped eq?)
       (hash-set! mf-table key #f)
       (define results
         (let try-rules ([rules rules] [results answer⊥])
           (match rules
             ['() results]
             [(cons (and rule (Rule name lhs rhs binding-side-conditions store-interaction)) rules)
              (match/values (a/match lhs argd ρ₀ store-spaces μ)
                [(#f _) (try-rules rules results)]
                [(b♯ ρ)
                 (expr-eval-bindings
                  ς
                  binding-side-conditions ρ store-spaces μ '() b♯
                  (λ (ρ store-spaces μ choices certain?)
                     (define results*
                       (answer-⊔1 results choices
                                ;; Quality is #t since meta-functions' evaluation does not affect
                                ;; the matching of a rule.
                                (Abs-Result/effect #t (pattern-eval rhs ρ) store-spaces μ)))
                     (cond 
                      ;; True match; we can stop searching through rules.
                      [certain? results*]
                      [else
                       (log-info
                        (format "Possible misfire of meta-function rule due to imprecise match ~a ~a ~a"
                                rule rhs ρ))
                       (try-rules rules results*)])))])])))
       (hash-set! mf-table key results)
       results]
      [results results]))
  (if trusted-implementation/abs
      (trusted-implementation/abs ς store-spaces μ argd)
      (match (mf-memo)
        [#f (define table (make-hasheq))
            (parameterize ([mf-memo table])
              (do-mf-eval table))]
        [table (do-mf-eval table)])))
(define mf-eval slow-meta-function-eval)
(define rule-eval slow-rule-eval)
(define expression-eval slow-expression-eval))

#|
;;for later
 (define-syntax (mk-mk-expr-eval-fn stx)
  (syntax-parse stx
   ([_ base-name:id]
    (define sublists
      (match-lambda**
       [(0 _)           '(())]
       [(_ '())         '()]
       [(m (cons x xs)) (let loop ([others (sublists (sub1 m) xs)])
                          (match others
                            ['() (sublists m xs)]
                            [(cons y others) (cons (cons x y) (loop others))]))]))

    (with-syntax ([((name qualities ...) ...)
                   (for*/list ([i (add1 5)]
                               [cs (in-list (sublists i '(#:reads
                                                          #:writes
                                                          #:cardinality
                                                          #:allocates
                                                          #:many)))])
                     (cons (format-id
                            #'base-name
                            "~a~a~a"
                            #'base-name
                            (if (null? cs) "" "/")
                            (string-join (map keyword->string cs) "/"))
                           cs))])
      #`(begin (make-expr-eval-fn names qualities ...) ...)))))
 (mk-mk-expr-eval-fn expression-eval)

 (define-syntax (make-expr-eval-fn stx)
  (syntax-parse stx
    [(_ name:id (~or (~optional (~and #:reads reads-σ))
                     (~optional (~and #:writes writes-σ))
                     (~optional (~and #:cardinality reads-μ))
                     (~optional (~and #:allocates writes-μ))
                     (~optional (~and #:many many))) ...)
     (define memo-wrap
       (if (or (attribute reads-σ) (attribute reads-μ))
           identity
           (λ (stx) #`(let ([memo-table (make-hash)]) #,stx))))
     (define-syntax-rule (single e) ;; TODO: just do the slow thing for now.
       )
     #`(define name
        #,(memo-wrap
           #`(λ (e ρ store-spaces μ) (error 'todo))))]))
|#
