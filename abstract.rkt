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

;; Evaluation is marked with a "quality" to determine if the results follow a side-condition or pattern-match
;; that "may" fail. This qualification is to reuse evaluation for the semantics of meta-functions,
;; which use the "first" rule that matches. When a rule "may" match, we have to try the next one to be safe.
;; If a rule exactly matches, we can stop.
;; A failed map lookup is simply stuck; it does not affect the quality of a match.

;; incoming-quality is for when e is evaluated following another expression's evaluation.
;; The quality will be at least the quality of the previous expression's.
(define (slow-expression-eval ς e ρ store-spaces μ incoming-quality)
  (let inner ([e e] [ρ ρ] [store-spaces store-spaces] [μ μ] [incoming-quality incoming-quality])
    (match e
;;; Always pure expressions
      [(Empty-set _) (set (Abs-Result/effect incoming-quality ∅ store-spaces μ))]

      ;; We get a set of results from expr. We expect these results to be sets.
      ;; We want to embody any (all) choices from these sets, so we flatten them into
      ;; a set of possible results.
      [(Choose _ expr)
       (for/fold ([acc ∅]) ([res-set (in-set (inner expr ρ store-spaces μ incoming-quality))])
         (match-define (Abs-Result/effect quality vset store-spaces* μ*) res-set)
         (cond
          [(set? vset)
           (for/fold ([acc acc]) ([v (in-set vset)])
             (set-add acc (Abs-Result/effect quality v store-spaces* μ*)))]
          [else
           (log-info (format "May have chosen from non-set ~a" vset))
           acc]))]

      ;; ASSUMPTION: pat has been pre-transformed so that recursive constructions
      ;; are routed through the store(s)
      [(Term _ pat) (set (Abs-Result/effect incoming-quality (pattern-eval pat ρ) store-spaces μ))]

;;; Always reads? expressions
      ;; reads? is true
      [(Store-lookup _ kexpr)
       (for/set ([kres (in-set (inner kexpr ρ store-spaces μ incoming-quality))])
         (match-define (Abs-Result/effect quality kv store-spaces* μ*) kres)
         (Abs-Result/effect quality (store-ref store-spaces kv) store-spaces* μ*))]

;;; allocs? is true
      ;; XXX: Should unqualified alloc forms be allowed?
      [(SAlloc _ space)
       (define addr (alloc ς ρ))
       (set (Abs-Result/effect incoming-quality
                               (Address-Structural space addr)
                               store-spaces
                               (μ+ μ addr 1)))]
      [(QSAlloc _ space hint)
       (define addr (alloc ς ρ hint))
       (set (Abs-Result/effect incoming-quality
                               (Address-Structural space addr)
                               store-spaces
                               (μ+ μ addr 1)))]
      [(MAlloc _ space)
       (define addr (alloc ς ρ))
       (set (Abs-Result/effect incoming-quality
                               (Address-Egal space addr)
                               store-spaces
                               (μ+ μ addr 1)))]
      [(QMAlloc _ space hint)
       (define addr (alloc ς ρ hint))
       (set (Abs-Result/effect incoming-quality
                               (Address-Egal space addr)
                               store-spaces
                               (μ+ μ addr 1)))]

;;; Depend on others
      ;; cards? true
      [(Equal _ l r)
       (for/fold ([acc ∅]) ([lres (in-set (inner l ρ store-spaces μ incoming-quality))])
         (match-define (Abs-Result/effect quality lv store-spaces* μ*) lres)
         (for/fold ([acc acc]) ([rres (in-set (inner r ρ store-spaces* μ* quality))])
           (match-define (Abs-Result/effect rquality rv store-spaces** μ**) rres)
           (for/fold ([acc acc]) ([b (in-set (⦃b⦄ (a/equal? lv rv store-spaces** μ**)))])
             (Abs-Result/effect rquality b store-spaces** μ**))))]

      ;; depending of mf analysis, the interaction can be anything
      [(Meta-function-call _ f arg)
       ;; meta-functions also have non-deterministic choice.
       (mf-eval ς
                store-spaces
                (hash-ref Ξ f (λ () (error "Unknown meta-function ~a" f)))
                (pattern-eval arg ρ)
                μ)]
      
      [(Map-lookup _ m kexpr default? dexpr)
       (define ks (inner kexpr ρ store-spaces μ incoming-quality))
       (define do-default
         (if default?
             (λ (store-spaces μ outgoing-quality [if-bad #f])
                (inner dexpr ρ store-spaces μ outgoing-quality))
             (λ (store-spaces μ outgoing-quality [if-bad #f])
                (when (procedure? if-bad) (if-bad))
                ∅)))
       (match (hash-ref ρ m (unbound-map-error 'map-ref m))
         [(abstract-ffun map)
          (define-values (res found?)
            (for/fold ([res ∅]) ([kres (in-set ks)])
              (match-define (Abs-Result/effect quality k store-spaces* μ*) kres)
              (define-values (res* found?)
                (for/fold ([res res] [found? #f])
                    ([(k* v) (in-dict map)])
                  (match (a/equal? k k* store-spaces* μ*)
                    [#f (values res found?)]
                    [#t (values (set-add res (Abs-Result/effect quality v store-spaces* μ*))
                                #t)]
                    ['b.⊤
                     (values
                      ;; XXX: emit log entry detailing possible miss?
                      (set-add res (Abs-Result/effect quality v store-spaces* μ*))
                      (b∨ found? 'b.⊤))])))
              (match found?
                [#t res*]
                [_ (set-union res* (do-default store-spaces* μ* quality))])))
          res]
         [(discrete-ffun map)
          (for/fold ([res ∅]) ([kres (in-set ks)])
            (match-define (Abs-Result/effect quality k store-spaces* μ*) kres)
            (match (hash-ref map k -unmapped)
              [(== -unmapped eq?)
               (do-default
                store-spaces* μ*
                quality
                (λ () (log-info (format "map-ref: Key unmapped in map ~a: ~a" m k))))]
              [v (cond
                  [(∣γ∣>1 k μ)
                   (log-info (format "map-ref: Key may not be present in map ~a: ~a" m k))
                   ;; XXX: emit log entry detailing possible miss?
                   (set-union (set-add res (Abs-Result/effect quality v store-spaces* μ*))
                              (do-default store-spaces* μ* quality))]
                  [else (set-add res (Abs-Result/effect quality v store-spaces* μ*))])]))]
         [(? dict? map) ;; concrete domain map. Do same as concrete semantics.
          (for/fold ([res ∅]) ([kres (in-set ks)])
            (match-define (Abs-Result/effect quality k store-spaces* μ*) kres)
            (match (hash-ref map k -unmapped)
              [(== -unmapped eq?)
               (set-union res
                          (do-default store-spaces* μ* quality
                                      (λ () (log-info (format "Key unmapped in map ~a: ~a" m k)))))]
              [v (set-add res (Abs-Result/effect quality v store-spaces* μ*))]))]
         [other (error 'map-lookup "Bad map ~a" other)])]

      ;; XXX: needs special threading
      [(Map-extend _ m kexpr vexpr trust-strong?)
       (define ks (inner kexpr ρ store-spaces μ incoming-quality))
       (define setter (if trust-strong? (λ (h k v) (hash-set h k (set v))) hash-add))
       (match (hash-ref ρ m (unbound-map-error 'map-ext m))
         [(abstract-ffun map)
          (for/fold ([acc ∅]) ([kres (in-set ks)])
            (match-define (Abs-Result/effect kquality k store-spaces* μ*) kres)
            (for/fold ([acc acc]) ([vres (in-set (inner vexpr ρ store-spaces* μ* kquality))])
              (match-define (Abs-Result/effect vquality v store-spaces** μ**) vres)
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
                         (for*/fold ([maps (set (Abs-Result/effect vquality base-map store-spaces** μ**))])
                             ([k* (in-set weakly)]
                              [map (in-set maps)])
                           (set-add maps
                                    (Abs-Result/effect vquality
                                                       (setter (Abs-Result/effect-term map) k* v)
                                                       store-spaces** μ**))))))]
         [(discrete-ffun map)
          ;; ASSUMPTION: abstract finite functions have a ℘ co-domain,
          ;; and values extended are elements of the set, not the type of the co-domain itself.
          ;; This should be weakened for better customizability in the future.
          ;; TODO?: allow non-determinism in vexpr to be absorbed into the abstract co-domain as a widening.
          (for/fold ([acc ∅]) ([kres (in-set ks)])
            (match-define (Abs-Result/effect kquality k store-spaces* μ*) kres)
            (for/fold ([acc acc]) ([vres (in-set (inner vexpr ρ store-spaces* μ* kquality))])
              (match-define (Abs-Result/effect vquality v store-spaces** μ**) vres)
              (set-add acc (Abs-Result/effect vquality (setter map k v) store-spaces** μ**))))]
         [(? dict? map)
          (for/fold ([acc ∅]) ([kres (in-set ks)])
            (match-define (Abs-Result/effect kquality k store-spaces* μ*) kres)
            (for/fold ([acc acc]) ([vres (in-set (inner vexpr ρ store-spaces* μ* kquality))])
              (match-define (Abs-Result/effect vquality v store-spaces** μ**) vres)
              (set-add acc (Abs-Result/effect vquality (hash-set map k v) store-spaces** μ**))))]
         [other (error 'map-extend "Bad map? ~a" other)])]

      ;; XXX: needs special threading
      [(If _ g t e)
       (for/fold ([acc ∅]) ([gres (in-set (inner g ρ store-spaces μ incoming-quality))])
         (match-define (Abs-Result/effect gquality g store-spaces* μ*) gres)
         (set-union acc
                    (if g
                        (inner t ρ store-spaces* μ* gquality)
                        (inner e ρ store-spaces* μ* gquality))))]

      ;; Really match-let
      [(Let _ bindings bexpr)
       (slow-eval-bindings
        ς bindings ρ store-spaces μ incoming-quality
        (λ (ρ store-spaces μ quality)
           (inner bexpr ρ store-spaces μ quality)))]

      [(In-Dom _ m kexpr)
       (define ks (inner kexpr ρ store-spaces μ incoming-quality))
       (match (hash-ref ρ m (unbound-map-error 'map-ext m))
         [(abstract-ffun map)
          (for/fold ([acc ∅]) ([kres (in-set ks)])
            (match-define (Abs-Result/effect kquality k store-spaces* μ*) kres)
            (for/fold ([acc acc])
                ([b (in-set (⦃b⦄
                             (for*/b∨ ([k* (in-dict-keys map)])
                                      (a/equal? k k* store-spaces* μ*))))])
              (set-add acc (Abs-Result/effect kquality b store-spaces* μ*))))]
         [(discrete-ffun map)
          (for/fold ([acc ∅]) ([kres (in-set ks)])
            (match-define (Abs-Result/effect kquality k store-spaces* μ*) kres)
            (for/fold ([acc acc])
                ([b (in-set (⦃b⦄
                             (b∧ (dict-has-key? map k)
                                 (implies (∣γ∣>1 k μ) 'b.⊤))))])
              (set-add acc (Abs-Result/effect kquality b store-spaces* μ*))))]
         [(? dict? map)
          (for/set ([kres (in-set ks)])
            (match-define (Abs-Result/effect kquality kv store-spaces* μ*) kres)
            (Abs-Result/effect kquality (dict-has-key? map kv) store-spaces* μ*))]
         [other (error 'slow-expression-eval "Bad map? ~a" other)])]

      [(Set-Union _ exprs)
       (define logged (mutable-set))
       (let ev-all ([quality incoming-quality]
                    [exprs exprs]
                    [cur-set ∅]
                    [store-spaces store-spaces]
                    [μ μ])
         (match exprs
           ['() (set (Abs-Result/effect quality cur-set store-spaces μ))]
           [(cons expr exprs)
            (for/fold ([results ∅])
                ([res (in-set (inner expr ρ store-spaces μ quality))])
              (match-define (Abs-Result/effect vquality v store-spaces* μ*) res)
              (cond 
               [(set? v)
                (set-union results
                           (ev-all vquality
                                   exprs (set-union cur-set v) store-spaces* μ*))]
               [else
                (unless (set-member? logged v)
                  (log-info (format "Cannot union non-set ~a" v))
                  (set-add! logged v))
                results]))]
           [_ (error 'set-union "bad exprs ~a" exprs)]))]

      [(Set-Add* _ set-expr exprs)
       (for/fold ([results ∅])
           ([setres (in-set (inner set-expr ρ store-spaces μ incoming-quality))])
         (match-define (Abs-Result/effect squality setv store-spaces* μ*) setres)
         (cond
          [(set? setv)
           (let ev-all ([quality squality]
                        [exprs exprs]
                        [cur-set setv]
                        [store-spaces store-spaces*]
                        [μ μ*])
             (match exprs
               ['() (set (Abs-Result/effect quality cur-set store-spaces μ))]
               [(cons expr exprs)
                (for/fold ([results results])
                    ([res (in-set (inner expr ρ store-spaces μ quality))])
                  (match-define (Abs-Result/effect vquality v store-spaces* μ*) res)
                  (set-union results
                             (ev-all vquality exprs (set-add cur-set v) store-spaces* μ*)))]
               [_ (error 'set-add* "Bad exprs ~a" exprs)]))]
          [else
           (log-info (format "Cannot add to non-set ~a" setv))
           results]))]

      ;; OPT-OP: if we know what abstractions a set contains (e.g. all discrete),
      ;; we can use set-member? instead of linear search.
      [(In-Set _ set-expr expr)
       (for/fold ([results ∅])
           ([setres (in-set (inner set-expr ρ store-spaces μ incoming-quality))])
         (match-define (Abs-Result/effect squality setv store-spaces* μ*) setres)
         (cond
          [(set? setv)
           (for/fold ([results results])
               ([vres (in-set (inner expr ρ store-spaces* μ* squality))])
             (match-define (Abs-Result/effect vquality v store-spaces** μ**) vres)
             (for/fold ([results results])
                 ([b (in-set (⦃b⦄ (for/b∨ ([sv (in-set setv)])
                                          (a/equal? sv v store-spaces** μ**))))])
               (set-add results
                        (Abs-Result/effect vquality b store-spaces** μ**))))]
          [else
           (log-info (format "In-Set given non-set ~a" setv))
           results]))]

      [(? boolean? b) (set (Abs-Result/effect incoming-quality b store-spaces μ))]

      [bad (error 'expr-eval "Bad expression ~a" bad)])))
(trace slow-expression-eval)

;; Binding/Store-extend/When are side-effecting statements (local/global/control).
;; They are available at the top level and in Let expressions.
;; Returns set of results and Boolean (#t iff there is a b.⊤ quality result).
(define (slow-eval-bindings ς bindings ρ store-spaces μ incoming-quality kont)
  (let proc-bindings ([quality incoming-quality] [bindings bindings] [ρ ρ] [store-spaces store-spaces] [μ μ])
    (match bindings
      ['() (kont ρ store-spaces μ quality)]
      [(cons binding bindings)
       (match binding
         [(Binding pat cexpr)
          (for/fold ([acc ∅])
              ([cvres (in-set (slow-expression-eval ς cexpr ρ store-spaces μ quality))])
            (match-define (Abs-Result/effect cquality cv store-spaces* μ*) cvres)
            (match/values (a/match pat cv ρ store-spaces* μ)
              [(#f _) acc]
              [(#t ρ*)
               (set-union acc (proc-bindings cquality bindings ρ* store-spaces* μ*))]
              [('b.⊤ ρ*)
               (log-info (format "Possible failed match in let ~a ~a" binding cv))
               (set-union acc (proc-bindings 'b.⊤ bindings ρ* store-spaces* μ*))]
              [(b♯ _) (error 'proc-bindings "Bad boolean♯ ~a" b♯)]))]
;;; Always writes?
         ;; TODO: allow approximation that stores evaluation of val-expr directly into store.
         [(Store-extend key-expr val-expr trust-strong?)
          ;; TODO?: make trust-strong? 3 valued. Trust/strong-when-safe/monotonic.
          ;; We use cardinality analysis to determine safety of strong updates.
          (define setter (if trust-strong?
                             (λ (store-spaces k v) (store-set store-spaces k (set v)))
                             store-add))
          (for/fold ([results ∅])
              ([kres (in-set (slow-expression-eval ς key-expr ρ store-spaces μ quality))])
            (match-define (Abs-Result/effect kquality k store-spaces* μ*) kres)
            (for/fold ([results results])
                ([vres (in-set (slow-expression-eval ς val-expr ρ store-spaces* μ* kquality))])
              (match-define (Abs-Result/effect vquality v store-spaces** μ**) vres)
              (set-union results
                         (proc-bindings vquality bindings ρ (setter store-spaces** k v) μ**))))]
         [(When expr)
          (for/fold ([results ∅])
              ([vres (in-set (slow-expression-eval ς expr ρ store-spaces μ quality))])
            (match-define (Abs-Result/effect vquality v store-spaces* μ*) vres)
            (cond
             [v
              (set-union results
                         ;; XXX: The one place that the quality can change
                         (proc-bindings (b∧ vquality v) bindings ρ store-spaces* μ*))]
             [else results]))]
         [_ (error 'proc-bindings "Bad binding ~a" binding)])]
      [_ (error 'proc-bindings "Bad bindings ~a" bindings)])))

(define (slow-rule-eval rule ς)
  (match-define (Rule name lhs rhs binding-side-conditions) rule)
  (match-define (Abs-State d store-spaces μ) ς)
  (match/values (a/match lhs d ρ₀ store-spaces μ)
    [(#f _) ∅]
    [(b♯ ρ)
     (slow-eval-bindings ς
      binding-side-conditions ρ store-spaces μ #t
      (λ (ρ store-spaces μ quality)
         (when (eq? quality 'b.⊤)
           (log-info
            (format "Possible misfire of rule due to imprecise match ~a ~a ~a"
                    rule rhs ρ)))
         (set (Abs-State (pattern-eval rhs ρ) store-spaces μ))))]))

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
  (match-define (Meta-function name rules _ trusted-implementation/abs) mf)
  (define (do-mf-eval table)
    (define mf-table (hash-ref! table mf make-hash))
    (define key (list ς store-spaces μ argd))
    (match (hash-ref mf-table key -unmapped)
      [#f ;; infinite loop. Reached same key.
       (hash-set! mf-table key ∅)
       ∅]
      [(== -unmapped eq?)
       (hash-set! mf-table key #f)
       (define results
         (let try-rules ([rules rules] [results ∅])
           (match rules
             ['() results]
             [(cons (and rule (Rule name lhs rhs binding-side-conditions)) rules)
              (match/values (a/match lhs argd ρ₀ store-spaces μ)
                [(#f _) (try-rules rules results)]
                [(b♯ ρ)
                 (slow-eval-bindings
                  ς
                  binding-side-conditions ρ store-spaces μ b♯
                  (λ (ρ store-spaces μ quality)
                     (define results*
                       (set-add results
                                ;; Quality is #t since meta-functions' evaluation does not affect
                                ;; the matching of a rule.
                                (Abs-Result/effect #t (pattern-eval rhs ρ) store-spaces μ)))
                     (cond 
                      [(eq? quality 'b.⊤)
                       (log-info
                        (format "Possible misfire of meta-function rule due to imprecise match ~a ~a ~a"
                                rule rhs ρ))
                       (try-rules rules results*)]
                      ;; True match; we can stop searching through rules.
                      [else results*])))])])))
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
