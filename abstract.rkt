#lang racket/base
(require "spaces.rkt" "shared.rkt" "lattices.rkt" "term-lattices.rkt"
         "signatures.rkt" "map-operations.rkt" "set-operations.rkt"
         "matching-equality.rkt"
         (only-in racket/bool implies)
         (only-in racket/function identity const)
         (for-syntax syntax/parse racket/base racket/match racket/syntax
                     (only-in racket/string string-join))
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
  (for/or ([space (in-dict-values (Language-spaces L))]
           #:when (and (External-Space? space)
                       ((External-Space-pred space) v)))
    (external space v)))

(define-unit abstract-reduction@
  (import language-parms^ matching-equality^ abstract-set-ops^ abstract-map-ops^)
  (export language-impl^)

  ;; for left-associated non-monotonic operations: set-remove* set-intersect set-subtract
  (define (reduce ς op e0 es ρ store-spaces μ choices certain?)
    (define core
      (in-hash (slow-expression-eval ς e0 ρ store-spaces μ choices certain?)))
    (cond
     [(empty? es) core]
     [else
      (for/fold ([acc answer⊥]) ([(schoice sres) (in-hash core)])
        (match-define (Abs-Result/effect scertain? setv store-spaces* μ*) sres)
        (for/fold ([acc acc]) ([setv (in-data setv)])
          (answer-⊔
           acc
           (let rep-bin ([exprs es]
                         [S setv]
                         [store-spaces store-spaces*]
                         [μ μ*]
                         [choices schoice]
                         [certain? scertain?])
             (match exprs
               ['()
                (hash choices (Abs-Result/effect certain? S store-spaces μ))]
               [(cons expr exprs)
                (for/fold ([acc acc])
                    ([(s*choice s*res)
                      (in-hash (slow-expression-eval ς expr ρ store-spaces μ choices certain?))])
                  (match-define (Abs-Result/effect s*certain? setv* store-spaces** μ**) s*res)
                  (for*/fold ([acc acc]) ([S (in-data S)]
                                          [setv* (in-data setv*)])
                    (answer-⊔
                     acc
                     (rep-bin
                      exprs
                      (op S setv* store-spaces** μ**)
                      store-spaces** μ**
                      s*choice s*certain?))))])))))]))

  ;; Evaluation is marked with a "certain?" to determine if the results follow a side-condition or pattern-match
  ;; that "may" fail. This qualification is to reuse evaluation for the semantics of meta-functions,
  ;; which use the "first" rule that matches. When a rule "may" match, we have to try the next one to be safe.
  ;; If a rule exactly matches, we can stop.
  ;; A failed map lookup is simply stuck; it does not affect the certainty of a match.

  ;; incoming-certain? is for when e is evaluated following another expression's evaluation.
  (define (slow-expression-eval ς e ρ store-spaces μ incoming-choices incoming-certain?)
    (define (eeval e ρ store-spaces μ choices certain?)
      (match e
;;; Always pure expressions
        [(Empty-set _ vcomp)
         (hash choices (Abs-Result/effect certain? (fset vcomp ∅) store-spaces μ))]

        [(Empty-map _ mcomp)
         (hash choices (Abs-Result/effect certain? (ffun mcomp ρ₀) store-spaces μ))]

        ;; ASSUMPTION: pat has been pre-transformed so that recursive constructions
        ;; are routed through the store(s)
        [(Term _ _ pat)
         (hash choices (Abs-Result/effect certain? (pattern-eval pat ρ) store-spaces μ))]
        [(? boolean? b)
         (hash choices (Abs-Result/effect certain? b store-spaces μ))]

;;; Always reads? expressions
        ;; reads? is true
        ;; FIXME: I'm unclear whether we should treat the codomain of a store as an abstract value that happens to be a set,
        ;; or simply as a set. This is a tough matter when we consider adding lazy-nondeterminism.
        [(Store-lookup _ _ kexpr)
         (for/hash ([(choice kres) (in-hash (eeval kexpr ρ store-spaces μ choices certain?))])
           (match-define (Abs-Result/effect kcertain? kv store-spaces* μ*) kres)
           (values choice (Abs-Result/effect kcertain? (store-ref store-spaces kv) store-spaces* μ*)))]

;;; allocs? is true
        [(Alloc _ _ space match-behavior equal-behavior hint)
         (define addr (alloc ς ρ hint))
         (hash choices (Abs-Result/effect
                        certain?
                        (Address space addr match-behavior equal-behavior)
                        store-spaces
                        (μ+ μ addr 1)))]

;;; Map operations

        [(Map-lookup _ _ m kexpr default? dexpr)
         (define ks (eeval kexpr ρ store-spaces μ choices certain?))
         (define do-default
           (if default?
               (λ (store-spaces μ outgoing-choices outgoing-certain? [if-bad #f])
                  (eeval dexpr ρ store-spaces μ outgoing-choices outgoing-certain?))
               (λ (store-spaces μ outgoing-choices outgoing-certain? [if-bad #f])
                  (when (procedure? if-bad) (if-bad))
                  answer⊥)))
         (match (hash-ref ρ m (unbound-map-error 'map-ref m))
           [(ffun (Map _ _ kcomp _) map)
            (define pc (Component-pc kcomp))
            (case pc
              [(abstract)
               (define-values (res found?)
                 (for/fold ([res answer⊥]) ([(choice kres) (in-hash ks)])
                   (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
                   (define-values (res* found?)
                     (for*/fold ([choice-res -unmapped] [found? #f])
                         ([k (in-data k)]
                          [(k* v) (in-hash map)])
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
              [(discrete)
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
              [(concrete)
               (for/fold ([res answer⊥]) ([(choice kres) (in-hash ks)])
                 (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
                 (for/fold ([res res]) ([k (in-data k)])
                   (match (hash-ref map k -unmapped)
                     [(== -unmapped eq?)
                      (answer-⊔
                       res
                       (do-default store-spaces* μ* choice kcertain?
                                   (λ () (log-info (format "Key unmapped in map ~a: ~a" m k)))))]
                     [v (answer-⊔1 res choice (Abs-Result/effect kcertain? v store-spaces* μ*))])))])]
           [other (error 'map-lookup "Bad map ~a" other)])]

        ;; FIXME?: Must trust that the key is in the same concrete/discrete/abstract
        ;; space classification as the map's other keys.
        [(Map-extend _ _ m kexpr vexpr trust-strong?)
         (define ks (eeval kexpr ρ store-spaces μ choices certain?))
         (define setter (if trust-strong? ffun-strong-update ffun-weak-update))
         (define mval (hash-ref ρ m (unbound-map-error 'map-ext m)))
         (define inner-extender
           (match mval
             [(ffun (Map _ _ kcomp _) _)
              (define pc (Component-pc kcomp))
              (case pc
                [(abstract) (abstract-map-extend mval setter)]
                [(discrete)
                 ;; ASSUMPTION: abstract finite functions have a ℘ co-domain,
                 ;; and values extended are elements of the set, not the type of the co-domain itself.
                 ;; This should be weakened for better customizability in the future.
                 ;; TODO?: allow non-determinism in vexpr to be absorbed into the abstract co-domain as a widening.
                 (λ (store-spaces μ certain? k v)
                    (Abs-Result/effect certain? (setter mval k v) store-spaces μ))]
                [(concrete)
                 (λ (store-spaces μ certain? k v)
                    (Abs-Result/effect certain?
                                       (ffun-strong-update mval k v)
                                       store-spaces μ))])]
             [other (error 'map-extend "Bad map? ~a" other)]))
         (for/fold ([acc answer⊥]) ([(kchoice kres) (in-hash ks)])
           (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
           (for*/fold ([acc acc]) ([(vchoice vres)
                                    (in-hash (eeval vexpr ρ store-spaces* μ* kchoice kcertain?))]
                                   [k (in-data k)])
             (match-define (Abs-Result/effect vcertain? v store-spaces** μ**) vres)
             (answer-⊔1 acc vchoice (inner-extender store-spaces** μ** vcertain? k v))))]

        [(Map-remove _ _ m kexpr)
         (define map (hash-ref ρ m (unbound-map-error 'map-remove m)))
         (for/fold ([acc answer⊥]) ([(kchoice kres)
                                     (in-hash (eeval kexpr ρ store-spaces μ choices certain?))])
           (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
           (for/fold ([acc acc]) ([k (in-data k)])
             (answer-⊔1 acc kchoice
                      (Abs-Result/effect kcertain?
                                         (a/map-remove map k store-spaces* μ*)
                                         store-spaces*
                                         μ*))))]

        [(Map-empty? _ _ m)
         (match (hash-ref ρ m (unbound-map-error 'map-empty? m))
           [(ffun (Map _ _ kcomp _) map)
            (define pc (Component-pc kcomp))
            (case pc
              [(concrete discrete)
               ;; concrete domain is obvious
               ;; UNCHECKED ASSUMPTION:
               ;; discrete domain: if there is any abstract value in the set,
               ;;  there must be at least one concrete value that it corresponds to.
               (hash choices
                     (Abs-Result/effect certain?
                                        (to-data (eq? 0 (hash-count map)))
                                        store-spaces μ))]
              ;; Abstract domains may have conflicting constraints that lead
              ;; to no concrete counterparts. We are especially cautious here.
              [(abstract)
               (hash choices
                     (Abs-Result/effect
                      certain?
                      (to-data
                       (b∨ (eq? 0 (hash-count map))
                           ;; If every element is > 1, we output maybe,
                           ;; since they may also be size 0
                           ;; If any element is = 1, we output #f
                           ;; ASSERTION: size exact 0 should never be live.
                           (match
                             (for/b⊔ ([sv (in-hash-keys map)])
                                     (∣γ∣>1 sv μ))
                             [#t 'b.⊤]
                             [_ #f]))))
                     store-spaces μ)])]
           [other
            (log-info (format "Map-empty? given non-map ~a" other))
            answer⊥])]

        [(In-Dom? _ _ m kexpr)
         (define ks (eeval kexpr ρ store-spaces μ choices certain?))
         (match (hash-ref ρ m (unbound-map-error 'map-ext m))
           [(ffun (Map _ _ kcomp _) map)
            (define pc (Component-pc kcomp))
            (case pc
              [(abstract)
               (for/hash ([(kchoice kres) (in-hash ks)])
                 (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
                 (define domv
                   (for/b⊔ ([k (in-data k)])
                           (for/b∨ ([k* (in-dict-keys map)])
                                   (a/equal? k k* store-spaces* μ*))))
                 (values kchoice (Abs-Result/effect kcertain?
                                                    (to-data domv)
                                                    store-spaces* μ*)))]
              [(discrete)
               (for/hash ([(kchoice kres) (in-hash ks)])
                 (match-define (Abs-Result/effect kcertain? k store-spaces* μ*) kres)
                 (define domv
                   (for/b⊔ ([k (in-data k)])
                           (b∧ (dict-has-key? map k)
                               (implies (∣γ∣>1 k μ) 'b.⊤))))
                 (values kchoice (Abs-Result/effect kcertain? (to-data domv) store-spaces* μ*)))]
              [(concrete)
               (for/hash ([(kchoice kres) (in-hash ks)])
                 (match-define (Abs-Result/effect kcertain? kv store-spaces* μ*) kres)
                 (values kchoice (Abs-Result/effect kcertain? (for/b⊔ ([k (in-data kv)])
                                                                      (dict-has-key? map kv))
                                                    store-spaces* μ*)))])]
           [other (error 'slow-expression-eval "Bad map? ~a" other)])]

;;; General expressions


        ;; We get a set of results from expr. We expect these results to be sets.
        ;; We want to embody any (all) choices from these sets, so we flatten them into
        ;; a set of possible results.
        ;; The semantics of choice is makes match-failure /local/ to choices, and not the
        ;; entire expression. Thus, if we choose from {1,2} and have a condition of even?,
        ;; we will always continue with 2, instead of consider the entire match to fail given 1.
        [(Choose _ _ label expr)
         (for/fold ([acc answer⊥])
             ([(choice res-set) (in-hash (eeval expr ρ store-spaces μ choices certain?))])
           (match-define (Abs-Result/effect rcertain? vset store-spaces* μ*) res-set)
           (for/fold ([acc acc]) ([v (in-data vset)])
             (hash-set acc
                       (cons (Choice label v) choice)
                       (Abs-Result/effect rcertain? v store-spaces* μ*))))]

        ;; cards? true
        [(Equal _ _ l r)
         (for/fold ([acc answer⊥])
             ([(lchoice lres) (in-hash (eeval l ρ store-spaces μ choices certain?))])
           (match-define (Abs-Result/effect lcertain? lv store-spaces* μ*) lres)
           (for/fold ([acc acc]) ([(rchoice rres)
                                   (in-hash (eeval r ρ store-spaces* μ* lchoice lcertain?))])
             (match-define (Abs-Result/effect rcertain? rv store-spaces** μ**) rres)
             (define equalv (a/equal? lv rv store-spaces** μ**))
             (hash-set acc rchoice
                       (Abs-Result/effect rcertain? (to-data equalv)
                                          store-spaces** μ**))))]

        ;; depending of mf analysis, the interaction can be anything
        [(Meta-function-call _ _ f arg)
         ;; meta-functions also have non-deterministic choice.
         (for/hash ([(choice res)
                     (in-hash
                      (mf-eval ς
                               store-spaces
                               (hash-ref Ξ f (λ () (error "Unknown meta-function ~a" f)))
                               (pattern-eval arg ρ)
                               μ))])
           (values (append choice choices) res))]

        [(If _ _ g t e)
         (define gress (eeval g ρ store-spaces μ choices certain?))
         (for/fold ([acc answer⊥]) ([(gchoice gres) (in-hash gress)])
           (match-define (Abs-Result/effect gcertain? g store-spaces* μ*) gres)
           (define (then) (eeval t ρ store-spaces* μ* gchoice gcertain?))
           (define (else) (eeval e ρ store-spaces* μ* gchoice gcertain?))
           (answer-⊔
            acc
            (match g
              [(or (Datum b) (? boolean? b)) (if b (then) (else))]
              [(Abs-Data _ data)
               (if (set-member? data #f)
                   (if (= (set-count data) 1)
                       (else)
                       (answer-⊔ (then) (else)))
                   (then))]
              ;; Everything else truish.
              [_ (then)])))]

        ;; Really match-let
        [(Let _ _ (BSCS _ bindings) bexpr)
         (expr-eval-bindings
          ς bindings ρ store-spaces μ choices certain?
          (λ (ρ store-spaces μ choices certain?)
             (eeval bexpr ρ store-spaces μ choices certain?)))]

        ;; TODO?: allow rules to have expressions in the rhs
        [(Match _ _ dexpr rules)
         (for/fold ([results answer⊥])
             ([(dchoice dres) (in-hash (eeval dexpr ρ store-spaces μ choices certain?))])
           (match-define (Abs-Result/effect dcertain? dv store-spaces* μ*) dres)
           (answer-⊔ results
                     (rules-in-order ς ρ store-spaces* μ* rules dv)))]

;;; Set operations

        [(Set-empty? _ _ set-expr)
         (for/fold ([results answer⊥])
             ([(schoice setres) (in-hash (eeval set-expr ρ store-spaces μ choices certain?))])
           (match-define (Abs-Result/effect scertain? setv store-spaces* μ*) setres)
           (for/fold ([results results]) ([setv (in-data setv)])
             (match setv
               [(fset (℘ _ _ vcomp) S)
                (define pc (Component-pc vcomp))
                (case pc
                  [(concrete discrete)
                   ;; concrete domain is obvious
                   ;; UNCHECKED ASSUMPTION:
                   ;; discrete domain: if there is any abstract value in the set,
                   ;;  there must be at least one concrete value that it corresponds to.
                   (answer-⊔1 results schoice
                            (Abs-Result/effect scertain?
                                               (to-data (set-empty? S))
                                               store-spaces* μ*))]
                  ;; Abstract domains may have conflicting constraints that lead
                  ;; to no concrete counterparts. We are especially cautious here.
                  [(abstract)
                   (answer-⊔1 results schoice
                            (Abs-Result/effect
                             scertain?
                             (to-data
                              (b∨ (set-empty? S)
                                  ;; If every element is > 1, we output maybe,
                                  ;; since they may also be size 0
                                  ;; If any element is = 1, we output #f
                                  ;; ASSERTION: size exact 0 should never be live.
                                  (match
                                    (for/b⊔ ([sv (in-set S)])
                                            (∣γ∣>1 sv μ))
                                    [#t 'b.⊤]
                                    [_ #f]))))
                            store-spaces* μ*)])]
               [other
                (log-info (format "Set-empty? given non-set ~a" other))
                results])))]

        [(or (Set-Union _ _ set-expr exprs)
             ;; FIXME?: must trust that the expressions all fit in the same
             ;; concrete/discrete or abstract domain as the set.
             (Set-Add* _ _ set-expr exprs))
         (define-values (set-op sane? verb-phrase)
           (if (Set-Add*? e)
               (values set-add (const #t) "add to" #f)
               (values set-union
                       (λ (s)
                          (or (set? s)
                              (not (log-info (format "Cannot union not-set ~a" s)))))
                       "union")))
         (for/fold ([results answer⊥])
             ([(schoice setres) (in-hash (eeval set-expr ρ store-spaces μ choices certain?))])
           (match-define (Abs-Result/effect scertain? setv store-spaces* μ*) setres)
           (for/fold ([results results]) ([setv (in-data setv)])
             (define-values (container S)
               (match setv
                 [(fset scomp S) (values (λ (S) (fset scomp S)) S)]
                 [other
                  (log-info (format "Cannot ~a non-set ~a" verb-phrase other))
                  #f]))
             (cond
              [container
               (let ev-all ([choices schoice]
                            [certain? scertain?]
                            [exprs exprs]
                            [cur-set S]
                            [store-spaces store-spaces*]
                            [μ μ*])
                 (match exprs
                   ['() (hash choices
                              (Abs-Result/effect certain? (container cur-set) store-spaces μ))]
                   [(cons expr exprs)
                    (for/fold ([results results])
                        ([(echoice res) (in-hash (eeval expr ρ store-spaces μ choices certain?))])
                      (match-define (Abs-Result/effect vcertain? v store-spaces* μ*) res)
                      (for/fold ([results results]) ([v (in-data v)]
                                                     #:when (sane? v))
                        (answer-⊔ results
                                  (ev-all echoice vcertain? exprs
                                          (set-op cur-set v)
                                          store-spaces* μ*))))]
                   [_ (error 'set-add* "Bad exprs ~a" exprs)]))]
              [else results])))]

        [(Set-Remove* _ _ set-expr exprs)
         (reduce ς a/set-remove set-expr exprs ρ store-spaces μ choices certain?)]

        [(Set-Intersect _ _ set-expr exprs)
         (reduce ς a/set-binary-intersect set-expr exprs ρ store-spaces μ choices certain?)]

        [(Set-Subtract _ _ set-expr exprs)
         (reduce ς a/set-binary-intersect set-expr exprs ρ store-spaces μ choices certain?)]

        [(In-Set? _ _ set-expr expr)
         (for/fold ([results answer⊥])
             ([(schoice setres) (in-hash (eeval set-expr ρ store-spaces μ choices certain?))])
           (match-define (Abs-Result/effect scertain? setv store-spaces* μ*) setres)
           (for/fold ([results results]) ([setv (in-data setv)])
             (define vcres (eeval expr ρ store-spaces* μ* schoice scertain?))
             (define eq-check
               (match setv
                 [(fset scomp S)
                  (define pc (Component-pc scomp))
                  (case pc
                    [(abstract) (λ (v store-spaces μ)
                                   (abstract-in-set? S v store-spaces μ))]
                    [(discrete) (λ (v store-spaces μ)
                                   (discrete-in-set? S v store-spaces μ))]
                    [(concrete) (λ (v store-spaces μ) (set-member? S v))])]
                 [other
                  (log-info (format "In-Set? given non-set ~a" other))
                  #f]))
             (cond
              [eq-check
               (for/fold ([results results])
                   ([(vchoice vres) (in-hash vcres)])
                 (match-define (Abs-Result/effect vcertain? v store-spaces** μ**) vres)
                 (for/fold ([results results]) ([v (in-data v)])
                   (define equalv (eq-check v store-spaces** μ**))
                   (answer-⊔1 results vchoice
                            (Abs-Result/effect vcertain? (to-data equalv) store-spaces** μ**))))]
              [else results])))]

        [(??? _ _ label) (error 'expr-eval "Reached unimplemented code ~a" label)]

        [bad (error 'expr-eval "Bad expression ~a" bad)]))
    (dtrace eeval)
    (eeval e ρ store-spaces μ incoming-choices incoming-certain?))

  ;; FIXME: distinguish stuck expressions from failing side-conditions to properly
  ;; continue to try the following rule.

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
                (for/fold ([acc acc]) ([cv (in-data cv)]
                                       [dρ (in-match-results (a/match pat cv ρ store-spaces* μ))])
                  (combine acc
                   (match dρ
                     [(May ρ*)
                      (log-info (format "Possible failed match in let ~a ~a" binding cv))
                      (proc-bindings cchoice 'b.⊤ bindings ρ* store-spaces* μ*)]
                     [ρ*
                      (proc-bindings cchoice ccertain? bindings ρ* store-spaces* μ*)]))))]
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
                (for/fold ([results results])
                    ([(vchoice vres)
                      (in-hash
                       (slow-expression-eval ς val-expr ρ store-spaces* μ* kchoice kcertain?))])
                  (match-define (Abs-Result/effect vcertain? v store-spaces** μ**) vres)
                  (for/fold ([results results]) ([k (in-data k)])
                    (combine
                     results
                     (proc-bindings vchoice vcertain? bindings ρ (setter store-spaces** k v) μ**)))))]
             [(When expr)
              (define condres (slow-expression-eval ς expr ρ store-spaces μ choices certain?))
              (for/fold ([results out⊥]) ([(vchoice vres) (in-hash condres)])
                (match-define (Abs-Result/effect vcertain? v store-spaces* μ*) vres)
                (define (pass certain?)
                  (proc-bindings vchoice certain? bindings ρ store-spaces* μ*))
                (match v
                  [(Abs-Data _ S)
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
  (define (set-union-check s₀ s₁)
    (unless (set? s₀) (error 'set-union-check "Expected set for first argument, got ~a" s₀))
    (unless (set? s₁) (error 'set-union-check "Expected set for second argument, got ~a" s₁))
    (set-union s₀ s₁))
  (mk-slow-eval-bindings set-eval-bindings ∅ set-union-check)

  (define (slow-rule-eval rule ς)
    (match-define (Rule name lhs rhs (BSCS store-interaction binding-side-conditions) _ _) rule)
    (match-define (Abs-State d store-spaces μ τ̂) ς)
    (define res (a/match lhs d ρ₀ store-spaces μ))
    (for/union ([dρ (in-match-results res)])
      (define ρ (match dρ [(May ρ) ρ] [ρ ρ]))
      (set-eval-bindings
       ς
       binding-side-conditions ρ store-spaces μ '() #t
       (λ (ρ store-spaces μ choices certain?)
          (dprintf "FIRE! ~a~%" name)
          (unless (and certain? (not (May? dρ)))
            (log-info
             (format "Possible misfire of rule due to imprecise match Rule: ~a Env: ~a Choices: ~a"
                     rule ρ choices)))
          (define new-term (pattern-eval rhs ρ))
          (set (Abs-State new-term store-spaces μ (trace-update ς new-term choices τ̂)))))))

  #|
  To run mutually-recursively but as a fixed-point computation, we need a
  /dynamically/ scoped memo-table, or a global memo-table (too space-inefficient).
  At the top level, a meta-function starts evaluating and sets up the memo table.
  If an entry is present:
  Entry is #f: we have hit an infinite loop ; thus memoize to ∅.
  Entry is a set: the meta-function has fully evaluated and these are all its results.
  If not present, set entry to #f and evaluate to all results. Then set entry to the set.

  TODO: mf's given a "trust recursion" tag to not do this space-intensive memoization.
  |#
;; Hasheq[Meta-function,Hash[(List State Store-Spaces Abs-Count DPattern),Set[Abs-Result/effect]]
(define mf-memo (make-parameter #f))
(define (slow-meta-function-eval ς store-spaces mf argd μ)
  (match-define (Meta-function name rules _ _ trusted-implementation/abs) mf)
  (dprintf "Running ~a~%" name)
  (define (do-mf-eval table)
    (define mf-table (hash-ref! table mf make-hash))
    (define key (list ς store-spaces μ argd))
    (match (hash-ref mf-table key -unmapped)
      [#f ;; infinite loop. Reached same key.
       (hash-set! mf-table key answer⊥)
       answer⊥]
      [(== -unmapped eq?)
       (hash-set! mf-table key #f)
       (define results (rules-in-order ς ρ₀ store-spaces μ rules argd))
       (hash-set! mf-table key results)
       results]
      [results results]))
  (if trusted-implementation/abs
      (trusted-implementation/abs L ς store-spaces μ argd)
      (match (mf-memo)
        [#f (define table (make-hasheq))
            (parameterize ([mf-memo table])
              (do-mf-eval table))]
        [table (do-mf-eval table)])))
(dtrace slow-meta-function-eval)

(define (rules-in-order ς ρ store-spaces μ rules argd)
  (let try-rules ([rules rules] [results answer⊥])
    (match rules
      ['()
       (when (equal? results answer⊥)
         (log-info (format "No rules matched for ~a (rules ~a)" argd rules)))
       results]
      [(cons (and rule (Rule name lhs rhs (BSCS store-interaction binding-side-conditions) _ _))
             rules)
       (define found?-Ivar (box #f)) ;; only increases, thus a classic Ivar.
       (define results*
         (for/fold ([results results])
             ([dρ (in-match-results (a/match lhs argd ρ store-spaces μ))])
           (define-values (b♯ ρ*)
             (match dρ [(May ρ) (values 'b.⊤ ρ)] [ρ (values #t ρ)]))
           (expr-eval-bindings
            ς
            binding-side-conditions ρ* store-spaces μ '() b♯
            (λ (ρ store-spaces μ choices certain?)
               (dprintf "FIRE ~a~%" name)
               (define results*
                 (answer-⊔1 results choices
                          ;; Quality is #t since meta-functions' evaluation does not affect
                          ;; the matching of a rule.
                          (Abs-Result/effect #t (pattern-eval rhs ρ) store-spaces μ)))
               (cond
                ;; True match; we can stop searching through rules.
                [certain?
                 (set-box! found?-Ivar #t)
                 results*]
                [else
                 (log-info
                  (format "Possible misfire of meta-function rule due to imprecise match ~a ~a ~a"
                          rule rhs ρ))
                 (set-box! (b∨ (unbox found?-Ivar) 'b.⊤))
                 results*])))))
       (match (unbox found?-Ivar)
         [#t results*]
         [_ (try-rules rules results*)])])))

(define mf-eval slow-meta-function-eval)
(define rule-eval slow-rule-eval)
(define expression-eval slow-expression-eval))

(define-compound-unit/infer abstract-semantics@
  (import language-parms^)
  (export language-impl^)
  (link
   ;; a/equal? a/match
   abstract-matching/equality@
   ;; [discrete|abstract]-[set-remove|in-set?] a/set-remove a/set-binary-[intersect|subtract]
   abstract-set-ops@
   ;; [discrete|abstract]-remove a/map-remove
   abstract-map-ops@
   ;; expression-eval rule-eval mf-eval
   abstract-reduction@))
