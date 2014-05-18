#lang racket/base

#|
This module defines the concrete semantics of reduction for languages written
in the spaces.rkt format.
|#

(require racket/match racket/set racket/dict racket/promise
         racket/list
         racket/unit
         "spaces.rkt"
         "shared.rkt"
         "signatures.rkt")
(provide concrete-semantics@)

(define-unit concrete-semantics@
  (import language-parms^)
  (export language-impl^)

  ;; c/match : Language → Pattern DPattern Map[Symbol, DPattern] → Option[Map[Symbol, DPattern]]
;; Concrete match. References' ∀? component does not matter.
;; There is at most one match.
;; If there is a match, the result is the binding environment. Otherwise #f.
(define (c/match pattern data ρ store-spaces)
  (define (inner pattern data ρ)
    (match* (pattern data)
      [((is-a space-name) d)
       (cond
        [(in-space? L space-name d) ρ]
        [else
         (log-info (format "space mismatch ~a ~a~%" space-name d))
         #f])]

      [((Name x pat) d)
       (match (dict-ref ρ x -unmapped)
         [(== -unmapped eq?)
          (match (inner pat d ρ)
            [#f #f]
            [ρ (hash-set ρ x d)])]
         [other (and (equal? other d) (inner pat d ρ))])]

      [((variant v comps) (variant v* ds))
       (cond
        [(eq? (Variant-name v) (Variant-name v*))
         ;; INVARIANT: Variants with the same name always have the same length.
         (define len (vector-length comps))
         (for/fold ([ρ ρ]) ([comp (in-vector comps)]
                            [d (in-vector ds)])
           (define ρ* (inner comp d ρ))
           #:final (not ρ*)
           ρ*)]
        [else (log-info "Match failure: variant mismatch ~a ~a" pattern data)
              #f])]

      [((Map-with kpat vpat mpat mode _) d)
       (error 'c/match "TODO Map-with")]

      [((Set-with vpat spat mode _) d)
       (error 'c/match "TODO Set-with")]

      [((? Rvar?) x) (error 'c/match "Unexpected reference in match pattern ~a" x)]

      [((and a₀ (Address space a _ 'Deref)) d)
       (inner (store-ref store-spaces a₀) d)]
      [(d (and a₁ (Address space a _ 'Deref)))
       (inner d (store-ref store-spaces a₁))]

      [((? dict? m₀) (? dict? m₁))
       (and (= (dict-count m₀) (dict-count m₁))
            (for/and ([(k₀ v₀) (in-dict m₀)])
              (match (dict-ref m₁ k₀ -unmapped)
                [(== -unmapped eq?)
                 ;; Slow path: linearly look for a key "equal" to k with "equal" values.
                 (for/or ([(k₁ v₁) (in-dict m₁)])
                   (and (inner k₀ k₁ ρ)
                        (inner v₀ v₁ ρ)))]
                [v₁ (inner v₀ v₁ ρ)])))]

      ;; this also captures equal Address-Egal values.
      [(atom atom) ρ]
      [(_ _)
       (log-info (format "c/match negative ~a ~a" pattern data))
       #f]))
  (inner pattern data ρ))

;; c/expression-eval : Language Expression Map[Symbol,DPattern] Map[Symbol,Meta-function] → ℘(DPattern)
;; Concrete evaluation of expressions. Returns entire set of possible evaluations
;; due to Choose expressions.
(define (expression-eval e ρ store-spaces)
  (match e
    [(Store-lookup _ _ kexpr)
     (for/set ([kres (in-set (expression-eval kexpr ρ store-spaces))])
       (match-define (State kv store-spaces*) kres)
       (State (store-ref store-spaces kv) store-spaces*))]
    [(Map-lookup _ _ m kexpr default? dexpr)
     (define ks (expression-eval kexpr ρ store-spaces))
     (define map (hash-ref ρ m (unbound-map-error 'map-ref m)))
     (for/fold ([res ∅]) ([kres (in-set ks)])
       (match-define (State k store-spaces*) kres)
       (match (hash-ref map k -unmapped)
         [(== -unmapped eq?)
          (if default?
              (set-union res (expression-eval dexpr ρ store-spaces*))
              (error 'map-ref "Key unmapped in map ~a: ~a" m k))]
         [v (set-add res (State v store-spaces*))]))]
    [(Map-extend _ _ m kexpr vexpr _)
     (define mv (hash-ref ρ m (unbound-map-error 'map-ext m)))
     (define ks (expression-eval kexpr ρ store-spaces))
     (for/fold ([acc ∅])
         ([kres (in-set ks)])
       (match-define (State k store-spaces*) kres)
       (for/fold ([acc acc]) ([vres (in-set (expression-eval vexpr ρ store-spaces*))])
         (match-define (State v store-spaces**) vres)
         (set-add acc (State (hash-set mv k v) store-spaces**))))]
    [(Empty-map _ _) (set (State #hash() store-spaces))]
    [(Map-empty? _ _ m)
     (set (State
           (eq? 0 (dict-count (hash-ref ρ m (unbound-map-error 'map-empty? m))))
           store-spaces))]
    [(Map-remove _ _ m kexpr)
     (error 'c/expression-eval "TODO map-remove")]

    [(Meta-function-call _ _ f arg)
     ;; meta-functions also have non-deterministic choice.
     (mf-eval store-spaces
              (hash-ref Ξ f (λ () (error "Unknown meta-function ~a" f)))
              (pattern-eval arg ρ))]
    [(If _ _ g t e)
     (for/union ([bres (in-set (expression-eval g ρ store-spaces))])
       (match-define (State b store-spaces*) bres)
       (if b
           (expression-eval t ρ store-spaces*)
           (expression-eval e ρ store-spaces*)))]
    [(Equal _ _ l r)
     (for/fold ([acc ∅])
         ([lres (in-set (expression-eval l ρ store-spaces))])
       (match-define (State lv store-spaces*) lres)
       (for/fold ([acc acc]) ([rres (in-set (expression-eval r ρ store-spaces*))])
         (match-define (State rv store-spaces**) rres)
         (set-add acc (State (equal? lv rv) store-spaces**))))]

    ;; Really let with non-linear pattern weirdness.
    [(Let _ _ bindings bexpr)
     (bindings-eval bindings ρ store-spaces
                    (λ (ρ store-spaces)
                       (expression-eval bexpr ρ store-spaces)))]

    [(Match _ _ dexpr rules)
     (for/fold ([acc ∅]) ([dres (in-set (expression-eval dexpr ρ store-spaces))])
       (match-define (State dv store-spaces*) dres)
       (set-union acc (for/or ([rule (in-list rules)])
                        (internal-rule-eval store-spaces* rule dv))))]

    [(Term _ _ pat) (set (State (pattern-eval pat ρ) store-spaces))]

    [(In-Dom? _ _ m kexpr)
     (define mv (hash-ref ρ m (unbound-map-error 'map-ext m)))
     (for/set ([kres (in-set (expression-eval kexpr ρ store-spaces))])
       (match-define (State kv store-spaces*) kres)
       (State (dict-has-key? mv kv) store-spaces*))]

    [(or (Set-Union _ _ set-expr exprs)
         (Set-Add* _ _ set-expr exprs)
         (Set-Remove* _ _ set-expr exprs)
         (Set-Intersect _ _ set-expr exprs)
         (Set-Subtract _ _ set-expr exprs))
     (define set-op
       (cond [(Set-Union? e) set-union]
             [(Set-Add*? e) set-add]
             [(Set-Remove*? e) set-remove]
             [(Set-Intersect? e) set-intersect]
             [(Set-Subtract? e) set-subtract]))
     (for/fold ([acc ∅]) ([sres (in-set (expression-eval set-expr ρ store-spaces))])
       (match-define (State sv store-spaces*) sres)
       (let do-set-op ([exprs exprs] [cur-set sv] [store-spaces store-spaces*])
         (match exprs
           ['() (set-union acc (State cur-set store-spaces))]
           [(cons expr exprs)
            (for/fold ([acc acc]) ([res (in-set (expression-eval expr ρ store-spaces))])
              (match-define (State v store-spaces*) res)
              (set-union acc
                         (do-set-op exprs (set-op cur-set v) store-spaces*)))])))]

    [(In-Set? _ _ set-expr expr)
     (for/fold ([acc ∅]) ([sres (in-set (expression-eval set-expr ρ store-spaces))])
       (match-define (State sv store-spaces*) sres)
       (for/fold ([acc acc]) ([res (in-set (expression-eval expr ρ store-spaces*))])
         (match-define (State v store-spaces*) res)
         (set-add acc (State (set-member? sv v) store-spaces*))))]
    [(Empty-set _ _) (set (State ∅ store-spaces))]

    ;; We get a set of results from expr. We expect these results to be sets.
    ;; We want to embody any (all) choices from these sets, so we flatten them into
    ;; a set of possible results.
    [(Choose _ _ _ expr)
     (for/fold ([acc ∅]) ([res (in-set (expression-eval expr ρ store-spaces))])
       (match-define (State some-set store-spaces*) res)
       (for/fold ([acc acc]) ([v (in-set some-set)])
         (set-add acc (State v store-spaces*))))]

    [(Alloc _ _ space mb eb hint)
     (set (State (Address space (gensym) mb eb) store-spaces))]

    [(? Datum? d) (set (State d store-spaces))]

    [bad (error 'expr-eval "Bad expression ~a" bad)]))

(define (bindings-eval bindings ρ store-spaces kont)
  (let proc-bindings ([bindings bindings] [ρ ρ] [store-spaces store-spaces])
    (match bindings
      ['() (kont ρ store-spaces)]
      [(cons (Binding pat cexpr) bindings)
       (for/fold ([acc ∅])
           ([cres (in-set (expression-eval cexpr ρ store-spaces))])
         (match-define (State cv store-spaces*) cres)
         (match (c/match pat cv ρ store-spaces)
           [#f acc]
           [ρ* (set-union acc (proc-bindings bindings ρ* store-spaces*))]))]
      [(cons (Store-extend kexpr vexpr _) bindings)
       (for/fold ([acc ∅]) ([kres (in-set (expression-eval kexpr ρ store-spaces))])
         (match-define (State kv store-spaces*) kres)
         (for/fold ([acc acc]) ([vres (in-set (expression-eval vexpr ρ store-spaces*))])
           (match-define (State vv store-spaces**) vres)
           (set-union acc
                      (proc-bindings bindings ρ (store-set store-spaces kv vv)))))]
      [(cons (When cexpr) bindings)
       (for/fold ([acc ∅]) ([cres (in-set (expression-eval cexpr ρ store-spaces))])
         (match-define (State cv store-spaces*) cres)
         (if cv
             (set-union acc (proc-bindings bindings ρ store-spaces*))
             acc))])))

;; rule-eval : Rule Map[Symbol,DPattern] DPattern Map[Symbol,Meta-function] → Optional[℘(DPattern)]
;; Evaluate a rule on some concrete term and return possible RHSs (#f if none, since ∅ is stuck)
(define (internal-rule-eval store-spaces rule d)
  (match-define (Rule name lhs rhs (BSCS _ binding-side-conditions) _ _) rule)
  (define found? (box #f))
  (match (c/match lhs d ρ₀ store-spaces)
    [#f #f]
    [ρ
     (define results
       (bindings-eval binding-side-conditions ρ store-spaces
                      (λ (ρ store-spaces)
                         (set-box! found? #t)
                         (set (State (pattern-eval rhs ρ) store-spaces)))))
     (and (unbox found?) results)]))

(define (rule-eval rule st)
  (match-define (State d store-spaces) st)
  (or (internal-rule-eval store-spaces rule d) ∅))

;; TODO?: Add ability to do safety checks on input/output belonging to a
;;        specified Space.
(define (mf-eval store-spaces mf argd)
  (match-define (Meta-function name rules _ trust/conc _) mf)
  (if trust/conc
      (trust/conc L store-spaces argd)
      ;; Use the first rule that matches.
      (for/or ([rule (in-list rules)])
        (internal-rule-eval store-spaces rule argd)))))
