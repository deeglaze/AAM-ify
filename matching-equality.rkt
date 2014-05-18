#lang racket/base
(require "signatures.rkt" "spaces.rkt" "lattices.rkt" "term-lattices.rkt"
         racket/fixnum racket/unsafe/ops racket/match racket/set racket/sequence racket/unit
         (only-in racket/bool implies)
         (only-in "shared.rkt" in-space? in-component? store-ref dtrace dprintf))
(provide abstract-matching/equality@
         in-match-results)

(define (match-⊔ m₀ m₁)
  (match* (m₀ m₁)
    [(#f m₁) m₁]
    [(m₀ #f) m₀]
    [((? set? M₀) (? set? M₁)) (set-union M₀ M₁)]
    [((? set? M₀) m₁) (set-add M₀ m₁)]
    [(m₀ (? set? M₁)) (set-add M₁ m₀)]
    [(_ _) (set m₀ m₁)]))

(define (quality->match q ρ)
  (match q
    [#t ρ]
    [#f #f]
    ['b.⊤ (May ρ)]))

(define (quality-⊔ may? ρ)
  (if (and may? (not (May? ρ)))
      (May ρ)
      ρ))

(define (in-match-results m)
  (match m
    [#f empty-sequence]
    [(? set? M) (in-set M)]
    [m (in-value m)]))

(define-unit abstract-matching/equality@
  (import language-parms^ abstract-set-ops^ abstract-map-ops^)
  (export matching-equality^)
  (define (a/match pattern data ρ store-spaces μ)
    ;; inner returns the certainty of the match and the updated map.
    (define (inner pattern data ρ)
      (match* (pattern data)
        [((is-a c) d)
         (and (in-component? L c d)
              ρ)]

        [((Name x pat) d)
         (match (hash-ref ρ x -unmapped)
           [(== -unmapped eq?)
            (for/fold ([result #f]) ([dρ (in-match-results (inner pat d ρ))])
             (match-⊔
              result
              (match dρ
                [(May ρ) (May (hash-set ρ x d))]
                [ρ (hash-set ρ x d)])))]
           [other
            (match (a/equal? other d store-spaces μ)
              [#f #f]
              [b♯ (define may? (eq? b♯ 'b.⊤))
                  (for/fold ([result #f]) ([dρ (in-match-results (inner pat d ρ))])
                    (match-⊔ result (quality-⊔ may? dρ)))])])]

        [((variant v comps) (variant v* data))
         (cond
          [(eq? (Variant-name v) (Variant-name v*))
           (define len (min (vector-length comps) (vector-length data)))
           (define (match-comps i ρ quality)
             (cond
              [(fx= i len) (quality->match quality ρ)]
              [else
               (define comp (unsafe-vector-ref comps i))
               (define d (unsafe-vector-ref data i))
               (for/fold ([acc #f]) ([dρ (in-match-results (inner comp d ρ))])
                 (match-⊔ acc
                          (match dρ
                            [(May ρ) (match-comps (add1 i) ρ 'b.⊤)]
                            [ρ (match-comps (add1 i) ρ quality)])))]))
           (dtrace match-comps)
           (match-comps 0 ρ #t)]
          [else
           (dprintf "Different names ~a ~a~%" (Variant-name v) (Variant-name v*))
           #f])]

        ;; NOTE: abstract-ffun and abstract-set can have 0 elements concretely
        ;; but still have represented values. In this case, the match results will
        ;; be qualified as May, so further matching can progress.

        ;; Map-with peels off kv pairs outside-in
        [((Map-with kpat vpat mpat mode _) m)
         (define map (ffun-dict m))
         (match mode
            ['first
             (for*/or
                 ([(k v) (in-hash map)]
                  [kdρ (in-match-results (inner kpat k ρ))]
                  [kρ (in-value (match kdρ [(May ρ) ρ] [ρ ρ]))]

                  [vdρ (in-match-results (inner vpat v kρ))]
                  [vρ (in-value (match vdρ [(May ρ) ρ] [ρ ρ]))]

                  [M (in-value (a/map-remove m k store-spaces μ))]
                  [may? (in-value (or (May? kdρ) (May? vdρ) (Abs-Data? M)))]
                  [m* (in-data M)]
                  [mdρ (in-match-results (inner mpat m* vρ))])
               (quality-⊔ may? mdρ))]

            ['all
             (for*/fold ([results #f])
                 ([(k v) (in-hash map)]
                  [kdρ (in-match-results (inner kpat k ρ))]
                  [kρ (in-value (match kdρ [(May ρ) ρ] [ρ ρ]))]

                  [vdρ (in-match-results (inner vpat v kρ))]
                  [vρ (in-value (match vdρ [(May ρ) ρ] [ρ ρ]))]

                  [M (in-value (a/map-remove m k store-spaces μ))]
                  [may? (in-value (or (May? kdρ) (May? vdρ) (Abs-Data? M)))]
                  [m* (in-data M)]
                  [mdρ (in-match-results (inner mpat m* vρ))])
               (match-⊔ results (quality-⊔ may? mdρ)))]

            ['best
             (define-values (dummy best-ρ)
               (for*/fold ([best-quality #f]
                           [best-ρ #f])
                   ([(k v) (in-hash map)]
                    [kdρ (in-match-results (inner kpat k ρ))]
                    [kρ (in-value (match kdρ [(May ρ) ρ] [ρ ρ]))]

                    [vdρ (in-match-results (inner vpat v kρ))]
                    [vρ (in-value (match vdρ [(May ρ) ρ] [ρ ρ]))]

                    [M (in-value (a/map-remove m k store-spaces μ))]
                    [may? (in-value (or (May? kdρ) (May? vdρ) (Abs-Data? M)))]
                    [m* (in-data M)]
                    [mdρ (in-match-results (inner mpat m* vρ))])
                 (if may?
                     (if best-quality
                         (values best-quality best-ρ)
                         (values 'b.⊤ mdρ))
                     (if (eq? best-quality #t)
                         (values best-quality best-ρ)
                         (values #t mdρ)))))
             best-ρ])]

        [((Set-with vpat spat mode _) s)
         (define S (fset-set s))
         (match mode
           ['first
            (for*/or
                ([v (in-set S)]
                 [vdρ (in-match-results (inner vpat v ρ))]
                 [vρ (in-value (match vdρ [(May ρ) ρ] [ρ ρ]))]

                 [s* (in-value (a/set-remove s v store-spaces μ))]
                 [may? (in-value (or (May? vdρ) (Abs-Data? s*)))]
                 [s* (in-data s*)]
                 [sdρ (in-match-results (inner spat s* vρ))])
              (quality-⊔ may? sdρ))]

           ['all
            (for*/fold ([results #f])
                ([v (in-set S)]
                 [vdρ (in-match-results (inner vpat v ρ))]
                 [vρ (in-value (match vdρ [(May ρ) ρ] [ρ ρ]))]

                 [s* (in-value (a/set-remove s v store-spaces μ))]
                 [may? (in-value (or (May? vdρ) (Abs-Data? s*)))]
                 [s* (in-data s*)]
                 [sdρ (in-match-results (inner spat s* vρ))])
              (match-⊔ results (quality-⊔ may? sdρ)))]

           ['best
            (define-values (dummy best-ρ)
              (for*/fold ([best-quality #f]
                          [best-ρ #f])
                  ([v (in-set S)]
                   [vdρ (in-match-results (inner vpat v ρ))]
                   [vρ (in-value (match vdρ [(May ρ) ρ] [ρ ρ]))]

                   [s* (in-value (a/set-remove s v store-spaces μ))]
                   [may? (in-value (or (May? vdρ) (Abs-Data? s*)))]
                   [s* (in-data s*)]
                   [sdρ (in-match-results (inner spat s* vρ))])
                (if may?
                    (if best-quality
                        (values best-quality best-ρ)
                        (values 'b.⊤ sdρ))
                    (if (eq? best-quality #t)
                        (values best-quality best-ρ)
                        (values #t sdρ)))))
            best-ρ])]

        ;; Wildcard/don't-care
        [((? Anything?) d) ρ]

        [((Anything* c) d)
         (if debug-mode
             (and (in-component? L c d) ρ)
             ρ)]
        ;; TODO: Add better syntax checking to rule this out before interpretation.
        [((? Rvar?) x) (error 'a/match "Unexpected reference in match pattern ~a" x)]

        [(a₀ a₁) (quality->match (a/equal? a₀ a₁ store-spaces μ) ρ)]))
    (dtrace inner)
    (inner pattern data ρ))

  ;; Takes language to get access to external spaces' cardinality analyses.
  (define (a/equal? d₀ d₁ store-spaces μ)
    (define (abstract-ffun-equal? f₀ f₁)
      (b∧ (ffun-⊑? f₀ f₁)
          (ffun-⊑? f₁ f₀)))

    ;; Slow path: linearly look for a key "equal" to k with "equal" values.
    (define (slow-equal k v f)
      (for/b∨ ([(k₁ v₁) (in-hash f)])
              (b∧ (a/equal? k k₁)
                  (a/equal? v v₁))))

    (define (ffun-⊑? dom f₀ f₁)
      (for/b∧ ([(k v) (in-hash f₀)])
              (match (hash-ref f₁ k -unmapped)
                [(== -unmapped eq?) (slow-equal k v f₁)]
                [v₁ ;; fast path: check the structurally equal key
                 (b∨ (a/equal? v v₁)
                     (slow-equal k v f₁))])))

    (define (concrete-ffun-equal? m₀ m₁)
      (and (= (hash-count m₀) (hash-count m₁))
           (for/b∧ ([(k₀ v₀) (in-hash m₀)])
                   (match (hash-ref m₁ k₀ -unmapped)
                     ;; Concrete domains w/o structural equality are actually abstract.
                     ;; Note this is different from the concrete semantics.
                     [(== -unmapped eq?) #f]
                     ;; Note we don't use b∨ with the slow path
                     [v₁ (a/equal? v₀ v₁)]))))

    (define (discrete-ffun-equal? m₀ m₁)
      (and (= (hash-count m₀) (hash-count m₁))
           (for/b∧ ([(k₀ v₀) (in-hash m₀)])
                   (match (hash-ref m₁ k₀ -unmapped)
                     [(== -unmapped eq?) #f]
                     [v₁ (b∧
                          ;; Discrete maps get structural equality on keys, but can only be
                          ;; truly equal if the key has cardinality 1.
                          (if (∣γ∣>1 k₀ μ) 'b.⊤ #t)
                          (a/equal? v₀ v₁))]))))

    (define (addr->quality a)
      (match (hash-ref μ a 'ω)
        [1 #t]
        ['ω 'b.⊤]
        [0 (error 'a/equal? "Live address with count 0: ~a (Counts ~a) (Store ~a)"
                  a μ store-spaces)]))

    (define (equal-step d₀ d₁)
      (match* (d₀ d₁)
        ;; We match on name instead of identity due to Variant refinements
        [((variant v ds₀) (variant v* ds₁))
         (and (eq? (Variant-name v) (Variant-name v*))
              (for/b∧ ([d₀ (in-vector ds₀)]
                       [d₁ (in-vector ds₁)])
                      (a/equal? d₀ d₁)))]

        ;; Addresses are the same if they have cardinality 1. Distinct addresses don't overlap.
        [((Address space a _ 'Identity) (Address space a _ _))
         (addr->quality a)]
        [((Address space a _ _) (Address space a _ 'Identity))
         (addr->quality a)]

        [((Address space a₀ _ 'Deref) (Address space a₁ _ 'Deref))
         (or (and (equal? a₀ a₁)
                  (eq? (addr->quality a₀) #t))
             ;; INVARIANT: not possible to be -unmapped since there must be
             ;; at least one value mapped in a store's address.
             (for*/b⊔ ([d₀ (in-set (hash-ref (hash-ref store-spaces space) a₀))]
                       [d₁ (in-set (hash-ref (hash-ref store-spaces space) a₁))])
                      (a/equal? d₀ d₁)))]
        [((Address space a _ 'Deref) d₁)
         ;; inline store-ref
         (for*/b⊔ ([d₀ (in-set (hash-ref (hash-ref store-spaces space) a))])
                  (a/equal? d₀ d₁))]
        [(d₀ (Address space a _ 'Deref))
         ;; inline store-ref
         (for*/b⊔ ([d₁ (in-set (hash-ref (hash-ref store-spaces space) a))])
                  (a/equal? d₀ d₁))]

        [((ffun (Map _ _ kcomp₀ _) m₀) (ffun (Map _ _ kcomp₁ _) m₁))
         (define pc₀ (Component-pc kcomp₀))
         (define pc₁ (Component-pc kcomp₁))
         (and (eq? pc₀ pc₁)
              (case pc₀
                [(concrete) (concrete-ffun-equal? m₀ m₁)]
                [(discrete) (discrete-ffun-equal? m₀ m₁)]
                [(abstract) (abstract-ffun-equal? m₀ m₁)]))]

        [((fset vcomp₀ s₀) (fset vcomp₁ s₁))
         (define pc₀ (Component-pc vcomp₀))
         (define pc₁ (Component-pc vcomp₁))
         (and (eq? pc₀ pc₁)
              (case pc₀
                [(concrete)
                 (equal? s₀ s₁)]
                [(discrete)
                 (b∧ (equal? s₀ s₁)
                     (implies (for/or ([v (in-set s₀)]) (∣γ∣>1 v μ)) 'b.⊤))]
                [(abstract)
                 (define (⊆? s₀ s₁)
                   (for/b∧ ([v (in-set s₀)])
                           (for/b∨ ([v* (in-set s₁)])
                                   (a/equal? v v*))))
                 (b∧ (⊆? s₀ s₁) (⊆? s₁ s₀))]))]

        [(atom atom) #t]

        [((external ex v₀) (external ex v₁))
         (match-define (External-Space _ card precision ≡ _ _ _) ex)
         (if ≡
          (≡ v₀ v₁ store-spaces μ a/equal?)
          (case precision
            [(concrete) (equal? v₀ v₁)]
            [(discrete)
             (b∧ (equal? v₀ v₁)
                 (implies (eq? (card v₀ μ) 'ω) 'b.⊤))]
            [(abstract) (error 'a/equal? "Cannot have non-discrete abstraction of external values without a custom equality relation ~a" d₀)]))]
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
  )
