#lang racket/base
(require "spaces.rkt" "shared.rkt" "ternary-counting.rkt"
         racket/match racket/dict racket/set racket/list)
#|
The abstract semantics differs from the concrete semantics in the following ways:
- equality matching is uncertain and is aided by cardinality analysis
- map lookup is uncertain and is aided by cardinality analysis
- meta-function evaluation must be done via fixed point computation
- Map-extend in maps with "abstract" domain change to weak updates (range already is lifted to ℘)
|#


;; Takes language to get access to external spaces' cardinality analyses.
(define ((a/equal? L) d₀ d₁ store-spaces μ)
  (define/match (egal-equal? a₀ a₁)
    [((Address-Egal space a) (Address-Egal space a))
     (match (hash-ref μ a₀ 'ω)
       [1 #t]
       ['ω 'b.⊤]
       [0 (error 'a/match "Live address with count 0: ~a (Counts ~a) (Store ~a)" a₀ μ store-spaces)])]
    [(_ _) #f])

  (define (equal-step d₀ d₁)
    (match* (d₀ d₁)
      [((Variant name ds₀) (Variant name ds₁))
       (for/b∧ ([d₀ (in-vector ds₀)]
                [d₁ (in-vector ds₁)])
               (a/equal? d₀ d₁))]

      ;; Maps need special treatment in the abstract.
      [((? dict? d₀) (? dict? d₁))
       (error 'a/match "Get abstract maps working.")]

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

      [(atom atom) #t]
      ;; TODO: external space equality checking
      [(_ _) #f]))

  ;; Circular addresses are possible
  (define seen (make-hasheq))
  (define (a/equal? d₀ d₁)
    (define checked-against (hash-ref! seen d₀ mutable-seteq))
    ;; already checked ⇒ assume equal
    ;; XXX: should this be #t or 'b.⊤?
    (or (set-member? checked-against d₁)
        (begin (set-add! checked-against d₁)
               (equal-step d₀ d₁))))

  (a/equal? d₀ d₁))

(define (a/match L)
  (define Lequal? (a/equal? L))
  (λ (pattern data store-spaces ρ μ)
     ;; inner returns the quality of the match and the updated map.
     (define (inner pattern data ρ)
       (match* (pattern data)
         [((Bvar x Space-name) d)
          (match (dict-ref ρ x -unmapped)
            [(== -unmapped eq?)
             (define (do-update) (values #t (dict-set ρ x d)))
             (cond
              [Space-name ;; Space provided ⇒ check if in space.
               (if (in-space? d L Space-name)
                   (do-update)
                   (values #f #f))]
              [else (do-update)])]
            [other (values (Lequal? other d store-spaces μ) ρ)])]
         
         [((Variant name comps) (Variant name data))
          (for/fold ([b #t] [ρ ρ])
              ([comp (in-vector comps)]
               [d (in-vector data)])
            (define-values (b* ρ*) (inner comp d ρ))
            (values (b∧ b b*) ρ*))]

         ;; Wildcard/don't-care
         [((? Anything?) d) (values #t ρ)]
         ;; TODO: Add better syntax checking to rule this out before interpretation.
         [((? Rvar?) x) (error 'a/match "Unexpected reference in match pattern ~a" x)]

         [(a₀ a₁) (values (Lequal? a₀ a₁ store-spaces μ) ρ)]))

     ;; TODO?: get rid of May and Must and just use multiple values
     (let-values ([(b ρ) (inner pattern data ρ)])
       (match b
         [#t (Must ρ)]
         [#f #f]
         ['b.⊤ (May ρ)]))))

(define (a/expression-eval* L e ρ Ξ [μ #f])
  (error 'a/expression-eval* "TODO"))

(define (a/rule-eval* L rule store-name d Ξ)
  (error 'a/rule-eval* "TODO"))

(define (a/meta-function-eval L mf argd store-name Ξ [μ #f])
  (error 'a/meta-function-eval))