#lang racket/base
(require racket/unit "spaces.rkt" "signatures.rkt" "lattices.rkt"
         "shared.rkt"
         racket/bool
         racket/match racket/set)
(provide abstract-set-ops@)

(define-unit abstract-set-ops@
  (import language-parms^ matching-equality^)
  (export abstract-set-ops^)
  
  (define (discrete-set-remove s v store-spaces μ)
    (match-define (discrete-set S) s)
    (cond
     [(set-member? S v)
      (define s* (discrete-set (set-remove S v)))
      (if (∣γ∣>1 v μ)
          (Abs-Data (set s s*))
          s*)]
     [else s]))

  (define (abstract-set-remove s v store-spaces μ)
    (match-define (abstract-set S) s)
    ;; remove every combination of values that match weakly.
    ;; always remove value if strongly matches.
    (define-values (S* weakly found?)
      (for/fold ([S* S] [weakly '()] [found? #f])
          ([v* (in-set S)])
        (match (a/equal? v v* store-spaces μ)
          [#t (values (set-remove S* v*) weakly (b⊔ found? #t))]
          [#f (values S* weakly found?)]
          ['b.⊤ (values S* (cons v* weakly) 'b.⊤)])))
    (match found?
      [#t (abstract-set S*)]
      [#f s]
      ['b.⊤
       (define unwrapped-sets
         (for*/fold ([Ss (set S*)]) ([v (in-list weakly)]
                                     [S (in-set Ss)])
           (set-add Ss (set-remove S v))))
       (Abs-Data (for/set ([S (in-set unwrapped-sets)]) (abstract-set S)))]))

  (define (a/set-remove s v store-spaces μ)
    (match s
      [(? set? S) (set-remove S v)]
      [(? discrete-set?) (discrete-set-remove s v store-spaces μ)]
      [(? abstract-set?) (abstract-set-remove s v store-spaces μ)]))


  (define (abstract-in-set? S v store-spaces μ)
    (for/b∨ ([sv (in-set S)])
            (a/equal? sv v store-spaces μ)))

  (define (discrete-in-set? S v store-spaces μ)
    (b∧ (set-member? S v)
        (implies (∣γ∣>1 v μ) 'b.⊤)))

  (define (a/set-binary-intersect s₀ s₁ store-spaces μ)

    (define (inter in-set? container S₀ S₁)
      (define-values (S* weakly)
        (for/fold ([S* ∅] [weakly '()]) ([v (in-set S₁)])
          (match (in-set? S₀ v store-spaces μ)
            [#t (values (set-add S* v) weakly)]
            [#f (values S* weakly)]
            ['b.⊤ (values S* (cons v weakly))])))
      (define unwrapped-sets
        (for*/fold ([sets (set S*)]) ([v (in-list weakly)]
                                      [S (in-set sets)])
          (set-add sets (set-add S v))))
      (Abs-Data (for/set ([S (in-set unwrapped-sets)]) (container S))))

    (match* (s₀ s₁)
      [((? set? S₀) (? set? S₁)) (set-intersect S₀ S₁)]
      
      [((discrete-set S₀) (discrete-set S₁))
       (inter discrete-in-set? discrete-set S₀ S₁)]
  
      [((abstract-set S₀) (abstract-set S₁))
       (inter abstract-in-set? abstract-set S₀ S₁)]
      [(_ _) (error 'a/set-binary-intersect "Set abstraction mismatch ~a ~a" s₀ s₁)]))

  (define (a/set-binary-subtract s₀ s₁ store-spaces μ)

    (define (sub in-set? container S₀ S₁)
      (define-values (S* weakly)
        (for/fold ([S* S₀] [weakly '()]) ([v (in-set S₁)])
          (match (in-set? S* v store-spaces μ)
            [#t (values (set-remove S* v) weakly)]
            [#f (values S* weakly)]
            ['b.⊤ (values S* (cons v weakly))])))
      (define unwrapped-sets
        (for*/fold ([sets (set S*)]) ([v (in-list weakly)]
                                      [S (in-set sets)])
          (set-add sets (set-remove S v))))
      (Abs-Data (for/set ([S (in-set unwrapped-sets)]) (container S))))
    
    (match* (s₀ s₁)
      [((? set? S₀) (? set? S₁)) (set-subtract S₀ S₁)]
      
      [((discrete-set S₀) (discrete-set S₁))
       (sub discrete-in-set? discrete-set S₀ S₁)]
  
      [((abstract-set S₀) (abstract-set S₁))
       (sub abstract-in-set? abstract-set S₀ S₁)]
      [(_ _) (error 'a/set-binary-subtract "Set abstraction mismatch ~a ~a" s₀ s₁)]))
  )

