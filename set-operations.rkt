#lang racket/base
(require racket/unit "spaces.rkt" "signatures.rkt" "lattices.rkt"
         "shared.rkt"
         racket/bool
         racket/match racket/set)
(provide abstract-set-ops@)

(define-unit abstract-set-ops@
  (import language-parms^ matching-equality^)
  (export abstract-set-ops^)
  
  (define (discrete-set-remove container s S v store-spaces μ)
    (cond
     [(set-member? S v)
      (define s* (container (set-remove S v)))
      (if (∣γ∣>1 v μ)
          (Abs-Data ρ₀ (mk-user-set s s*))
          s*)]
     [else s]))

  (define (abstract-set-remove container s S v store-spaces μ)
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
      [#t (container S*)]
      [#f s]
      ['b.⊤
       (define unwrapped-sets
         (for*/fold ([Ss (set S*)]) ([v (in-list weakly)]
                                     [S (in-set Ss)])
           (set-add Ss (set-remove S v))))
       (Abs-Data ρ₀ (for/fold ([AS (mk-user-set)])
                        ([S (in-set unwrapped-sets)])
                      (set-add AS (container S))))]))

  (define (a/set-remove s v store-spaces μ)
    (match-define (fset vcomp S) s)
    (define (container S) (fset vcomp S))
    (case (Component-pc vcomp)
      [(concrete) (container (set-remove S v))]
      [(discrete) (discrete-set-remove container s S v store-spaces μ)]
      [(abstract) (abstract-set-remove container s S v store-spaces μ)]))


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
      (Abs-Data ρ₀ (for/fold ([AS (mk-user-set)])
                       ([S (in-set unwrapped-sets)])
                     (set-add AS (container S)))))

    (match-define (fset vcomp₀ S₀) s₀)
    (match-define (fset vcomp₁ S₁) s₁)
    (unless (equal? vcomp₀ vcomp₁)
      (error 'a/set-binary-intersect "Set space mismatch ~a ~a" s₀ s₁))
    (define (container S) (fset vcomp₀ S))
    (case (Component-pc vcomp₀)
      [(concrete) (container (set-intersect S₀ S₁))]
      [(discrete) (inter discrete-in-set? container S₀ S₁)]  
      [(abstract) (inter abstract-in-set? container S₀ S₁)]))

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
      (Abs-Data ρ₀ (for/fold ([AS (mk-user-set)])
                       ([S (in-set unwrapped-sets)])
                     (set-add AS (container S)))))
    
    (match-define (fset vcomp₀ S₀) s₀)
    (match-define (fset vcomp₁ S₁) s₁)
    (unless (equal? vcomp₀ vcomp₁)
      (error 'a/set-binary-subtract "Set space mismatch ~a ~a" s₀ s₁))
    (define (container S) (fset vcomp₀ S))
    (case (Component-pc vcomp₀)
      [(concrete) (container (set-subtract S₀ S₁))]
      [(discrete) (sub discrete-in-set? container S₀ S₁)]
      [(abstract) (sub abstract-in-set? container S₀ S₁)])))

