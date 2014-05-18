#lang racket/base

(require (for-syntax syntax/for-body racket/base)
         racket/match racket/set
         "spaces.rkt"
         "shared.rkt")
(provide ;; Abstract counting algebra
         μ+ μmax μ⊔ c+ cmax c⊑ ∣γ∣>1 μ⊔/Δ
         ;; Precision classifier algebra
         pc⊔ for/pc⊔ for*/pc⊔
         ;; Ternary logic algebra
         b∨ b∧ b¬ b⊔ ⦃b⦄ q∧ absb.⊤
         for/b⊔ for*/b⊔
         for/b∧ for*/b∧
         for/b∨ for*/b∨
         ;; Ternary wrappers
         (struct-out May)
         (struct-out Must))

;; The abstract counting algebra is ≤, + and max in ℕ compactified to {0,1,ω}

(define/match (c+ c₀ c₁)
  [(0 c) c]
  [(c 0) c]
  [(_ _) 'ω])

(define/match (cmax c₀ c₁)
  [((not 'ω) c) c]
  [(c (not 'ω)) c]
  [(_ _) 'ω])

(define/match (c⊑ c₀ c₁)
  [(c c) #t]
  [(0 c) #t]
  [(1 'ω) #t]
  [(_ _) #f])

(define (μ+ μ a c) (hash-set μ a (c+ c (hash-ref μ a 0))))
(define (μmax μ a c) (hash-set μ a (cmax c (hash-ref μ a 0))))
(define (μ⊔ μ₀ μ₁) (for/fold ([μ μ₀]) ([(a c) (in-hash μ₁)]) (μmax μ a c)))

(define (μmax/Δ μ a c)
  (define old (hash-ref μ a 0))
  (define c* (cmax c old))
  (values (hash-set μ a c*) (not (eq? c* old))))
(define (μ⊔/Δ μ₀ μ₁)
  (for/fold ([μ μ₀] [Δ? #f])
      ([(a c) (in-hash μ₁)])
    (define-values (μ* Δ?*) (μmax/Δ μ a c))
    (values μ* (or Δ? Δ?*))))

;; general cardinality analysis based on abstract counting info
(define (∣γ∣>1 v μ)
  (let aliased? ([v v])
    (match v
      [(variant var data)
       (for/or ([d (in-vector data)]) (aliased? d))]
      ;; INVARIANT/ASSUMPTION: abstract-ffuns do not have distinct keys that are a/equal?=#t
      [(ffun (Map _ _ kcomp _) map)
       (case (Component-pc kcomp)
         [(abstract discrete)
          (for/or ([(k v) (in-hash map)])
            (or (aliased? k) (aliased? v)))]
         [(concrete)
          (for/or ([v (in-hash-values map)]) (aliased? v))])]
      ;; FIXME?: Is it right to not dereference Address 'Deref? It's of course safe.
      [(Address _ a _ _)
       (eq? (hash-ref μ a 0) 'ω)]
      [(fset scomp vs)
       (case (Component-pc scomp)
         [(concrete) #f]
         [(abstract discrete)
          (for/or ([v (in-set vs)]) (aliased? v))])]
      [(Abs-Data Eh S)
       (or (for/or ([v (in-hash-values Eh)]) (aliased? v))
           (if (user-set? S)
               (for/or ([v (in-set S)]) (aliased? v))
               (aliased? S)))]
      [(external (? External-Space? E) ev)
       (define card (External-Space-cardinality E))
       (unless card
         (error '∣γ∣>1 "Partially specified spaces requires a cardinality analysis ~a" E))
       (eq? (card ev μ) 'ω)]
      [atom #f])))

(define/match (pc⊔ pc₀ pc₁)
  [(_ 'abstract) 'abstract]
  [('abstract _) 'abstract]
  [('discrete _) 'discrete]
  [(_ 'discrete) 'discrete]
  [('concrete 'concrete) 'concrete])

;; Ternary logic in the Kleene sense.
(define ⦃t⦄ (mk-user-set #t))
(define ⦃f⦄ (mk-user-set #f))
(define ⦃b.⊤⦄ (mk-user-set #t #f))
(define/match (⦃b⦄ b)
  [(#t) ⦃t⦄]
  [(#f) ⦃f⦄]
  [('b.⊤) ⦃b.⊤⦄]
  [(_) (error '⦃b⦄ "Bad boolean♯ ~a" b)])

(define-syntax-rule (b∨ b₀ b₁)
  (let ([no-dup (λ () b₁)])
    (match b₀
      [#t #t]
      [#f (no-dup)]
      ['b.⊤ (or (no-dup) 'b.⊤)]
      [_ (error 'b∨ "Bad boolean♯ ~a" b₀)])))

(define-syntax-rule (b∧ b₀ b₁)
  (let ([no-dup (λ () b₁)])
   (match b₀
     [#t (no-dup)]
     [#f #f]
     ['b.⊤ (and (no-dup) 'b.⊤)]
     [_ (error 'b∧ "Bad boolean♯ ~a" b₀)])))

;; When b is not 'b.⊤, the certainty is unchanged.
(define (q∧ q b)
  (and (boolean? b) q))

(define absb.⊤ (Abs-Data ρ₀ (⦃b⦄ 'b.⊤)))
(define (b¬ b) (if (eq? b 'b.⊤) 'b.⊤ (not b)))

;; 'b.⊤ if different, except if b₀ is -unmapped, in which case we get b₁
(define (b⊔ b₀ b₁)
  (cond [(eq? b₀ -unmapped) b₁]
        [(eq? b₀ b₁) b₁]
        [else 'b.⊤]))

;; We need a qualifier for successful matches to know if we need to continue
;; trying to match for a meta-function.
(struct May (dpat) #:transparent)
(struct Must (dpat) #:transparent)

;; Produce versions of for[*]/and for[*]/or etc for the binary operations:

(define-syntax-rule (define-for/b-op name folder start op bval short-circuit)
  (...
   (define-syntax (name stx)
     (syntax-case stx ()
       [(_ guards body ...)
        (with-syntax ([((pre-body ...) (post-body ...)) (split-for-body stx #'(body ...))])
          (syntax/loc stx
            (folder ([acc start]) guards
              pre-body ...
              (define bval (op acc (let () post-body ...)))
              #:break short-circuit
              bval)))]))))

 ;; short-circuit on #f
(define-for/b-op for/b∧ for/fold #t b∧ bval (not bval))
(define-for/b-op for*/b∧ for*/fold #t b∧ bval (not bval))
;; short-circuit on 'b.⊤
(define-for/b-op for/b⊔ for/fold -unmapped b⊔ bval (eq? bval 'b.⊤))
(define-for/b-op for*/b⊔ for*/fold -unmapped b⊔ bval (eq? bval 'b.⊤))
;; short-circuit on #t
(define-for/b-op for/b∨ for/fold #f b∨ bval (eq? bval #t))
(define-for/b-op for*/b∨ for*/fold #f b∨ bval (eq? bval #t))
;; short-circuit on 'abstract
(define-for/b-op for/pc⊔ for/fold 'concrete pc⊔ bval (eq? bval 'abstract))
(define-for/b-op for*/pc⊔ for*/fold 'concrete pc⊔ bval (eq? bval 'abstract))
