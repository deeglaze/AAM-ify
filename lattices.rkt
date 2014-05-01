#lang racket/base

(require (for-syntax syntax/for-body racket/base)
         racket/match racket/set "spaces.rkt" "shared.rkt")
(provide ;; Abstract counting algebra
         μ+ μmax μ⊔ c+ cmax c⊑ ∣γ∣>1
         ;; Ternary logic algebra
         b∨ b∧ b¬ b⊔ ⦃b⦄ q∧
         for/b⊔ for*/b⊔
         for/b∧ for*/b∧
         for/b∨ for*/b∨
         ;; Ternary wrappers
         (struct-out May)
         (struct-out Must)
         ;; answers
         to-data in-data
         answer⊥ answer-⊔ answer-⊔1 result-⊔
)

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

;; general cardinality analysis based on abstract counting info
(define (∣γ∣>1 v μ)
  (let aliased? ([v v])
    (match v
      [(variant var data)
       (for/or ([d (in-vector data)]) (aliased? d))]
      ;; INVARIANT/ASSUMPTION: abstract-ffuns do not have distinct keys that are a/equal?=#t
      [(or (abstract-ffun map) (discrete-ffun map))
       (for/or ([(k v) (in-hash map)])
         (or (aliased? k) (aliased? v)))]
      ;; keys trusted
      [(? hash? map) (for/or ([v (in-hash-values map)]) (aliased? v))]
      ;; FIXME?: Is it right to not dereference Address-Structural? It's of course safe.
      [(or (Address-Structural _ a) (Address-Egal _ a))
       (eq? (hash-ref μ a 0) 'ω)]
      [(? set? vs) #f] ;; trusted concrete
      [(or (abstract-set S) (discrete-set S))
       (for/or ([v (in-set S)]) (aliased? v))]
      [(external (External-Space _ card _ _) ev)
       (eq? (card ev μ) 'ω)]
      [atom #f])))

;; Ternary logic in the Kleene sense.
(define ⦃t⦄ (set #t))
(define ⦃f⦄ (set #f))
(define ⦃b.⊤⦄ (set #t #f))
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

;;; Abstract results
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
  [((Abs-Result/effect certain?₀ v₀ σ₀ μ₀)
    (Abs-Result/effect certain?₁ v₁ σ₁ μ₁))
   (Abs-Result/effect (and certain?₀ certain?₁) (term-⊔ v₀ v₁)
                      (store-space-⊔ σ₀ σ₁) (μ⊔ μ₀ μ₁))])

;; TODO?: Plug in custom ⊔ here.
(define (store-space-⊔ σ₀ σ₁)
  (if (eq? σ₀ σ₁)
      σ₀
      (for/fold ([σ σ₀]) ([(space store) (in-hash σ₁)])
        (hash-set σ space (hash-join store (hash-ref σ₀ space #hash()))))))
