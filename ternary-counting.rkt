#lang racket/base

(require (for-syntax syntax/for-body racket/base)
         racket/match racket/set (only-in "spaces.rkt" -unmapped))
(provide ;; Abstract counting algebra
         μ+ μmax μ⊔ c+ cmax c⊑
         ;; Ternary logic algebra
         b∨ b∧ b¬ bδ ⦃b⦄
         for/bδ for*/bδ
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

(define (μ+ μ a c) (hash-set μ (c+ c (hash-ref μ a 0))))
(define (μmax μ a c) (hash-set μ (cmax c (hash-ref μ a 0))))
(define (μ⊔ μ₀ μ₁) (for/fold ([μ μ₀]) ([(a c) (in-hash μ₁)]) (μmax μ a c)))

;; Ternary logic in the Kleene sense.
(define ⦃t⦄ (set #t))
(define ⦃f⦄ (set #f))
(define ⦃b.⊤⦄ (set #t #f))
(define/match (⦃b⦄ b)
  [(#t) ⦃t⦄]
  [(#f) ⦃f⦄]
  [('b.⊤) ⦃b.⊤⦄])

(define-syntax-rule (b∨ b₀ b₁)
  (let ([no-dup (λ () b₁)])
    (match b₀
      [#t #t]
      [#f (no-dup)]
      ['b.⊤ (or (no-dup) 'b.⊤)])))

(define-syntax-rule (b∧ b₀ b₁)
  (let ([no-dup (λ () b₁)])
   (match b₀
     [#t (no-dup)]
     [#f #f]
     ['b.⊤ (and (no-dup) 'b.⊤)])))

(define (b¬ b) (if (eq? b 'b.⊤) 'b.⊤ (not b)))

;; 'b.⊤ if different, except if b₀ is -unmapped, in which case we get b₁
(define (bδ b₀ b₁)
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
(define-for/b-op for/bδ for/fold -unmapped bδ bval (eq? bval 'b.⊤))
(define-for/b-op for*/bδ for*/fold -unmapped bδ bval (eq? bval 'b.⊤))
;; short-circuit on #t
(define-for/b-op for/b∨ for/fold #f b∨ bval (eq? bval #t))
(define-for/b-op for*/b∨ for*/fold #f b∨ bval (eq? bval #t))
