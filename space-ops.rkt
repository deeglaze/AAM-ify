#lang racket/base
(require racket/match racket/set racket/fixnum
         racket/trace
         "spaces.rkt" "lattices.rkt")
(provide combine
         set-union/Δ set-add/Δ
         add-⊤ flat-card flat-⊔ flat-≡ flat-quine
         add-℘ set-card external-set-⊔ user-set-⊔ set-≡ set-quine
         in-external-set in-user-set
         mk-user-set user-set?)

(define-custom-set-types external-set equal?)

(define (combine . es)
  (let recur ([es es])
    (match es
      ['() pure]
      [(cons e es)
       (fxior (match e
                [(or (expression si _)
                     (BSCS si _)
                     (Meta-function _ _ si _ _)
                     (Rule _ _ _ (BSCS si _) _ _)) si]
                [(? fixnum?) e]
                [else (error 'combine "Expected value with store-interaction or fixnum ~a" e)])
              (recur es))])))

(define (add-⊤ pred) (λ (v) (or (eq? v -⊤) (pred v))))
(define (add-℘ pred) (λ (v) (or (external-set? v) ;; INVARIANT: only values satisfying pred in set
                                (pred v))))
(define (flat-card v) (if (eq? v -⊤) 'ω 1))
(define (flat-⊔ ev₀ ev₁) (if (equal? ev₀ ev₁) (values ev₀ #f) (values -⊤ #t)))
(define (flat-≡ ev₀ ev₁) (if (or (eq? ev₀ -⊤) (eq? ev₁ -⊤))
                             'b.⊤
                             (equal? ev₀ ev₁)))
(define (flat-quine v) (if (eq? v -⊤) #'-⊤ #`'#,v))
(define (set-quine v)
  (if (external-set? v)
      #`(make-immutable-external-set
         (list . #,(for/list ([x (in-set v)]) #`'#,x)))
      #`'#,v))
(define (in-X-set X)
  (λ (v) (if (X v) (in-set v) (in-value v))))
(define in-external-set (in-X-set external-set?))
(define in-user-set (in-X-set user-set?))


(define (set-card v)
  (match (set-count v)
    [(and (or 1 0) n̂) n̂]
    [_ 'ω]))

(define ((set-⊔ pred mk) s₀ s₁)
  (if (pred s₀)
      (cond [(pred s₁) (set-union/Δ s₀ s₁)]
            [else (set-add/Δ s₀ s₁)])
      (cond [(pred s₁)
             (if (and (= (set-count s₁) 1)
                      (equal? s₀ (set-first s₁)))
                 (values s₁ #f)
                 (values (set-add s₁ s₀) #t))]
            [else (values (mk (list s₀ s₁)) #t)])))
(define external-set-⊔ (set-⊔ external-set? make-immutable-external-set))
(define user-set-⊔ (set-⊔ user-set? make-immutable-user-set))

;; This is the set interpretation of values, so they are only equal if they are singleton sets.
;; They are may-equal if they have any elements in common.
(define (set-≡ s₀ s₁)
  (cond [(and (= (set-count s₀) 1) (equal? s₀ s₁)) #t]
        [(set-empty? (set-intersect s₀ s₁)) #f]
        [else 'b.⊤]))

(define (set-union/Δ S₀ S₁)
  (cond
   [(eq? S₀ S₁) (values S₀ #f)]
   [else (define S* (set-union S₀ S₁))
         (values S* (not (fx= (set-count S*) (set-count S₀))))]))

(define (set-add/Δ S v)
  (define S* (set-add S v))
  (values S* (not (fx= (set-count S*) (set-count S)))))
