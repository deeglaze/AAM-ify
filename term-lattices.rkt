#lang racket/base
(require racket/match racket/set racket/fixnum racket/sequence
         "spaces.rkt" "lattices.rkt" "space-ops.rkt"
         "shared.rkt")
(provide ;; answers
         to-data in-data
         answer⊥ answer-⊔ answer-⊔1 result-⊔
         ;; sets of values and maps
         store-add store-set ffun-strong-update ffun-weak-update
         ;; run with widening
         apply-reduction-relation*/∇)

;; NOTE: The Δ functions follow the convention that the left value is "old" and
;; the right value is "new", so it suffices to compare the output to the old value.
(define (E-⊔/Δ E ev₀ v₁)
  (define ⊔/Δ (External-Space-⊔ E))
  (cond
   [⊔/Δ
    (define-values (v* Δ?)
      (⊔/Δ ev₀ (external-v v₁)))
    (values (external E v*) Δ?)]
   [else
    (error 'E-⊔/Δ "Partially specified space require a quine ~a" E)]))
(define (E-⊔ E ev₀ v₁)
  (define-values (v* Δ?) (E-⊔/Δ E ev₀ v₁))
  v*)

(define (Eh-⊔ Eh E v)
  (match (hash-ref Eh E -unmapped)
    [(== -unmapped eq?)
     (hash-set Eh E v)]
    [(external _ ev₀)
     (define-values (v* Δ?*) (E-⊔/Δ E ev₀ v))
     (hash-set Eh E v*)]
    [other (error 'Eh-⊔ "INTERNAL: should not store non-external values ~a" other)]))

(define (Eh-⊔/Δ Eh E v Δ-already?)
  (match (hash-ref Eh E -unmapped)
    [(== -unmapped eq?)
     (values (hash-set Eh E v) #t)]
    [(external _ ev₀)
     (define-values (v* Δ?*) (E-⊔/Δ E ev₀ v))
     (values (hash-set Eh E v*) (or Δ-already? Δ?*))]
    [other (error 'Eh-⊔/Δ "INTERNAL: should not store non-external values ~a" other)]))

;; INVARIANT: if v external, the space is not E.
(define (eadd E ev v)
  (match v
    [(external E* _) (Abs-Data (hash E ev E* v) u∅)]
    [_ (Abs-Data (hash E ev) (mk-user-set v))]))

;;; Abstract results
(define (term-⊔/Δ v₀ v₁)
  (match* (v₀ v₁)
    [(v v) (values v #f)]
    [((Abs-Data Eh₀ payload₀) (Abs-Data Eh₁ payload₁))
     (define-values (Eh* Δ?)
       (for/fold ([Eh* Eh₀] [Δ? #f]) ([(E ev₁) (in-hash Eh₁)])
         (Eh-⊔/Δ Eh* E ev₁ Δ?)))
     (define-values (payload* Δ?*) (user-set-⊔ payload₀ payload₁))
     (values (Abs-Data Eh* payload*) (or Δ? Δ?*))]
    [((Abs-Data Eh payload) v)
     (match v
       [(external E _)
        (define-values (Eh* Δ?) (Eh-⊔/Δ Eh E v #f))
        (if Δ?
            (values (Abs-Data Eh* payload) #t)
            (values v₀ #f))]
       [_ (define-values (payload* Δ?) (user-set-⊔ payload v))
          (if Δ?
              (values (Abs-Data Eh payload*) #t)
              (values v₀ #f))])]
    ;; Not symmetric to above case because of Δ convention.
    [(v (Abs-Data Eh payload))
     (match v
       [(external E ev)
        (cond
         ;; Make sure that v₁ isn't just v wrapped.
         [(and (set-empty? payload)
               (eq? 1 (hash-count Eh))
               (equal? v (hash-ref Eh E)))
          (values v₁ #f)]
         ;; It isn't, so join. We know it's different.
         [else
          (define-values (Eh* Δ?) (Eh-⊔/Δ Eh E v #t))
          (values (Abs-Data Eh* payload) #t)])]
       [v (cond
           ;; Another wrap check.
           [(and (equal? Eh ρ₀)
                 (= (set-count payload) 1)
                 (equal? (set-first payload) v))
            (values v₁ #f)]
           [else
            (define-values (payload* dummy) (user-set-⊔ payload v))
            (values (Abs-Data Eh payload*) #t)])])]
    [((external E ev₀) (external E _)) (E-⊔/Δ E ev₀ v₁)]
    [((external E _) v) (values (eadd E v₀ v) #t)]
    [(v (external E _)) (values (eadd E v₁ v) #t)]
    [(_ _) (values (Abs-Data ρ₀ (mk-user-set v₀ v₁)) #t)]))

(define (term-⊔ v₀ v₁)
  (define (addv Eh payload v)
    (match v
      [(external E _)
       (Abs-Data (Eh-⊔ Eh E v) payload)]
      [_
       (define-values (payload* dummy) (user-set-⊔ payload v))
       (Abs-Data Eh payload*)]))
  (match* (v₀ v₁)
    [(v v) v]
    [((Abs-Data Eh₀ payload₀) (Abs-Data Eh₁ payload₁))
     (define Eh*
       (for/fold ([Eh* Eh₀]) ([(E ev₁) (in-hash Eh₁)])
         (Eh-⊔ Eh* E ev₁)))
     (define-values (payload* dummy) (user-set-⊔ payload₀ payload₁))
     (Abs-Data Eh* payload*)]
    [((Abs-Data Eh payload) v) (addv Eh payload v)]
    [(v (Abs-Data Eh payload)) (addv Eh payload v)]
    [((external E ev₀) (external E _))
     (E-⊔ E ev₀ v₁)]
    [((external E _) v) (eadd E v₀ v)]
    [(v (external E _)) (eadd E v₁ v)]
    [(_ _) (Abs-Data ρ₀ (mk-user-set v₀ v₁))]))

(define (in-external-hash Eh)
  (define (gen-outer box pos)
    (define-values (E ev) ((vector-ref pos 3)))
    (define enum (External-Space-enum E))
    (unless enum
      (error 'in-external-hash
             "Partially specified space requires an enumerator ~a" E))
    (define-values (? !) (sequence-generate (enum ev)))
    (cond
     [(?)
      (vector-set! pos 0 ?)
      (vector-set! pos 1 !)
      (set-box! box (!))
      pos]
     [else #f]))
  (make-do-sequence
   (λ ()
      (define last-value (box -unmapped))
      (values (λ (pos) (unbox last-value))
              (λ (pos)
                 (cond
                  [((vector-ref pos 0))
                   (set-box! last-value ((vector-ref pos 1)))
                   pos]
                  [((vector-ref pos 2)) (gen-outer last-value pos)]
                  [else #f]))
              (let-values ([(? !) (sequence-generate (in-hash Eh))])
                (and (?) (gen-outer last-value (vector #f #f ? !))))
              values #f #f))))

(define (in-data v)
  (match v
    [(Abs-Data Eh S) (sequence-append (in-external-hash Eh) (in-set S))]
    [singleton (in-value singleton)]))

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

(define (hash-⊔1 h k v)
  (match (hash-ref h k -unmapped)
    [(== -unmapped eq?) (hash-set h k v)]
    [old (hash-set h k (term-⊔ old v))]))

(define (hash-⊔1/Δ h k v)
  (match (hash-ref h k -unmapped)
    [(== -unmapped eq?) (values (hash-set h k v) #t)]
    [old (define-values (v* Δ?) (term-⊔/Δ old v))
         (values (hash-set h k v*) Δ?)]))

(define (hash-⊔/Δ h₀ h₁)
  (for/fold ([h h₀] [Δ? #f]) ([(k v) (in-hash h₁)])
    (define-values (h* Δ?*) (hash-⊔1/Δ h k v))
    (values h* (or Δ? Δ?*))))

(define (hash-⊔ h₀ h₁)
  (for/fold ([h h₀]) ([(k v) (in-hash h₁)])
    (hash-⊔1 h k v)))

(define store-add (store-op 'store-add hash-⊔1))

(define (ffun-strong-update m k v)
  (match-define (ffun mcomp map) m)
  (ffun mcomp (hash-set map k v)))


(define (ffun-weak-update m k v)
  (match-define (ffun mcomp map) m)
  (ffun mcomp (hash-⊔1 map k v)))

(define (store-space-⊔/Δ σ₀ σ₁)
  (if (eq? σ₀ σ₁)
      (values σ₀ #f)
      (for/fold ([σ σ₀] [Δ? #f]) ([(space store) (in-hash σ₁)])
        (define-values (store* Δ?*) (hash-⊔/Δ store (hash-ref σ₀ space #hash())))
        (values (hash-set σ space store*) (or Δ? Δ?*)))))

(define (store-space-⊔ σ₀ σ₁)
  (if (eq? σ₀ σ₁)
      σ₀
      (for/fold ([σ σ₀]) ([(space store) (in-hash σ₁)])
        (hash-⊔ store (hash-ref σ₀ space #hash())))))

(define/match (abs-state-⊔ s₀ s₁)
  [((Abs-State t₀ σ₀ μ₀ τ̂₀) (Abs-State t₁ σ₁ μ₁ τ̂₁))
   (unless (and (equal? t₀ t₁) (equal? τ̂₀ τ̂₁))
     (error 'abs-state-⊔ "Expected same term and trace abstraction, got ~a ~a" s₀ s₁))
   (define-values (σ* Δ?) (store-space-⊔/Δ σ₀ σ₁))
   (define-values (μ* Δ?*) (μ⊔/Δ μ₀ μ₁))
   (values (Abs-State t₀ σ* (μ⊔ μ₀ μ₁) τ̂₀) (or Δ? Δ?*))])

(define (apply-reduction-relation*/∇ rule-eval R [∇ abs-state-⊔])
  (define reduce (apply-reduction-relation rule-eval R))
  (λ (term)
     (define seen (make-hash))
     (define (seen-add! s)
       (define τ̂ (Abs-State-τ̂ s))
       (match (hash-ref seen τ̂ -unmapped)
         [(== -unmapped eq?)
          (hash-set! seen τ̂ s)
          s]
         [s-old
          (define-values (s* changed?) (∇ s s-old))
          (cond [changed?
                 (hash-set! seen τ̂ s*)
                 s*]
                [else #f])]))
     (let fix ([term term])
       (for* ([term* (in-set (reduce term))]
              [term♯ (in-value (seen-add! term*))]
              #:when term♯)
         (fix term♯)))
     seen))
