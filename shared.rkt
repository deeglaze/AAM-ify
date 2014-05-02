#lang racket/base

#|
Utility functions and specific functions that are shared between concrete and abstract AAM
|#

(require racket/match racket/set racket/dict "spaces.rkt"
         racket/unit
         (only-in math/number-theory binomial)
         racket/trace)
(provide unbound-map-error
         pattern-eval
         apply-reduction-relation
         apply-reduction-relation*
         apply-reduction-relation*/memo
         apply-reduction-relation*/∇
         store-ref store-set store-add weak-update-with-data strong-update-with-data
         in-space? in-variant? in-component?
         hash-join
         hash-add
         hash-union
         for/union
         for*/union
         set-add*
         list-of-sets→set-of-lists
         sexp-to-dpattern/check
         extract-set/container extract-map/container
         dpattern->sexp)

(define (unbound-map-error who m) (λ () (error who "Map unbound ~a" m)))

(define (extract-set/container v fail-msg)
  (match v
    [(? set? S) (values S values)]
    [(abstract-set S) (values S abstract-set)]
    [(discrete-set S) (values S discrete-set)]
    [other
     (when fail-msg
      (log-info (format fail-msg other)))
     (values #f #f)]))

(define (extract-map/container v fail-msg)
  (match v
    [(? hash? map) (values map values)]
    [(abstract-ffun map) (values map abstract-ffun)]
    [(discrete-ffun map) (values map discrete-ffun)]
    [other
     (when fail-msg
      (log-info (format fail-msg other)))
     (values #f #f)]))

;; pattern-eval : Pattern Map[Symbol,DPattern] → DPattern
;; Concretize a pattern given an environment of bindings.
(define (pattern-eval pat ρ)
  (match pat
    [(Rvar x) (hash-ref ρ x (λ () (error 'pattern-eval "Unbound pattern variable ~a" x)))]
    [(variant var pats) (variant var (for/vector #:length (vector-length pats)
                                                 ([pat (in-vector pats)])
                                          (pattern-eval pat ρ)))]
    [(or (? Name?) (? Space?) (? Map-with?) (? Set-with?))
     (error 'pattern-eval "Cannot eval a binding pattern ~a" pat)]
    [atom atom]))

(define ((apply-reduction-relation rule-eval rules) term)
  (for/union ([rule (in-list rules)]) (rule-eval rule term)))

(define (extend-indefinitely F x)
  (match (F x)
    [(? set-empty?) (set x)]
    [outs (for/union ([term* (in-set outs)]) (extend-indefinitely F term*))]))

(define (apply-reduction-relation* rule-eval rules)
  (define reduce (apply-reduction-relation rule-eval rules))
  (λ (term) (extend-indefinitely reduce term)))

(define (apply-reduction-relation*/memo rule-eval rules)
  (define reduce (apply-reduction-relation rule-eval rules))
  (λ (term)
     (define seen (mutable-set))
     (let fix ([term term])
       (cond
        [(set-member? seen term) ∅]
        [else
         (set-add! seen term)
         (match (reduce term)
           [(? set-empty?) (set term)]
           [outs (for/union ([term* (in-set outs)]) (fix term*))])]))))

(define (apply-reduction-relation*/∇ ⊔ rule-eval rules)
  (define reduce (apply-reduction-relation rule-eval rules))
  (λ (term)
     (define seen (make-hash))
     (define (seen-add! s)
       (define τ̂ (Abs-State-τ̂ s))
       (match (hash-ref seen τ̂ -unmapped)
         [(== -unmapped eq?)
          (hash-set! seen τ̂ s)
          s]
         [s-old
          (define-values (s* changed?) (⊔ s s-old))
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

;; in-space? : DPattern Language Space-name → Boolean
;; Decide whether a DPattern d is in Space space-name, which is defined in Language L.
(define (in-space-ref? L space-name d)
  (match-define (Language spaces _) L)
  (define space
    (hash-ref spaces space-name
              (λ () (error 'in-space? "Undefined space ~a"
                           space-name))))
  (in-space? L space d))

(define (in-variant? L var d)
  (match-define (Variant name comps _ _) var)
  (match d
    [(variant (Variant (== name) _ _ _) ds)
     ;; INVARIANT: variants with the same name have same length vectors.
     (for/and ([comp (in-vector comps)]
               [d (in-vector ds)])
       (in-component? L comp d))]
    [_ #f]))

(define (in-space? L space d)
  (match-define (Language spaces _) L)
  (match space
    [(User-Space variants-or-components _ _)
     (for/or ([var (in-list variants-or-components)])
       (cond [(Variant? var) (in-variant? L var d)]
             [(Space-reference? var) (in-space-ref? (Space-reference-name var) d)]
             [else (in-component? L var d)]))]
    [(Address-Space space)
     (match d
       [(or (Address-Structural (== space eq?) _)
            (Address-Egal (== space eq?) _)) #t]
       [_ #f])]
    ;; XXX: should external space predicates be allowed to return 'b.⊤?
    [(External-Space pred _ _ _)
     (match d
       [(external (== space) _) #t]
       [v (pred v)])]
    [_ (error 'in-space? "Bad space ~a" space)]))

(define (in-component? L comp d)
  (match comp
    [(Space-reference name) (in-space-ref? L name d)]
    [(Map domain range)
     (define (check-map d)
       (for/and ([(k v) (in-dict d)])
         (and (in-component? L domain k)
              (in-component? L range v))))
     (match d
       [(or (abstract-ffun m)
            (discrete-ffun m)
            (? dict? m)) (check-map m)]
       [_ #f])]
    [(℘ comp)
     (and (set? d)
          (for/and ([v (in-set d)]) (in-component? L comp v)))]
    [(? Address-Space?) #t]
    [_ (error 'in-component? "Bad component ~a" comp)]))

;; sexp-to-dpattern/check : S-exp Space-name Language → DPattern
;; A minor parser from sexp to internal representation.
;; Any head-position constructor is considered a variant.
;; Ensure all variants exist in L.
(define (sexp-to-dpattern/check sexp expected-space-name L)
  (match-define (Language spaces _) L)
  (define (component-sexp-to-dpat comp sexp)
    (match comp
      [(℘ comp)
       (unless (set? sexp)
         (error 'component-sexp-to-dpat "Expected a set of ~a given ~a" comp sexp))
       (for/set ([s (in-set sexp)])
         (component-sexp-to-dpat comp s))]
      [(Map domain range)
       (unless (dict? sexp)
         (error 'component-sexp-to-dpat "Expected a map from ~a to ~a given ~a" domain range sexp))
       (for/hash ([(k v) (in-dict sexp)])
         (values (component-sexp-to-dpat domain k)
                 (component-sexp-to-dpat range v)))]
      [(Space-reference name) (space-to-dpat name sexp)]
      [_ (error 'component-sexp-to-dpat "Bad component ~a" comp)]))

  (define (space-to-dpat space-name sexp)
    (define space
      (dict-ref spaces space-name
                (λ () (error 'sexp-to-dpattern/check
                             "Expected space undefined ~a" space-name))))
    (match space
      [(Address-Space space) (Address-Egal space sexp)] ;; An address may take any form.
      [(External-Space pred _ _ _) (and (pred sexp) sexp)]
      [(User-Space variants-or-components _ _)
       (match sexp
         [`(,(? symbol? head) . ,rest)
          (let/ec break
           (define var
             (for/or ([v (in-list variants-or-components)])
               (cond [(Variant? v)
                      (and (eq? head (Variant-name v))
                           v)]
                     [(Space-reference? v)
                      (with-handlers ([exn:fail? (λ (e) #f)])
                        (break (space-to-dpat (Space-reference-name v) sexp)))]
                     [else
                      (with-handlers ([exn:fail? (λ (e) #f)])
                        (break (component-sexp-to-dpat v sexp)))])))
           (unless (Variant? var)
             (error 'sexp-to-dpattern/check
                    "Expected one of these variants ~a given ~a" variants-or-components sexp))
           (define comps (Variant-Components var))
           (define len (vector-length comps))
           (unless (= len (length rest))
             (error 'to-dpat "Variant components have arity mismatch. Given ~a expected ~a"
                    rest (Variant-Components var)))
           (define parsed-rest
             (for/vector #:length len ([sexp (in-list rest)]
                                       [comp (in-vector comps)])
                         (component-sexp-to-dpat comp sexp)))
           (variant var parsed-rest))]
         [_ (error 'to-dpat "Expected a variant constructor in head position ~a" sexp)])]
      [_ (error 'space-to-dpat "Bad space ~a" space)]))
  (space-to-dpat expected-space-name sexp))

(define (dpattern->sexp d)
  (match d
    [(variant (Variant name _ _ _) ds)
     (cons name (for/list ([d (in-vector ds)]) (dpattern->sexp d)))]
    [(or (discrete-ffun d)
         (abstract-ffun d)
         (? dict? d))
     (cons 'make-hash
           (for/list ([(k v) (in-dict d)])
             (list (dpattern->sexp k) (dpattern->sexp v))))]
    [(external _ v) v]
    [atom atom]))

;; Utility functions
(define (set-add* s args)
  (for/fold ([s s]) ([arg (in-list args)]) (set-add s args)))

(define (list-of-sets→set-of-lists lst)
  (match lst
    [(cons s ss) (for*/set ([v (in-set s)]
                            [lst (in-set (list-of-sets→set-of-lists ss))])
                   (cons v lst))]
    ['() (set '())]))
(define-syntax-rule (for/union guard body ...)
  (for/fold ([acc ∅]) guard (set-union acc (let () body ...))))
(define-syntax-rule (for*/union guard body ...)
  (for*/fold ([acc ∅]) guard (set-union acc (let () body ...))))

(define (hash-join h k v) (hash-set h k (set-union (hash-ref h k ∅) v)))
(define (hash-add h k v) (hash-set h k (set-add (hash-ref h k ∅) v)))
(define (hash-union h₀ h₁)
  (for/fold ([h h₀]) ([(k vs) (in-hash h₁)]) (hash-join h k vs)))

(define (store-ref store-spaces k)
  (match k
    [(or (Address-Structural space addr)
         (Address-Egal space addr))
     (hash-ref (hash-ref store-spaces space #hash())
               addr
               (λ () (error 'store-ref "Unmapped address ~a" k)))]
    [_ (error 'store-ref "Bad address ~a" k)]))

(define (store-op who op)
  (λ (store-spaces k v)
     (match k
       [(or (Address-Structural space addr)
            (Address-Egal space addr))
        (hash-set store-spaces
                  space
                  (op (hash-ref store-spaces space #hash()) addr v))]
       [_ (error who "Bad address ~a" k)])))

(define (strong-update-with-data m k v)
  (match v
    [(Abs-Data S) (hash-set m k S)]
    [singleton (hash-set m k (set singleton))]))

(define (weak-update-with-data m k v)
  (match v
    [(Abs-Data S) (hash-join m k S)]
    [singleton (hash-add m k singleton)]))

(define store-set (store-op 'store-set strong-update-with-data))
(define store-add (store-op 'store-add weak-update-with-data))
