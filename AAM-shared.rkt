#lang racket/base

#|
Utility functions and specific functions that are shared between concrete and abstract AAM
|#

(require racket/match racket/set racket/dict "AAM-spaces.rkt")
(provide unbound-map-error
         pattern-eval
         in-space?
         hash-join
         hash-add
         hash-union
         for/union
         for*/union
         set-add*
         list-of-sets→set-of-lists
         sexp-to-dpattern/check)

(define (unbound-map-error who m) (λ () (error who "Map unbound ~a" m)))

;; pattern-eval : Pattern Map[Symbol,DPattern] → DPattern
;; Concretize a pattern given an environment of bindings.
(define (pattern-eval pat ρ)
  (match pat
    [(Rvar x) (hash-ref ρ x (λ () (error 'pattern-eval "Unbound pattern variable ~a" x)))]
    [(Variant name pats) (Variant name (map (λ (pat) (pattern-eval pat ρ)) pats))]
    [(Bvar _ _) (error 'pattern-eval "Cannot eval a binding pattern ~a" pat)]
    [atom atom]))

;; in-space? : DPattern Language Space-name → Boolean
;; Decide whether a DPattern d is in Space space-name, which is defined in Language L.
(define (in-space? d L space-name)
  (match-define (Language _ spaces) L)
  (define (in-space? space-name d)
    (define space
      (hash-ref spaces space-name (λ () (error 'in-space? "Undefined space ~a in language ~a"
                                          space-name
                                          (Language-name L)))))
    (match space
      [(User-Space variants-or-components _)
       (for/or ([var (in-list variants-or-components)])
         (cond [(Variant? var) (in-variant? var d)]
               [(Space-reference? var) (in-space? (Space-reference-name var) d)]
               [else (in-component? var d)]))]
      [(Address-Space) (Address? d)]
      [(External-Space pred _ _) (pred d)]
      [_ (error 'in-space? "Bad space ~a" space)]))

  (define (in-component? comp d)
    (match comp
      [(Space-reference name) (in-space? name d)]
      [(Map domain range)
       (and (dict? d)
            (for/and ([(k v) (in-dict d)])
              (and (in-component? domain k)
                   (in-component? range v))))]
      [(℘ comp)
       (and (set? d)
            (for/and ([v (in-set d)]) (in-component? comp v)))]
      [(Address-Space) #t]
      [_ (error 'in-component? "Bad component ~a" comp)]))

  (define (in-variant? var d)
    (match-define (Variant name comps) var)
    (match d
      [(Variant (== name eq?) ds)
       (let check-comps ([comps comps] [ds ds])
         (match* (comps ds)
           [((cons comp comps) (cons d ds))
            (and (in-component? comp d)
                 (check-comps comps ds))]
           [('() '()) #t]
           [(_ _) #f]))]
      [_ #f]))

  (in-space? space-name d))

;; sexp-to-dpattern/check : S-exp Space-name Language → DPattern
;; A minor parser from sexp to internal representation.
;; Any head-position constructor is considered a variant.
;; Ensure all variants exist in L.
(define (sexp-to-dpattern/check sexp expected-space-name L)
  (match-define (Language name spaces) L)
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
      [(Space-reference name) (space-to-dpat name sexp)]))

  (define (space-to-dpat space-name sexp)
    (define space
      (dict-ref spaces space-name
                (λ () (error 'sexp-to-dpattern/check
                             "Expected space undefined ~a" space-name))))
    (match space
      [(Address-Space) (Address sexp)] ;; An address may take any form.
      [(External-Space pred _ _) (and (pred sexp) sexp)]
      [(User-Space variants-or-components _)
       (match sexp
         [`(,(? symbol? head) . ,rest)
          (let/ec break
            (define var
              (for/or ([v (in-list variants-or-components)])
                (cond [(Variant? v)
                       (and (eq? head (Variant-name v))
                            v)]
                      [(Space-reference? v)
                       (with-handlers ([exn? (λ (e) #f)])
                         (break (space-to-dpat (Space-reference-name v) sexp)))]
                      [else
                       (with-handlers ([exn? (λ (e) #f)])
                         (break (component-sexp-to-dpat v sexp)))])))
            (unless var (error 'sexp-to-dpattern/check
                               "Expected one of these variants ~a given ~a" variants-or-components sexp))
            (define parsed-rest
              (let do-stuff ([comps (Variant-Components var)] [lst rest])
                (match* (comps lst)
                  [((cons comp comps) (cons sexp sexps))
                   (cons (component-sexp-to-dpat comp sexp)
                         (do-stuff comps sexps))]
                  [('() '()) '()]
                  [(_ _)
                   (error 'to-dpat "Variant components have arity mismatch. Given ~a expected ~a"
                          rest (Variant-Components var))])))
            (Variant head parsed-rest))]
         [_ (error 'to-dpat "Expected a variant constructor in head position ~a" sexp)])]))
  (space-to-dpat expected-space-name sexp))

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