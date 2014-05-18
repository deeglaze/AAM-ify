#lang racket/base
(require racket/unit "spaces.rkt" "signatures.rkt" "lattices.rkt"
         racket/match racket/set)
(provide abstract-map-ops@)

(define-unit abstract-map-ops@
  (import language-parms^ matching-equality^)
  (export abstract-map-ops^)

  (define ((abstract-map-extend mcomp map setter) store-spaces μ certain? k v)
    ;; TODO: This explosion of nastiness is begging for a plug-in widening.
    ;; this may be the form of abstract-ffun having an (optional) extra function
    ;; that takes 〈map,trust-strong?, ks, vs, store-spaces, μ〉 and produces a set of maps
    ;; such that there is a galois connection between that set and the set this fallback produces.

    ;; Build two sets for keys that are strongly present or weakly (possibly) present.
    ;; Strongly present keys are in all possible maps. The rest have an exponential blowup.
    ;; OPT: we cut out the intermediate step and build the base map with strongly present keys.
    (define-values (base-map weakly)
      (for*/fold ([base-map map] [weakly '()]) ([k* (in-hash-keys map)])
        (match (a/equal? k k* store-spaces μ)
          [#t (values (setter base-map v) weakly)]
          [#f (values base-map weakly)]
          ['b.⊤ (values base-map (cons k* weakly))])))
    ;; Each key adds to possible maps
  
    (Abs-Result/effect certain?
                       (Abs-Data
                        ρ₀
                        (for*/fold ([maps (mk-user-set base-map)])
                            ([k* (in-list weakly)]
                             [map (in-set maps)])
                          (set-add maps (setter map k* v))))
                       store-spaces μ))

  (define (abstract-map-remove container m map k store-spaces μ)
    ;; remove every combination of values that match weakly.
    ;; always remove value if strongly matches.
    (define-values (map* weakly found?)
      (for/fold ([map* map] [weakly '()] [found? #f])
          ([k* (in-hash-keys map)])
        (match (a/equal? k k* store-spaces μ)
          [#t (values (hash-remove map* k*) weakly (b⊔ found? #t))]
          [#f (values map* weakly found?)]
          ['b.⊤ (values map* (cons k* weakly) 'b.⊤)])))
    (match found?
      [#t (container map*)]
      [#f m]
      ['b.⊤
       (define unwrapped-maps
         (for*/fold ([maps (set map*)]) ([k (in-list weakly)]
                                         [map (in-set maps)])
           (set-add maps (hash-remove map k))))
       (Abs-Data ρ₀ (for/fold ([S (mk-user-set)])
                        ([map (in-set unwrapped-maps)])
                      (set-add S (container map))))]))

  (define (discrete-map-remove container m map k store-spaces μ)
    (cond
     [(hash-has-key? map k)
      (define m* (container (hash-remove map k)))
      (if (∣γ∣>1 k μ)
          (Abs-Data ρ₀ (mk-user-set m m*))
          m*)]
     [else m]))

  (define (a/map-remove m k store-spaces μ)
    (match-define (ffun (and mcomp (Map _ _ kcomp _)) map) m)
    (define (container map) (ffun mcomp map))
    (case (Component-pc kcomp)
      [(concrete) (container (hash-remove map k))]
      [(discrete) (discrete-map-remove container m map k store-spaces μ)]
      [(abstract) (abstract-map-remove container m map k store-spaces μ)])))
