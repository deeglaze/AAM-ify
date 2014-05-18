#lang racket/base
(require racket/unit)
(provide language-parms^
         language-impl^
         matching-equality^
         abstract-set-ops^
         abstract-map-ops^
         )
(define-signature language-parms^
  (L ;; Language
   alloc ;; State Map[Symbol,DPattern] [Any] → Any
   Ξ ;; Map[Symbol,Meta-function]
   trace-update
   R))

;; A Store-Space is a Map[Address-Space-Name,Map[Any,DPattern]]
;; An Abs-Count is a Map[Any,Card]
(define-signature language-impl^
  (expression-eval ;; [Abs-]State Expression Store-Space [Abs-Count] → Set[[Abs-]Result/effect]
   rule-eval ;; Rule Store-Space [Abs-]State → Set[[Abs-]State]
   mf-eval ;; [Abs-]State Store-Space Meta-function DPattern [Abs-Count] → Set[[Abs-]Result/effect]
   ))

(define-signature matching-equality^
  (a/match a/equal?))

(define-signature abstract-set-ops^
  (discrete-set-remove
   abstract-set-remove
   a/set-remove
   abstract-in-set?
   discrete-in-set?
   a/set-binary-intersect
   a/set-binary-subtract))

(define-signature abstract-map-ops^
  (discrete-map-remove
   abstract-map-remove
   abstract-map-extend
   a/map-remove))
