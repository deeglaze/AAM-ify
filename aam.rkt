#lang racket/base
(require "parser.rkt" "shared.rkt" "spaces.rkt" "signatures.rkt"
         "transform.rkt"
         racket/unit
         (for-syntax racket/base))

(define-language CESK
  [BAddrs #:address-space bindings]
  [Variable #:external-space symbol? #:cardinality (λ (e) 1)]
  [Env (Variable → (Address-Space bindings))]
  [Expr (Ref Variable) (App Expr Expr) Pre-value #:trust-recursion]
  [Pre-value (Lam Variable Expr) #:trust-recursion]
  [With-env (Closure Expr Env)]
  [Value (Closure Pre-value Env)]
  #:refinement ([Closure (Value With-env)])
  [Frame (Ar Expr Env) (Fn Value)]
  [Kont (Mt) (Kcons Frame Kont)]
  [States (State With-env Kont)])

(define CESK-R
  (reduction-relation CESK
    [--> #:name variable-lookup
         (State (Closure (Ref x) ρ) κ)
         (State v κ)
         (where v (Store-lookup (Map-lookup ρ x)))]
    [--> #:name application
         (State (Closure (App e₀ e₁) ρ) κ)
         (State (Closure e₀ ρ) (Kcons (Ar e₁ ρ) κ))]
    [--> #:name argument-eval
         (State (Name v Value) (Kcons (Ar e ρ) κ))
         (State (Closure e ρ) (Kcons (Fn v) κ))]
    [--> #:name function-eval
         (State (Name v Value) (Kcons (Fn (Closure (Lam x e) ρ)) κ))
         (State (Closure e ρ*) κ)
         (where a (MAlloc bindings))
         (where ρ* (Map-extend ρ x a))
         (update a v)]))
(define-values (CESK♯ CESK-R♯ CESK-Ξ♯)
  (transform-semantics CESK CESK-R))

;; Can't put this in define-unit since it does compile-time side-effects.
(define-language CM-L
  [BAddrs #:address-space bindings]
  [Variable #:external-space symbol? #:cardinality (λ (e) 1)]
  [Permission #:external-space symbol? #:cardinality (λ (e) 1)]
  [Permissions (℘ Permission)]
  [GD (Deny) (Grant)]
  [Expr (Ref Variable) (App Expr Expr) Pre-value (Fail)
        (Frame Permissions Expr) (Grant Permissions Expr)
        (Test Permissions Expr Expr)
        #:trust-recursion]
  [Env (Variable → (Address-Space bindings))]
  [Pre-value (Lam Variable Expr) #:trust-recursion]
  [With-env (Closure Expr Env)]
  [Value (Closure Pre-value Env)]
  #:refinement ([Closure (Value With-env)])
  [Frame (Ar Expr Env) (Fn Value)]
  [Permission-map (Map Permission GD)]
  [Kont (Mt Permission-map) (Kcons Frame Permission-map Kont)]
  [States (State With-env Kont)]
  [OK-args (RK Permissions Kont)]
  [Pre-image-args (PI Permission-map GD)]
  [Bar-R-args (BR Permissions Permission-map)]
  [Set-m-args (SM Permission-map Kont)]
  [Grant-R-args (GR Permissions Permission-map)])

(define-metafunctions CM-L
  (Pre-image
   [(PI m v) es
    (when (Map-empty? m))
    (where es (Empty-set #:abstraction-of (Term m)))]
   [(PI (Map-with k v m) v)
    s
    (where s (Set-Add* (Pre-image (PI m v)) k))])

  (Marks-of
   [(Mt m) m]
   [(Kcons _ m _) m])

  (Set-marks
   [(SM m (Mt _)) (Mt m)]
   [(SM m (Kcons φ _ κ)) (Kcons φ m κ)])

  (Grant-perms
   [(GR R m) m
    (when (Set-empty? R))]
   [(GR (Set-with p R) m) m*
    (where m* (Let [(where m* (Grant-perms (GR R m)))]
                   (Map-extend m* p (Term (Grant)))))])

  ;; Every mapped permission not in R is set to deny.
  ;; Others are unchanged.
  (Bar-R
   [(BR R m) m
    (when (Map-empty? m))]
   [(BR R (Map-with m p gd)) m**
    (where m** (Let [(where m* (Bar-R (BR R m)))]
                  (Map-extend m* p (If (In-Set? R p)
                                       gd
                                       (Term (Deny))))))])

  (OK 
   [(RK r (Mt m)) allow
    (where allow (Set-empty? (Set-Intersect r (Pre-image (PI m (Deny))))))]
   [(RK r (Kcons _ m k)) allow
    (where allow (If (Set-empty? (Set-Intersect r (Pre-image (PI m (Deny)))))
                     (Let [(where r* (Set-Subtract r (Pre-image (PI m (Grant)))))]
                          (OK (RK r* k)))
                     #f))]))

(define CM-R
  (reduction-relation CM-L #:pun-space-names
    [--> #:name variable-lookup
         (State (Closure (Ref x) ρ) κ)
         (State v κ)
         (where v (Store-lookup (Map-lookup ρ x)))]
    [--> #:name application
         (State (Closure (App e₀ e₁) ρ) κ)
         (State (Closure e₀ ρ) (Kcons (Ar e₁ ρ) m κ))
         (where m (Marks-of κ))]
    [--> #:name argument-eval
         (State (Name v Value) (Kcons (Ar e ρ) m κ))
         (State (Closure e ρ) (Kcons (Fn v) m κ))]
    [--> #:name function-eval
         (State (Name v Value) (Kcons (Fn (Closure (Lam x e) ρ)) m κ))
         (State (Closure e ρ*) κ)
         (where a (MAlloc bindings))
         (where ρ* (Map-extend ρ x a))
         (update a v)]

    [--> #:name framing
         (State (Closure (Frame R e) ρ) κ)
         (State (Closure e ρ) κ*)
         (where κ* (Let [(where m (Marks-of κ))
                         (where m* (Bar-R (BR R m)))]
                        (Set-marks (SM m* κ))))]
    [--> #:name grant
         (State (Closure (Grant R e) ρ) κ)
         (State (Closure e ρ) κ*)
         (where κ* (Let [(where m (Marks-of κ))
                         (where m* (Grant-perms (GR R m)))]
                        (Set-marks (SM m* κ))))]
    [--> #:name test-permissions
         (State (Closure (Test R e₀ e₁) ρ) κ)
         (State (Closure e ρ) κ)
         (where e (If (OK (RK R κ))
                      e₀
                      e₁))]
    [--> (State (Closure (Fail) ρ) κ)
         (State (Closure (Fail) ρ) (Mt e))
         (where e (Empty-map #:concrete))]))

(define-unit CM-machine@
  (import)
  (export language-parms^)

  (define L (reify-language CM-L))

  (define trace-update #f)
  (define alloc #f)
  (define Ξ (reify-metafunctions-of CM-L))
  (printf "Damn~%"))
