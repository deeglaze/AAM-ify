#lang racket/base
(require "parser.rkt" "shared.rkt" "spaces.rkt"
         racket/unit
         (for-syntax racket/base))
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
  [Frame (Ar Expr Env) (Fn Value)]
  [Permission-map (Map Permission GD)]
  [Kont (Mt Permission-map) (Kcons Frame Permission-map Kont)]
  [States (State With-env Kont)]
  [OK-args (RK Permissions Kont)]
  [Pre-image-args (PI Permission-map GD)])
(begin-for-syntax (printf "Blorg"))

(define-metafunctions CM-L
  (Pre-image
   [(PI m v) es
    (when (Map-empty? m))
    (where es (Empty-set #:abstraction-of (Term m)))]
   [(PI (Map-with m k v) v)
    s
    (where s (Set-Add* (Pre-image (PI m v)) k))])

  (OK 
   [(RK r (Mt m)) allow
    (where allow (Set-empty? (Set-Intersect r (Pre-image (PI m (Deny))))))]
   [(RK r (Kcons _ m k)) allow
    (where allow (If (Set-empty? (Set-Intersect r (Pre-image (PI m (Deny)))))
                     (Let ([where r* (Set-Subtract r (Pre-image (PI m (Grant))))])
                          (OK (RK r* k)))
                     #f))]))

(define-unit CM-machine@
  (import)
  (export language-parms^)

  (define L (reify-language CM-L))

  (define trace-update #f)
  (define alloc #f)
  (define Ξ (reify-metafunctions-of CM-L)))
