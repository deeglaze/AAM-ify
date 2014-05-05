#lang racket/base
(require "parser.rkt" "shared.rkt" "spaces.rkt" "signatures.rkt"
         "concrete.rkt" "abstract.rkt"
         "transform-syntax.rkt" "alloc-skeleton.rkt"
         racket/unit
         racket/pretty
         (for-syntax racket/base))

(define-language CEK
  [Variable #:external-space symbol? #:cardinality (λ (e) 1) #:concrete]
  [Env (Variable → Value)]
  [Expr (Ref Variable) (App Expr Expr) Pre-value #:trust-recursion]
  [Pre-value (Lam Variable Expr) #:trust-recursion]
  [With-env (Closure Expr Env)]
  [Value (Closure Pre-value Env)]
  #:refinement ([Closure (Value With-env)])
  [Frame (Ar Expr Env) (Fn Value)]
  [Kont (Mt) (Kcons Frame Kont)]
  [States (State With-env Kont)])

(define CEK-R
  (reduction-relation CEK #:pun-space-names
    [--> #:name inject
         (Name e (Space Expr))
         (State (Closure e ρ₀) (Mt))
         (where ρ₀ (Empty-map #:concrete))]
    [--> #:name variable-lookup
         (State (Closure (Ref x) ρ) κ)
         (State v κ)
         (where v (Map-lookup ρ x))]
    [--> #:name application
         (State (Closure (App e₀ e₁) ρ) κ)
         (State (Closure e₀ ρ) (Kcons (Ar e₁ ρ) κ))]
    [--> #:name argument-eval
         (State (Name v Value) (Kcons (Ar e ρ) κ))
         (State (Closure e ρ) (Kcons (Fn v) κ))]
    [--> #:name function-eval
         (State (Name v Value) (Kcons (Fn (Closure (Lam x e) ρ)) κ))
         (State (Closure e ρ*) κ)
         (where ρ* (Map-extend ρ x v))]))
(define-values (CEK♯ CEK-Ξ♯ CEK-R♯)
  (transform-semantics CEK CEK-R))
(pretty-print CEK♯)
(newline)
(pretty-print (unparse-semantics CEK♯ CEK-R♯))


(define-language CESK
  [BAddrs #:address-space bindings]
  [Variable #:external-space symbol? #:cardinality (λ (e) 1) #:concrete]
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
  (reduction-relation CESK #:pun-space-names
    [--> #:name inject
         (Name e (Space Expr))
         (State (Closure e ρ₀) (Mt))
         (where ρ₀ (Empty-map #:concrete))]
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
(define-values (CESK♯ CESK-Ξ♯ CESK-R♯)
  (transform-semantics CESK CESK-R))

;; Can't put this in define-unit since it does compile-time side-effects.
(define-language CM-L
  [BAddrs #:address-space bindings]
  [Variable #:external-space symbol? #:cardinality (λ (e) 1) #:concrete]
  [Permission #:external-space symbol? #:cardinality (λ (e) 1) #:concrete]
  [Permissions (℘ Permission)]
  [GD (Deny) (Grant)]
  [Expr (Ref Variable) (App Expr Expr) Pre-value (Fail)
        (Frame Permissions Expr) (Grant Permissions Expr)
        (Test Permissions Expr Expr) #:trust-recursion]
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

(define-language Scheme
  [BAddr #:address-space bindings]
  [MAddr #:address-space mutable]
  [Variable #:external-space symbol? #:cardinality (λ (e) 1) #:concrete]
  [Number #:external-space number? #:cardinality (λ (e) 1) #:concrete]
  [String #:external-space string? #:cardinality (λ (e) 1) #:concrete]
  [Char #:external-space char? #:cardinality (λ (e) 1) #:concrete]
  [Symbol #:external-space symbol? #:cardinality (λ (e) 1) #:concrete]
  [Variable-List '() (VarCons Variable Variable-List) #:trust-recursion]
  [Variable-List-Trusted '() (TVarCons Variable Variable-List) #:trust-recursion #:trust-construction]
  [Expr (Ref Variable)
        (App Expr Expr-List)
        Pre-value
        (Quote Literal)
        (sIf Expr Expr Expr)
        (sLet Let-Clauses Expr)
        (sLetrec Let-Clauses Expr)
        (Let/cc Variable Expr)
        Primitive
        #:trust-recursion]
  [Primitive-name ;; tag checks
                  'pair?
                  'null?
                  'string?
                  'procedure?
                  'vector?
                  'boolean?
                  'symbol?
                  ;; others
                  'apply
                  'box 'unbox 'set-box! ;; because Fuck set!
                  'zero? '+ '- 'apply 'vector-length]
  [Primitive (Prim Primitive-name)]
  [Let-Clauses '() (LCcons Variable Expr Let-Clauses) #:trust-recursion]
  [Letrec-tuples '() (LRcons BAddr Expr Letrec-tuples) #:trust-recursion #:trust-construction]
  [Expr-List '() (Econs Expr Expr-List) #:trust-recursion]
  [Literal Number String Symbol Char Bool '()]
  [Bool #t #f]
  [Env (Variable → BAddr)]
  [Pre-value (Lam Variable-List Expr) (RLam Variable-List Variable Expr) #:trust-recursion]
  [Value (Closure Pre-value Env)
         Primitive
         Literal
         (Consv Value Value)
         (Vector Number Value-List)
         (Box MAddr)
         (Void)]
  [Address-List-Trusted '() (TAcons BAddr Address-List-Trusted)
                        #:trust-recursion #:trust-construction]
  [Value-List-Trusted '() (TVcons Value Value-List-Trusted) #:trust-recursion #:trust-construction]
  [Value-List '() (Vcons Value Value-List)]
  [Frame (kEv Expr-List Value-List-Trusted Env)
         (kIf Expr Expr Env)
         (klt Variable Let-Clauses Variable-List-Trusted Value-List-Trusted Expr Env)
         (klc BAddr Letrec-tuples Expr Env)]
  [Kont (Mt) (Kcons Frame Kont)]
  [States (Ev Expr Env Kont)
          (Co Kont Value)
          ;; "plain apply"
          (Pa Variable-List Expr Env Value-List-Trusted Kont)
          ;; "rest-arg apply"
          (Ra Variable-List Variable Expr Env Value-List-Trusted Kont)]
  ;; Meta-function argument spaces
  [Alloc-letrec-args (AL Let-Clauses Env)]
  [Alloc-letrec-result (ALres Letrec-tuples Env)]
  [TV-reverse-aux-args (TVRA Value-List-Trusted Value-List-Trusted)]
  [Bind-let-args (BL Variable-List-Trusted Value-List-Trusted Env)]
  [Bind-args-args (BA Variable-List Value-List-Trusted Env)]
  [Bind-rest-args-args (BAR Variable-List Variable Value-List-Trusted Bool Env)])

(define-metafunctions Scheme
  (bind-args
   [(BA '() '() ρ) ρ]
   [(BA (VarCons x xs) (TVcons v vs) ρ)
    ρ**
    (where a (MAlloc bindings))
    (where ρ* (Map-extend ρ x a))
    (update a v)
    (where ρ** (bind-args (BA xs vs ρ*)))])

  (bind-rest-args
   ;; No more args. Rest-arg gets empty list since nothing given.
   [(BAR '() r '() bind-last? ρ)
    ρ*
    (when (If bind-list? #f #t)) ;; bad match if supposed to have a list.
    (where ra (MAlloc bindings))
    (where ρ* (Map-extend ρ r ra))
    (update ra '())]
   ;; Last argument is the rest arg.
   [(BAR '() r (TVcons v '()) bind-last? ρ)
    ρ*
    (where ra (MAlloc bindings))
    (where ρ* (Map-extend ρ r ra))
    (update ra (If bind-last?
                   v
                   (Cons v '())))]
   ;; More arguments given. Allocate conses.
   [(BAR '() r (TVcons v vs) b? ρ)
    ρ*
    (where ra (MAlloc bindings))
    (where ρ* (bind-rest-args (BAR '() r vs b? ρ)))
    (where rv (Store-lookup (Map-lookup ρ* r)))
    (update ra (Cons v rv))
    ;; Point r at the new cons cell.
    (where ρ** (Map-extend ρ* r ra))]
   ;; Starting with original arguments.
   [(BAR (VarCons x xs) r (TVcons v vs) b? ρ)
    ρ**
    (where a (MAlloc bindings))
    (where ρ* (Map-extend ρ x a))
    (update a v)
    (where ρ** (bind-rest-args (BAR xs r vs b? ρ*)))])

  (alloc-letrec
   [(AL '() ρ) (ALres '() ρ)]
   [(AL (LCcons x e lcs) ρ)
    (ALres (LRcons a e lrs) ρ**)
    (where (ALres lrs ρ*) (alloc-letrec (AL lcs ρ)))
    (where a (MAlloc bindings))
    (where ρ** (Map-extend ρ* x a))])

  (TVreverse
   [l (TVreverse-aux l '())])

  (TVreverse-aux
   [(TVRA '() acc) acc]
   [(TVRA (TVcons v vs) acc)
    l
    (where l (TVreverse-aux (TVRA vs (TVcons v acc))))])
  
  (bind-let
   [(BL '() '() ρ) ρ]
   [(BL (TVarCons x xs) (TVcons v vs) ρ)
    ρ**
    (where a (MAlloc bindings))
    (where ρ* (Map-extend ρ x a))
    (update a v)
    (where ρ** (bind-let (BL xs vs ρ*)))])
  )

(define Scheme-R
  (reduction-relation Scheme
    ;; "Eval" rules
    [--> (Ev (Ref x) ρ κ)
         (Co κ v)
         (where v (Store-lookup (Map-lookup ρ x)))]
    [--> (Ev (App e₀ es) ρ κ)
         (Ev e₀ ρ (Kcons (kEv es '() ρ) κ))]
    [--> #:name λ→closure
         (Ev (Name l (Space Pre-value)) ρ κ)
         (Co κ (Closure l ρ))]
    [--> (Ev (Quote l) ρ κ)
         (Co κ l)]
    [--> (Ev (sIf g t e) ρ κ)
         (Ev g ρ (Kcons (kIf t e ρ) κ))]
    [--> #:name let-0-clauses
         (Ev (sLet '() e) ρ κ)
         (Ev e ρ κ)]
    [--> (Ev (sLet (LCcons x e lcs) body) ρ κ)
         (Ev e ρ (Kcons (klt x lcs '() '() body ρ) κ))]
    [--> #:name letrec-0-clauses
         (Ev (sLetrec '() e) ρ κ)
         (Ev e ρ κ)]
    [--> (Ev (sLetrec (Name lcs (LCcons _ _ _)) body) ρ κ)
         (Ev e ρ (Kcons (klc a lrs body ρ*) κ))
         (where (ALres (LRcons a e lrs) ρ*) (alloc-letrec (AL lcs ρ)))]
    [--> (Ev (Let/cc x e) ρ κ)
         (Ev e ρ* κ)
         (where a (MAlloc bindings))
         (where ρ* (Map-extend ρ x a))
         (update a κ)]
    [--> (Ev (Set! x e) ρ κ)
         (Ev e ρ (Kcons (kS! a) κ))
         (where a (Map-lookup ρ x))]
    [--> (Ev (Name prim (Prim _)) ρ κ)
         (Co κ prim)]
    ;; "Continue" rules
    [--> (Co (Kcons (kEv '() vs ρ) κ) v)
         rhs
         (where (TVcons (Closure fn ρ) args) (TVreverse (TVcons v vs)))
         (where rhs (Match fn
                      [(Lam xs e) (Pa xs e ρ args κ)]
                      [(RLam xs r e) (Ra xs r e ρ args κ)]
                      [(Prim p) rhs (where rhs (prim-apply p args κ))]))]
    [--> (Co (Kcons (kEv (Econs e es) vs ρ) κ) v)
         (Ev e ρ (Kcons (kEv es (TVcons v vs) ρ) κ))]
    [--> (Co (Kcons (kIf then else ρ) κ) v)
         (Ev which ρ κ)
         (where which (If v then else))]
    [--> (Co (Kcons (kS! a) κ) v)
         (Co κ (Void))
         (update a v)]
    [--> #:name let-finished
         (Co (Kcons (klt x '() xs vs body ρ) κ) v)
         (Ev body ρ* κ)
         (where ρ* (bind-let (BL (TVarCons x xvs) (TVcons v vs) ρ)))]
    [--> (Co (Kcons (klt x (LCcons y e lcs) xs vs body ρ) κ) v)
         (Ev e ρ (Kcons (klt y lcs (TVarCons x xs) (TVcons v vs) body ρ) κ))]
    [--> (Co (Kcons (klc a '() body ρ) κ) v)
         (Ev body ρ κ)
         (update a v)]
    [--> (Co (Kcons (klc a (LRcons a* e lrs) body ρ) κ) v)
         (Ev e ρ (Kcons (klc a* lrs body ρ) κ))
         (update a v)]
    ;; "Apply" rules
    [--> (Pa xs e ρ args κ)
         (Ev e ρ* κ)
         (where ρ* (bind-args (BA xs args ρ)))]
    [--> (Ra xs r e ρ args κ)
         (Ev e ρ* κ)
         (where ρ* (bind-rest-args (BAR xs r args #f ρ)))]))

(define-unit CM-machine@
  (import)
  (export language-parms^)

  (define L (reify-language CM-L))
  (define Ξ (reify-metafunctions-of CM-L))

  (define trace-update #f)
  (define alloc #f))

(define-unit abstract-CM-machine@
  (import)
  (export language-parms^)

  (define-values (L Ξ R) (transform-semantics CM-L CM-R))

  (alloc-skeleton L)

  (define trace-update #f)
  (define alloc #f))

(define-values/invoke-unit/infer (link CM-machine@ concrete-semantics@))
