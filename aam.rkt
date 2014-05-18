#lang racket/base
(require "parser.rkt"
         "unparser.rkt"
         "shared.rkt" "spaces.rkt" "signatures.rkt"
         "concrete.rkt" "abstract.rkt"
         "transform-syntax.rkt" "alloc-skeleton.rkt"
         racket/unit
         racket/match
         racket/pretty
         (for-syntax racket/base racket/match "spaces.rkt"))

(module both-phases racket/base
  (require "lattices.rkt" "spaces.rkt" racket/match)
  (provide (all-defined-out)
           (all-from-out "lattices.rkt"))
  (define (get-space L name) (hash-ref (Language-spaces L) name))
  (define (extract x)
    (match x
      [(or (external _ v) (Datum v)) v]
      [_ (error 'extract "Expected external or Datum ~a" x)])))
(require (submod "." both-phases)
         (for-syntax (submod "." both-phases)))
#;
'(
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
                             (Name e (is-a Expr))
                             (State (Closure e ρ₀) (Mt))
                             (where ρ₀ (Empty-map Env))]
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
(pretty-print (unparse-language CEK♯))
(newline)
(pretty-print (unparse-semantics CEK♯ CEK-R♯))
)

(define-language CESK
  [BAddrs (Address-Space bindings)]
  [Variable #:external-space symbol? #:cardinality (λ (e) 1) #:concrete]
  [Env (Variable → BAddrs)]
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
                            (Name e (is-a Expr))
                            (State (Closure e ρ₀) (Mt))
                            (where ρ₀ (Empty-map Env))]
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
                            (where a (Alloc bindings #:egal))
                            (where ρ* (Map-extend ρ x a))
                            (update a v)]))
 (define-values (CESK♯ CESK-Ξ♯ CESK-R♯)
   (transform-semantics CESK CESK-R))

 ;; Can't put this in define-unit since it does compile-time side-effects.
 (define-language CM-L
   [BAddrs (Address-Space bindings)]
   [Variable #:external-space symbol? #:cardinality (λ (e) 1) #:concrete]
   [Permission #:external-space symbol? #:cardinality (λ (e) 1) #:concrete]
   [Permissions (℘ Permission)]
   ;; FIXME: GD used to have a (Grant) which then conflicted with the Expr Grant form.
   ;; define-language did not complain at the right time.
   [GD (Deny) (Allow)]
   [Expr (Ref Variable) (App Expr Expr) Pre-value (Fail)
         (Frame Permissions Expr) (Grant Permissions Expr)
         (Test Permissions Expr Expr) #:trust-recursion]
   [Env (Variable → BAddrs)]
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
     (where es (Empty-set Permissions))]
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
                    (Map-extend m* p (Term (Allow)))))])

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
                      (Let [(where r* (Set-Subtract r (Pre-image (PI m (Allow)))))]
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
                            (where a (Alloc bindings #:egal))
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
                            (where e (Empty-map Env))]))



 (define-language Scheme
   [BAddr (Address-Space bindings)]
   [MAddr (Address-Space mutable)]
   [Variable #:external-space symbol?]
   [Number #:external-space number?]
   [String #:external-space string?]
   [Char #:external-space char?]
   [Symbol #:external-space symbol?]
   [Variable-List '() (VarCons Variable Variable-List) #:trust-recursion]
   [Variable-List-Trusted '() (TVarCons Variable Variable-List-Trusted)
                          #:trust-recursion #:trust-construction]
   [Expr (Ref Variable)
         (App Expr Expr-List)
         Pre-value
         (Quote Literal)
         (sIf Expr Expr Expr)
         (sLet Let-Clauses Expr)
         (sLetrec Let-Clauses Expr)
         (Begin Expr Expr-List)
         Primitive
         #:trust-recursion]
   [Primitive-name ;; tag checks
    Predicate
    Numerics
    Data-operators
    ;; others
    'apply 'call/cc]
   [Predicate 'pair?
              'null?
              'string?
              'procedure?
              'vector?
              'boolean?
              'symbol?
              'void?
              'eof-object?]
   [Numerics 'zero? '+ '- '/ '* 'sub1]
   [Data-operators 'box 'unbox 'set-box! ;; No set! in the language
                   'make-vector 'vector 'vector-length 'vector-set! 'vector-ref
                   'cons 'car 'cdr
                   'void]
   [Primitive (Prim Primitive-name)]
   [Let-Clauses '() (LCcons Variable Expr Let-Clauses) #:trust-recursion]
   [Letrec-tuples '() (LRcons BAddr Expr Letrec-tuples) #:trust-recursion #:trust-construction]
   [Expr-List '() (Econs Expr Expr-List) #:trust-recursion]
   [Literal Number String Symbol Char Bool '() (Void) (Eof-object)]
   [Env (Variable → BAddr)]
   [Pre-value (Lam Variable-List Expr) (RLam Variable-List Variable Expr) #:trust-recursion]
   [Value (Closure Pre-value Env)
          (Cons Value Value)
          (Vector Number Value-List)
          (Box MAddr)
          Flat-Value]
   [Flat-Value Primitive
               Literal]
   [Address-List-Trusted '() (TAcons BAddr Address-List-Trusted)
                         #:trust-recursion #:trust-construction]
   [Value-List-Trusted '() (TVcons Value Value-List-Trusted) #:trust-recursion #:trust-construction]
   [Value-List '() (Vcons Value Value-List)]
   [Frame (kEv Expr-List Value-List-Trusted Env)
          (kIf Expr Expr Env)
          (klt Variable Let-Clauses Variable-List-Trusted Value-List-Trusted Expr Env)
          (klc BAddr Letrec-tuples Expr Env)
          (kBegin Expr-List Env)]
   [Kont (Mt) (Kcons Frame Kont)]
   [States (Ev Expr Env Kont)
           (Co Kont Value)
           ;; "plain apply"
           (Pa Variable-List Expr Env Value-List-Trusted Kont)
           ;; "rest-arg apply"
           (Ra Variable-List Variable Expr Env Value-List-Trusted Kont)
           ;; answers
           (Ans Value)]
   ;; Meta-function argument spaces
   [Alloc-letrec-args (AL Let-Clauses Env)]
   [Alloc-letrec-result (ALres Letrec-tuples Env)]
   [TV-reverse-aux-args (TVRA Value-List-Trusted Value-List-Trusted)]
   [Bind-let-args (BL Variable-List-Trusted Value-List-Trusted Env)]
   [Bind-args-apply-args (BAA Variable-List Value-List-Trusted Env)]
   [Bind-args-args (BA Variable-List Value-List-Trusted Env)]
   [Bind-rest-args-args (BAR Variable-List Variable Value-List-Trusted Bool Env)]
   [Prim-apply-args (PA Primitive-name Value-List-Trusted Kont)]
   [Predicate-args (PP Predicate Value)]
   [Numeric-args (NP Numerics Value-List-Trusted)]
   [Binary-num-args (B2 Number Number)]
   [Data-args (DP Data-operators Value-List-Trusted)])

 (define-metafunctions Scheme
   (bind-args
    [(BA '() '() ρ) ρ]
    [(BA (VarCons x xs) (TVcons v vs) ρ)
     ρ**
     (where a (Alloc bindings #:egal))
     (where ρ* (Map-extend ρ x a))
     (update a v)
     (where ρ** (bind-args (BA xs vs ρ*)))])

   (bind-args-apply
    ;; Expecting no more arguments, must not have any more arguments.
    [(BAA '() (TVcons '() '()) ρ) ρ]
    [(BAA (VarCons x xs) (TVcons (Cons v vs) '()) ρ)
     ρ**
     (where a (Alloc bindings #:egal))
     (where ρ* (Map-extend ρ x a))
     (update a v)
     (where ρ** (bind-args-apply (BAA xs (TVcons vs '()) ρ*)))]
    [(BAA (VarCons x xs) (TVcons v vs) ρ)
     ρ**
     (where a (Alloc bindings #:egal))
     (where ρ* (Map-extend ρ x a))
     (update a v)
     (where ρ** (bind-args-apply (BAA xs vs ρ*)))])

   (bind-rest-args
    ;; No more args. Rest-arg gets empty list since nothing given.
    [(BAR '() r '() bind-last? ρ)
     ρ*
     (when (If bind-last? #f #t)) ;; bad match if supposed to have a list.
     (where ra (Alloc bindings #:egal))
     (where ρ* (Map-extend ρ r ra))
     (update ra '())]
    ;; Last argument is the rest arg.
    ;; XXX: We don't check if v is a proper list when v is expected to be a list.
    [(BAR '() r (TVcons v '()) bind-last? ρ)
     ρ*
     (where ra (Alloc bindings #:egal))
     (where ρ* (Map-extend ρ r ra))
     (update ra (If bind-last?
                    v
                    (Term (Cons v '()))))]
    ;; More arguments given. Allocate conses.
    [(BAR '() r (TVcons v vs) b? ρ)
     ρ*
     (where ra (Alloc bindings #:egal))
     (where ρ* (bind-rest-args (BAR '() r vs b? ρ)))
     (where rv (Store-lookup (Map-lookup ρ* r)))
     (update ra (Term (Cons v rv)))
     ;; Point r at the new cons cell.
     (where ρ** (Map-extend ρ* r ra))]
    ;; Fewer arguments given. If bind-last? then pull values from the list.
    [(BAR (VarCons x xs) r (TVcons (Cons v vs) '()) #t ρ)
     ρ**
     (where a (Alloc bindings #:egal))
     (where ρ* (Map-extend ρ x a))
     (update a v)
     (where ρ** (bind-rest-args (BAR xs r (TVcons vs '()) #t ρ*)))]
    ;; Starting with original arguments.
    [(BAR (VarCons x xs) r (TVcons v vs) b? ρ)
     ρ**
     (where a (Alloc bindings #:egal))
     (where ρ* (Map-extend ρ x a))
     (update a v)
     (where ρ** (bind-rest-args (BAR xs r vs b? ρ*)))])

   (alloc-letrec
    [(AL '() ρ) (ALres '() ρ)]
    [(AL (LCcons x e lcs) ρ)
     (ALres (LRcons a e lrs) ρ**)
     (where (ALres lrs ρ*) (alloc-letrec (AL lcs ρ)))
     (where a (Alloc bindings #:egal))
     (where ρ** (Map-extend ρ* x a))])

   (TVreverse
    [l l*
       (where l* (TVreverse-aux (TVRA l '())))])

   (TVreverse-aux
    [(TVRA '() acc) acc]
    [(TVRA (TVcons v vs) acc)
     l
     (where l (TVreverse-aux (TVRA vs (TVcons v acc))))])
  
   (bind-let
    [(BL '() '() ρ) ρ]
    [(BL (TVarCons x xs) (TVcons v vs) ρ)
     ρ**
     (where a (Alloc bindings #:egal))
     (where ρ* (Map-extend ρ x a))
     (update a v)
     (where ρ** (bind-let (BL xs vs ρ*)))])
  
   (prim-apply
    [(PA 'apply (TVcons (Prim p) args) κ)
     dummy
     (where dummy (??? 'apply-prim))]
    [(PA 'apply (TVcons (Closure (RLam xs r e) ρ) args) κ)
     (Ev e ρ* κ)
     (where ρ* (bind-rest-args (BAR xs r args #t ρ)))]
    [(PA 'apply (TVcons (Closure (Lam xs e) ρ) args) κ)
     (Ev e ρ* κ)
     (where ρ* (bind-args-apply (BAA xs args ρ)))]

    [(PA 'call/cc (TVcons fnv '()) κ)
     rhs
     (where rhs (Match fnv
                       [(Closure fn ρ)
                        v
                        (where v
                               (Match fn
                                      [(Lam (VarCons k '()) e)
                                       (Ev e ρ* κ)
                                       (where a (Alloc bindings #:egal))
                                       (where ρ* (Map-extend ρ k a))
                                       (update a κ)]
                                      [(RLam '() r e)
                                       (Ev e ρ* κ)
                                       (where a (Alloc bindings #:egal))
                                       (where ρ* (Map-extend ρ r a))
                                       (update a (Term (Cons κ '())))]
                                      [(RLam (VarCons k '()) r e)
                                       (Ev e ρ** κ)
                                       (where a (Alloc bindings #:egal))
                                       (where ra (Alloc bindings #:egal))
                                       (where ρ* (Map-extend ρ k a))
                                       (where ρ** (Map-extend ρ* r ra))
                                       (update a κ)
                                       (update ra '())]))]
                       [(Prim p) dummy (where dummy (??? "call/cc given primitive"))]))]

    [(PA (Name p (is-a Predicate)) (TVcons v '()) κ)
     (Co κ b)
     (where b (predicate-prim (PP p v)))]

    [(PA (Name p (is-a Numerics)) vs κ)
     (Co κ v)
     (where v (numeric-prim (NP p vs)))]

    [(PA (Name p (is-a Data-operators)) vs κ)
     (Co κ v)
     (where v (data-prim (DP p vs)))])

   (data-prim
    [(DP 'cons (TVcons car (TVcons cdr '())))
     (Cons car cdr)]
    [(DP 'car (TVcons (Cons car _) '()))
     car]
    [(DP 'cdr (TVcons (Cons _ cdr) '()))
     cdr]
    [(DP 'box (TVcons v '()))
     (Box a)
     (where a (Alloc mutable #:egal))
     (update a v)]
    [(DP 'unbox (TVcons (Box a) '()))
     v
     (where v (Store-lookup a))]
    [(DP 'set-box! (TVcons (Box a) (TVcons v '())))
     (Void)
     (update a v)]
    [(DP 'void _) (Void)])

   (predicate-prim
    [(PP 'procedure? v) b
     (where b (Match v [(Closure _ _) #t] [(Prim _) #t] [_ #f]))]
    [(PP 'null? v) b
     (where b (Match v ['() #t] [_ #f]))]
    [(PP 'number? v) b
     (where b (Match v [(is-a Number) #t] [_ #f]))]
    [(PP 'pair? v) b
     (where b (Match v [(Cons _ _) #t] [_ #f]))]
    [(PP 'string? v) b
     (where b (Match v [(is-a String) #t] [_ #f]))]
    [(PP 'vector? v) b
     (where b (Match v [(Vector _ _) #t] [_ #f]))]
    [(PP 'boolean? v) b
     (where b (Match v [(is-a Bool) #t] [_ #f]))]
    [(PP 'symbol? v) b
     (where b (Match v [(is-a Symbol) #t] [_ #f]))]
    [(PP 'char? v) b
     (where b (Match v [(is-a Char) #t] [_ #f]))]
    [(PP 'void? v) b
     (where b (Match v [(Void) #t] [_ #f]))]
    [(PP 'eof-object? v) b
     (where b (Match v [(Eof-object) #t] [_ #f]))])

   (binary-+
    #:concrete (λ (L store-spaces argd)
                  (State
                   (match argd
                     [(variant (Variant _ 'B2 _ _ _) (vector n r))
                      (external (get-space L 'Number) (+ (extract n) (extract r)))])
                   store-spaces))
    #:abstract (λ (L ς store-spaces μ argd)
                  (hash '()
                   (Abs-Result/effect
                    #t
                    (external (get-space L 'Number)
                     (match argd
                       [(variant (Variant _ 'B2 _ _ _) (vector n r))
                        (define n* (extract n))
                        (define r* (extract r))
                        (cond [(zero? n*) r*]
                              [(zero? r*) n*]
                              [else -⊤])]))
                    store-spaces μ))))
   (binary-*
    #:concrete (λ (L store-spaces argd)
                  (State
                   (match argd
                     [(variant (Variant _ 'B2 _ _ _) (vector n r))
                      (external (get-space L 'Number) (* (extract n) (extract r)))])
                   store-spaces))
    #:abstract (λ (L ς store-spaces μ argd)
                  (hash '()
                   (Abs-Result/effect
                    #t
                    (external (get-space L 'Number)
                     (match argd
                       [(variant (Variant _ 'B2 _ _ _) (vector n* r*))
                        (define n (extract n*))
                        (define r (extract r*))
                        (cond [(or (eq? n -⊤) (eq? r -⊤)) -⊤]
                              [(eq? 1 n) r]
                              [(eq? 1 r) n]
                              [else -⊤])]))
                    store-spaces μ))))

   (external-zero?
    #:concrete (λ (L store-spaces argd)
                  (State 
                   (match argd
                     [(or (external _ n) (Datum n))
                      (and (number? n) (zero? n))]
                     [_ #f])
                   store-spaces))
    #:abstract (λ (L ς store-spaces μ argd)
                  (hash '()
                   (Abs-Result/effect
                    #t
                    (match argd
                      [(or (external _ n) (Datum n))
                       (if (eq? n -⊤)
                           absb.⊤
                           (and (number? n) (zero? n)))]
                      [_ #f])
                    store-spaces μ))))
   (numeric-prim
    [(NP '+ '()) 0]
    [(NP '+ (TVcons (Name n (is-a Number)) vs))
     res
     (where r (numeric-prim (NP '+ vs)))
     (where res (binary-+ (B2 n r)))]
    [(NP '* '()) 1]
    [(NP '* (TVcons (Name n (is-a Number)) vs))
     res
     (where r (numeric-prim (NP '* vs)))
     (where res (binary-* (B2 n r)))]
    [(NP 'zero? (TVcons n '()))
     res
     (where res (external-zero? n))]
    [(NP 'zero? (TVcons (Name n (is-a Number)) '()))
     #t]
    [(NP 'sub1 (TVcons (Name n (is-a Number)) '()))
     [#:external Number -⊤]]))


 (define Scheme-R
   (reduction-relation Scheme
     ;; "Eval" rules
     [--> #:name var-lookup
          (Ev (Ref x) ρ κ)
          (Co κ v)
          (where v (Store-lookup (Map-lookup ρ x)))]
     [--> #:name ev-app
          (Ev (App e₀ es) ρ κ)
          (Ev e₀ ρ (Kcons (kEv es '() ρ) κ))]
     [--> #:name λ→closure
          (Ev (Name l (is-a Pre-value)) ρ κ)
          (Co κ (Closure l ρ))]
     [--> #:name literal→value
          (Ev (Quote l) ρ κ)
          (Co κ l)]
     [--> #:name ev-if
          (Ev (sIf g t e) ρ κ)
          (Ev g ρ (Kcons (kIf t e ρ) κ))]
     [--> #:name let-0-clauses
          (Ev (sLet '() e) ρ κ)
          (Ev e ρ κ)]
     [--> #:name ev-let
          (Ev (sLet (LCcons x e lcs) body) ρ κ)
          (Ev e ρ (Kcons (klt x lcs '() '() body ρ) κ))]
     [--> #:name letrec-0-clauses
          (Ev (sLetrec '() e) ρ κ)
          (Ev e ρ κ)]
     [--> #:name ev-letrec
          (Ev (sLetrec (Name lcs (LCcons _ _ _)) body) ρ κ)
          (Ev e ρ* (Kcons (klc a lrs body ρ*) κ))
          (where (ALres (LRcons a e lrs) ρ*) (alloc-letrec (AL lcs ρ)))]
     [--> #:name ev-begin
          (Ev (Begin e es) ρ κ)
          (Ev e ρ (Kcons (kBegin es ρ) κ))]
     [--> #:name prim-name→prim
          (Ev (Name prim (Prim _)) ρ κ)
          (Co κ prim)]
     ;; "Continue" rules
     [--> #:name go-apply
          (Co (Kcons (kEv '() vs _) κ) v)
          rhs
          (where (TVcons fn args) (TVreverse (TVcons v vs)))
          (where rhs (Match fn
                            [(Closure (Lam xs e) ρ) (Pa xs e ρ args κ)]
                            [(Closure (RLam xs r e) ρ) (Ra xs r e ρ args κ)]
                            [(Prim p) rhs (where rhs (prim-apply (PA p args κ)))]))]
     [--> #:name co-arg
          (Co (Kcons (kEv (Econs e es) vs ρ) κ) v)
          (Ev e ρ (Kcons (kEv es (TVcons v vs) ρ) κ))]
     [--> #:name co-if
          (Co (Kcons (kIf then else ρ) κ) v)
          (Ev which ρ κ)
          (where which (If v then else))]
     [--> #:name let-finished
          (Co (Kcons (klt x '() xs vs body ρ) κ) v)
          (Ev body ρ* κ)
          (where ρ* (bind-let (BL (TVarCons x xs) (TVcons v vs) ρ)))]
     [--> #:name co-let
          (Co (Kcons (klt x (LCcons y e lcs) xs vs body ρ) κ) v)
          (Ev e ρ (Kcons (klt y lcs (TVarCons x xs) (TVcons v vs) body ρ) κ))]
     [--> #:name letrec-finished
          (Co (Kcons (klc a '() body ρ) κ) v)
          (Ev body ρ κ)
          (update a v)]
     [--> #:name co-letrec
          (Co (Kcons (klc a (LRcons a* e lrs) body ρ) κ) v)
          (Ev e ρ (Kcons (klc a* lrs body ρ) κ))
          (update a v)]
     [--> #:name co-begin
          (Co (Kcons (kBegin (TVcons e es) ρ) κ) v)
          (Ev e ρ (Kcons (kBegin es ρ) κ))]
     [--> #:name begin-finished
          (Co (Kcons (kBegin '() ρ) κ) v)
          (Co κ v)]
     ;; "Apply" rules
     [--> #:name plain-apply
          (Pa xs e ρ args κ)
          (Ev e ρ* κ)
          (where ρ* (bind-args (BA xs args ρ)))]
     [--> #:name rest-apply
          (Ra xs r e ρ args κ)
          (Ev e ρ* κ)
          (where ρ* (bind-rest-args (BAR xs r args #f ρ)))]
     [--> #:name done
          (Co (Mt) v)
          (Ans v)]))


(define-unit Scheme@
  (import)
  (export language-parms^)

  (define L (reify-language Scheme))
  (define Ξ (reify-metafunctions-of Scheme))
  (define R Scheme-R)

  (define trace-update #f)
  (define alloc #f))

(define-unit abstract-Scheme@
  (import)
  (export language-parms^)

  (define-values (abs-L Ξ R)
    (transform-semantics
     Scheme Scheme-R
     #:hint-relabeling
     ([`((ev-app RHS) ,(Variant-field 'Ev 2) ,(Variant-field 'Kcons 1))
       'AppK] 
      [`((ev-if RHS) ,(Variant-field 'Ev 2) ,(Variant-field 'Kcons 1))
       'IfK]
      [`((ev-let RHS) ,(Variant-field 'Ev 2) ,(Variant-field 'Kcons 1))
       'LetK]
      [`((ev-letrec RHS) ,(Variant-field 'Ev 2) ,(Variant-field 'Kcons 1))
       'LetrecK]
      [`((co-arg RHS) ,(Variant-field 'Ev 2) ,(Variant-field 'Kcons 1))
       'kEvK]
      [`((co-let RHS) ,(Variant-field 'Ev 2) ,(Variant-field 'Kcons 1))
       'kLetK]
      [`((co-letrec RHS) ,(Variant-field 'Ev 2) ,(Variant-field 'Kcons 1))
       'kLetrecK]
      [`(bind-args (Rule 1) (Let-binding 0))
       'bind-args]
      [`(bind-args-apply (Rule 1) (Let-binding 0))
       'bind-args-apply-pull]
      [`(bind-args-apply (Rule 2) (Let-binding 0))
       'bind-args-apply]
      [`(bind-rest-args (Rule 0) (Let-binding 1))
       'bind-rest-args-empty]
      [`(bind-rest-args (Rule 1) (Let-binding 0))
       'bind-rest-args-rest]
      [`((bind-rest-args (Rule 1) (Let-store-val 2) If-else) ,(Variant-field 'Cons 0))
       'bind-rest-args-spill-value]
      [`((bind-rest-args (Rule 1) (Let-store-val 2) If-else) ,(Variant-field 'Cons 1))
       'bind-rest-args-spill-tail]
      [`(bind-rest-args (Rule 2) (Let-binding 0))
       'bind-rest-args-bunch-tail]
      [`((bind-rest-args (Rule 2) (Let-store-val 3)) ,(Variant-field 'Cons 0))
       'bind-rest-args-bunch-value]
      [`((bind-rest-args (Rule 2) (Let-store-val 3)) ,(Variant-field 'Cons 1))
       'bind-rest-args-bunch-rest]
      [`(bind-rest-args (Rule 3) (Let-binding 0))
       'bind-rest-args-pull]
      [`(bind-rest-args (Rule 4) (Let-binding 0))
       'bind-rest-args]
      [`(alloc-letrec (Rule 1) (Let-binding 1))
       'alloc-letrec]
      [`(bind-let (Rule 1) (Let-binding 0))
       'bind-let]
      [`(prim-apply (Rule 3) (Let-binding 0) Match-rule (Rule 0) (Let-binding 0) Match-rule (Rule 2) (Let-binding 0))
       'rest-arg-call/cc-mandatory]
      [`(prim-apply (Rule 3) (Let-binding 0) Match-rule (Rule 0) (Let-binding 0) Match-rule (Rule 2) (Let-binding 1))
       'rest-arg-call/cc-mandatory-tail]
      [`(prim-apply (Rule 3) (Let-binding 0) Match-rule (Rule 0) (Let-binding 0) Match-rule (Rule 1) (Let-binding 0))
       'rest-arg-call/cc-rest]
      [`((prim-apply (Rule 3) (Let-binding 0) Match-rule (Rule 0) (Let-binding 0) Match-rule (Rule 1) (Let-store-val 2)) ,(Variant-field 'Cons 0))
       'rest-arg-call/cc-rest-value]
      [`((prim-apply (Rule 3) (Let-binding 0) Match-rule (Rule 0) (Let-binding 0) Match-rule (Rule 1) (Let-store-val 2)) ,(Variant-field 'Cons 1))
       'rest-arg-call/cc-rest-null]
      [`(prim-apply (Rule 3) (Let-binding 0) Match-rule (Rule 0) (Let-binding 0) Match-rule (Rule 0) (Let-binding 0))
       'plain-call/cc-arg]
      [`((data-prim (Rule 0) RHS) ,(Variant-field 'Cons 0))
       'cons-car]
      [`((data-prim (Rule 0) RHS) ,(Variant-field 'Cons 1))
       'cons-cdr]
      [`(data-prim (Rule 3) (Let-binding 0))
       'box])))
  (define L (Abs-Language-L abs-L))

  (define-values (scheme-alloc scheme-alloc-stx) (alloc-skeleton R Ξ))
  (pretty-write (unparse-language L))
  (pretty-write (unparse-semantics abs-L R))
  (pretty-write (unparse-Ξ abs-L Ξ))
  (pretty-write (syntax->datum scheme-alloc-stx))
  
  (define (trace-update ς new-term choices τ̂)
    new-term)
  (define alloc
    (λ (ς ρ hint)
       (match-define (Abs-State term σ μ τ̂) ς)
       (match hint
         ['AppK hint]
         ['IfK hint]
         ['LetK hint]
         ['LetrecK hint]
         ['kEvK hint]
         ['kLetK hint]
         ['kLetrecK hint]
         ['bind-args hint]
         ['bind-args-apply-pull hint]
         ['bind-args-apply hint]
         ['bind-rest-args-empty hint]
         ['bind-rest-args-rest hint]
         ['bind-rest-args-spill-value hint]
         ['bind-rest-args-spill-tail hint]
         ['bind-rest-args-bunch-tail hint]
         ['bind-rest-args-bunch-value hint]
         ['bind-rest-args-bunch-rest hint]
         ['bind-rest-args-pull hint]
         ['bind-rest-args hint]
         ['alloc-letrec hint]
         ['bind-let hint]
         ['rest-arg-call/cc-mandatory hint]
         ['rest-arg-call/cc-mandatory-tail hint]
         ['rest-arg-call/cc-rest hint]
         ['rest-arg-call/cc-rest-value hint]
         ['rest-arg-call/cc-rest-null hint]
         ['plain-call/cc-arg hint]
         ['cons-car hint]
         ['cons-cdr hint]
         ['box hint]))))

(module+ Scheme-concrete
  (provide (rename-out [expression-eval concrete-scheme-eval]))
  (define-values/invoke-unit/infer (link Scheme@ concrete-semantics@)))
(module+ Scheme-abstract
  (provide (rename-out [rule-eval abstract-scheme-eval])
           trace-update alloc L R)
  (define-values/invoke-unit/infer (export language-parms^ language-impl^)
    (link abstract-Scheme@ abstract-semantics@)))
