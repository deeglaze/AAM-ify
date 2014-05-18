#lang racket/base
(require (for-syntax syntax/parse racket/base syntax/parse/experimental/template
                     "spaces.rkt")
         racket/match racket/set racket/fixnum
         racket/trace
         "parser.rkt"
         "spaces.rkt" "space-ops.rkt"
         "transform-language.rkt"
         "transform-semantics.rkt")
(provide transform-semantics)

(define (update-store-interactions-b bs ΞΔ)
  (match-define (BSCS si bindings) bs)
  (define-values (rev-bs si* Δ?)
    (for/fold ([rev-bs '()] [si* pure] [Δ? #f])
        ([binding (in-list bindings)])
      (match binding
        [(When e)
         (define-values (v Δ?*) (update-store-interactions-e e ΞΔ))
         (values (cons (When v) rev-bs)
                 (combine si v)
                 (or Δ? Δ?*))]
        [(Binding pat e)
         (define-values (v Δ?*) (update-store-interactions-e e ΞΔ))
         (values (cons (Binding pat v) rev-bs)
                 (combine si v)
                 (or Δ? Δ?*))]
        [(Store-extend k v strong?)
         (define-values (kv kΔ?) (update-store-interactions-e k ΞΔ))
         (define-values (vv vΔ?) (update-store-interactions-e v ΞΔ))
         (values (cons (Store-extend kv vv strong?) rev-bs)
                 (combine si kv vv)
                 (or Δ? kΔ? vΔ?))])))
  (values (BSCS si* (reverse rev-bs)) (or Δ? (not (fx= si* si)))))

(define (update-store-interactions-e e ΞΔ)
  (define (bind oldv e fn [otherΔ? #f])
    (define-values (v Δ?) (recur e))
    (define-values (v* Δ?*)
      (call-with-values (λ () (fn v))
        (case-lambda
          [(v*) (values v* #f)]
          [(v* Δ?*) (values v* Δ?*)])))
    (values v* (or Δ? Δ?*
                   (not (fx= (combine v*)
                             (combine oldv)))
                   otherΔ?)))

  (define (bind-lst oldv es fn [otherΔ? #f])
    (let recur ([es es] [es* '()] [Δ? otherΔ?] [si pure])
      (match es
        ['() (define v* (fn (reverse es*) si))
         (values v* (or Δ?
                        (not (fx= (combine v*)
                                  (combine oldv)))))]
        [(cons e es)
         (define-values (v Δ?*) (recur e))
         (recur es
                (cons v es*)
                (or Δ? Δ?*)
                (fxior si (combine v)))])))

  (define (recur e)
    (match e
      [(Store-lookup si c kexpr)
       (bind e kexpr
             (λ (k*)
                (Store-lookup (combine reads k*) c k*)))]

      [(If si c gu th el)
       (bind e gu
             (λ (g*)
                (bind e th
                      (λ (t*)
                         (bind e el
                               (λ (e*) (If (combine g* t* e*) c g* t* e*)))))))]

      [(Let si c bindings body)
       (define-values (bindings* Δ?)
         (update-store-interactions-b bindings ΞΔ))
       (bind e body
             (λ (b*) (Let (combine bindings* b*) c bindings* b*))
             Δ?)]

      [(Match si c disc rules)
       (bind e disc
             (λ (e*)
                (define-values (rules* si* Δ?)
                  (for/fold ([rev-rules '()] [si* pure] [Δ? #f])
                      ([rule (in-list rules)])
                    (define-values (rule* Δ?*)
                      (update-store-interactions-r rule ΞΔ))
                    (values (cons rule* rev-rules)
                            (combine si* rule*)
                            (or Δ? Δ?*))))
                (values (Match (combine e* si*) c e* rules*) Δ?)))]

      [(Equal _ c lexpr rexpr)
       (bind e lexpr
             (λ (l*)
                (bind e rexpr
                      (λ (r*) (Equal (combine many l* r*) c l* r*)))))]

      [(Meta-function-call si c name arg-pat)
       (define si* (hash-ref ΞΔ name read/write/alloc/many))
       (values (Meta-function-call si* c name arg-pat)
               (not (fx= si si*)))]

      [(Choose si c ℓ ec)
       (bind e ec (λ (ec*) (Choose (combine many ec*) c ℓ ec*)))]

;;; Map operations

      [(Map-lookup si c m kexpr default? dexpr)
       (bind e kexpr
             (λ (k*)
                (cond
                 [default?
                   (bind dexpr
                         (λ (d*) (Map-lookup (combine many k* d*) c m k* #t d*)))]
                 [else
                  (Map-lookup (combine many k*) c m k* #f #f)])))]

      [(Map-extend _ c m kexpr vexpr trust-strong?)
       (bind e kexpr
             (λ (k*)
                (bind e vexpr
                      (λ (v*)
                         (Map-extend (combine k* v*) c m k* v* trust-strong?)))))]

      [(Map-remove _ c m kexpr)
       (bind e kexpr
             (λ (k*) (Map-remove (combine reads many k*) c m k*)))]
      ;; Map-empty? is at end

      [(In-Dom? _ c mvar kexpr)
       (bind e kexpr
             (λ (k*) (In-Dom? (combine reads many k*) c mvar k*)))]

;;; Set operations

      [(Set-empty? _ c sexpr)
       (bind e sexpr
             (λ (s*) (Set-empty? (combine many s*) c s*)))]

      [(In-Set? _ c sexpr vexpr)
       (bind e sexpr
             (λ (s*)
                (bind e
                      (λ (v*)
                         (In-Set? (combine reads many s* v*) c s* v*)))))]

      [(or (Set-Union _ c set-expr sexprs)
           (Set-Add* _ c set-expr sexprs)
           (Set-Remove* _ c set-expr sexprs)
           (Set-Intersect _ c set-expr sexprs)
           (Set-Subtract _ c set-expr sexprs))
       (define container
         (cond [(Set-Union? e) (λ (si s* ss*) (Set-Union si c s* ss*))]
               [(Set-Add*? e) (λ (si s* ss*) (Set-Union si c s* ss*))]
               [(Set-Remove*? e) (λ (si s* ss*) (Set-Remove* (combine many reads si) c s* ss*))]
               [(Set-Intersect? e) (λ (si s* ss*) (Set-Intersect (combine many reads si) c s* ss*))]
               [(Set-Subtract? e) (λ (si s* ss*) (Set-Subtract (combine many reads si) c s* ss*))]))
       (bind e set-expr
             (λ (s*)
                (bind-lst e sexprs (λ (ss* si) (container si s* ss*)))))]


      [(or (? Unsafe-store-ref?) (? Unsafe-store-space-ref?)
           (? Alloc?) (? Map-empty??) (? Term?) (? Empty-set?) (? Empty-map?) (? ????))
       (values e #f)]
      [_ (error 'update-store-interactions-e "Bad expression ~a" e)]))

  (recur e))

(define (update-store-interactions-r r ΞΔ)
  (match-define (Rule rule-name lhs rhs bscs lexpect rexpect) r)
  (define-values (bscs* Δ?) (update-store-interactions-b bscs ΞΔ))
  (values (Rule rule-name lhs rhs bscs* lexpect rexpect) Δ?))

(define (update-store-interactions-mf mf ΞΔ)
  (match-define (Meta-function name rules si t/conc t/abs) mf)
  (cond
   [t/abs (values mf #f)]
   [else
    (define-values (rev-rules* si* Δ?)
      (for/fold ([rrules '()] [si pure] [Δ? #f]) ([rule (in-list rules)])
        (define-values (r Δ?*) (update-store-interactions-r rule ΞΔ))
        (values (cons r rrules) (fxior si (BSCS-store-interaction
                                           (Rule-binding-side-conditions r))) (or Δ? Δ?*))))
    (values (Meta-function name (reverse rev-rules*) si* t/conc #f)
            (or Δ? (not (fx= si si*))))]))

(define (stabilize-ΞΔ mfs ΞΔ)
  (define-values (mfs* Δ? ΞΔ*)
    (for/fold ([mfs mfs] [Δ? #f] [ΞΔ ΞΔ])
        ([(name mf) (in-hash mfs)])
      (define-values (mf* Δ?*) (update-store-interactions-mf mf ΞΔ))
      (if Δ?*
          (values (hash-set mfs name mf*)
                  #t
                  (hash-set ΞΔ name (Meta-function-store-interaction mf*)))
          (values mfs Δ? ΞΔ))))
  (if Δ?
      (stabilize-ΞΔ mfs* ΞΔ*)
      (values mfs* ΞΔ*)))

;; TODO: lift to syntax level to provide better errors.
(define-syntax (transform-semantics stx)
  (syntax-parse stx
    [(_ L:Lang
        (~var op (Options-cls (Language-options (attribute L.langv))))
        red:expr (~optional (~seq #:hint-relabeling ([hints:expr hint*s:expr] ...))))
     ;; TODO: incorporate relabeling into transformation and warn/error when
     ;; a hint is specified but not generated.
     (with-syntax ([options (quine-Options (attribute op.value))])
      (quasisyntax/loc stx
        (let*-values ([(rL) (reify-language L.id)]
                      [(rspaces) (Language-spaces rL)]
                      [(abs-lang)
                       (abstract-language rL options)]
                      [(relabeling)
                       (hash . #,(reverse (for/fold ([acc '()])
                                              ([hint (in-list (or (attribute hints) '()))]
                                               [hint* (in-list (or (attribute hint*s) '()))])
                                            (list* hint* hint acc))))]
                      [(mfs ΞΔ)
                       (for/fold ([mfs ρ₀] [ΞΔ ρ₀])
                           ([(name mf) (in-hash (reify-metafunctions-of L.id))])
                         (define mf* (abstract-meta-function abs-lang ρ₀ relabeling mf
                                                             #:options options))
                         (values (hash-set mfs name mf*)
                                 (hash-set ΞΔ name (Meta-function-store-interaction mf*))))]
                      [(mfs* ΞΔ*) (stabilize-ΞΔ mfs ΞΔ)])
          (match-define (Abs-Language _ rec-addrs rec-spaces abs-spaces nonrec-spaces) abs-lang)
          (printf "Recursive addresses ~a~%Recursive spaces ~a~%Abstract spaces ~a~%Nonrecursive spaces ~a~%"
                  rec-addrs rec-spaces abs-spaces nonrec-spaces)
          (define R red)
          (match R
            [(Reduction-Relation rules expect-space)
             (values
              abs-lang
              mfs*
              (Reduction-Relation
               (for/list ([rule (in-list rules)]
                          [i (in-naturals)])
                 (abstract-rule abs-lang ΞΔ* rule i relabeling
                                #:options options))
               (and expect-space
                    ((replace-recursive-mentions options nonrec-spaces rec-spaces #f)
                     expect-space))))]
            [_ (error 'transform-semantics "Expected a reduction relation, got ~a" R)]))))]))
