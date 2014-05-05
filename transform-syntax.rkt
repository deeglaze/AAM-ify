#lang racket/base
(require (for-syntax syntax/parse racket/base)
         racket/match racket/set racket/fixnum
         "parser.rkt"
         "spaces.rkt"
         "transform.rkt")
(provide transform-semantics)

(define (update-store-interactions-b bs ΞΔ)
  (let recur ([bs bs] [rev-bs '()] [si pure] [Δ? #f])
    (match bs
      ['() (values (reverse rev-bs) si Δ?)]
      [(cons (When e) bs)
       (define-values (v Δ?*) (update-store-interactions-e e ΞΔ))
       (recur bs
              (cons (When v) rev-bs)
              (fxior si (expression-store-interaction v))
              (or Δ? Δ?*))]
      [(cons (Binding pat e) bs)
       (define-values (v Δ?*) (update-store-interactions-e e ΞΔ))
       (recur bs
              (cons (Binding pat v) rev-bs)
              (fxior si (expression-store-interaction v))
              (or Δ? Δ?*))]
      [(cons (Store-extend k v strong?) bs)
       (define-values (kv kΔ?) (update-store-interactions-e k ΞΔ))
       (define-values (vv vΔ?) (update-store-interactions-e v ΞΔ))
       (recur bs
              (cons (Store-extend kv vv strong?) rev-bs)
              (fxior si (combine kv vv))
              (or Δ? kΔ? vΔ?))])))

(define (update-store-interactions-e e ΞΔ)
  (define (bind oldv e fn [otherΔ? #f])
    (define-values (v Δ?) (recur e))
    (define v* (fn v))
    (values v* (or Δ?
                   (not (fx= (expression-store-interaction v*)
                             (expression-store-interaction oldv)))
                   otherΔ?)))

  (define (bind-lst oldv es fn [otherΔ? #f])
    (let recur ([es es] [es* '()] [Δ? otherΔ?] [si pure])
      (match es
        ['() (define v* (fn (reverse es*) si))
         (values v* (or Δ?
                        (not (fx= (expression-store-interaction v*)
                                  (expression-store-interaction oldv)))))]
        [(cons e es)
         (define-values (v Δ?*) (recur e))
         (recur es
                (cons v es*)
                (or Δ? Δ?*)
                (fxior si (expression-store-interaction v)))])))

  (define (recur e)
    (match e
    [(Term _ pattern) (values e #f)]
    [(Store-lookup si kexpr)
     (bind e kexpr
           (λ (k*)
              (Store-lookup (combine reads k*) k*)))]

    [(If si gu th el)
     (bind e gu
           (λ (g*)
              (bind e th
                    (λ (t*)
                       (bind e el
                             (λ (e*) (If (combine g* t* e*) g* t* e*)))))))]

    [(Let si bindings body)
     (define-values (bindings* si* Δ?)
       (update-store-interactions-b bindings ΞΔ))
     (bind e body
           (λ (b*) (Let (combine si* b*) bindings* b*))
           Δ?)]

    [(Equal _ lexpr rexpr)
     (bind e lexpr
           (λ (l*)
              (bind e rexpr
                    (λ (r*) (Equal (combine many l* r*) l* r*)))))]

    [(Meta-function-call si name arg-pat)
     (define si* (hash-ref ΞΔ name read/write/alloc/many))
     (values (Meta-function-call si* name arg-pat)
             (not (fx= si si*)))]

    [(Choose si ℓ ec)
     (bind e ec (λ (ec*) (Choose (combine many ec*) ℓ ec*)))]

;;; Map operations

    [(Map-lookup si m kexpr default? dexpr)
     (bind e kexpr
           (λ (k*)
              (cond
               [default?
                 (bind dexpr
                       (λ (d*) (Map-lookup (combine many k* d*) m k* #t d*)))]
               [else
                (Map-lookup (combine many k*) m k* #f #f)])))]

    [(Map-extend _ m kexpr vexpr trust-strong?)
     (bind e kexpr
           (λ (k*)
              (bind e vexpr
                    (λ (v*)
                       (Map-extend (combine k* v*) m k* v* trust-strong?)))))]

    [(Map-remove _ m kexpr) (error 'update-store-interactions-e "TODO map-remove")]
    [(Empty-map si container)
     (if (procedure? container)
         (values e #f)
         (bind e container (λ (c*) (Empty-map (combine c*) c*))))]
    ;; Map-empty? is at end

    [(In-Dom? _ mvar kexpr)
     (bind e kexpr
           (λ (k*) (In-Dom? (combine many k*) mvar k*)))]

;;; Set operations

    [(Empty-set si container)
     (if (procedure? container)
         (values e #f)
         (bind e container (λ (c*) (Empty-set (combine c*) c*))))]
    [(Set-empty? _ sexpr)
     (bind e sexpr
           (λ (s*) (Set-empty? (combine many s*) s*)))]

    [(In-Set? _ sexpr vexpr)
     (bind e sexpr
           (λ (s*)
              (bind e
                    (λ (v*)
                       (In-Set? (combine many s* v*) s* v*)))))]

    [(or (Set-Union _ set-expr sexprs)
         (Set-Add* _ set-expr sexprs)
         (Set-Remove* _ set-expr sexprs)
         (Set-Intersect _ set-expr sexprs)
         (Set-Subtract _ set-expr sexprs))
     (define container
       (cond [(Set-Union? e) (λ (si s* ss*) (Set-Union si s* ss*))]
             [(Set-Add*? e) (λ (si s* ss*) (Set-Union si s* ss*))]
             [(Set-Remove*? e) (λ (si s* ss*) (Set-Remove* (combine many reads si) s* ss*))]
             [(Set-Intersect? e) (λ (si s* ss*) (Set-Intersect (combine many reads si) s* ss*))]
             [(Set-Subtract? e) (λ (si s* ss*) (Set-Subtract (combine many reads si) s* ss*))]))
     (bind e set-expr
           (λ (s*)
              (bind-lst e sexprs (λ (ss* si) (container si s* ss*)))))]


    [(or (? SAlloc?) (? MAlloc?)) (error 'update-store-interactions-e "Bad abs-expr ~a" e)]

    [(or (? Boolean?) (? Unsafe-store-ref?) (? Unsafe-store-space-ref?)
         (? QSAlloc?) (? QSAlloc?) (? Map-empty??))
     (values e #f)]
    [_ (error 'update-store-interactions-e "Bad expression ~a" e)]))

  (recur e))

(define (update-store-interactions-r r ΞΔ)
  (match-define (Rule rule-name lhs rhs bscs si) r)
  (define-values (bscs* si* Δ?) (update-store-interactions-b bscs ΞΔ))
  (values (Rule rule-name lhs rhs bscs* si*) Δ?))

(define (update-store-interactions-mf mf ΞΔ)
  (match-define (Meta-function name rules si t/conc t/abs) mf)
  (cond
   [t/abs (values mf #f)]
   [else
    (define-values (rev-rules* si* Δ?)
      (for/fold ([rrules '()] [si pure] [Δ? #f]) ([rule (in-list rules)])
        (define-values (r Δ?*) (update-store-interactions-r rule ΞΔ))
        (values (cons r rrules) (fxior si (Rule-store-interaction r)) (or Δ? Δ?*))))
    (values (Meta-function name (reverse rev-rules*) si* t/conc #f)
            (or Δ? (not (fx= si si*))))]))

(define (stabilize-ΞΔ mfs ΞΔ)
  (define-values (mfs* Δ? ΞΔ*)
    (for/fold ([mfs ρ₀] [Δ? #f] [ΞΔ ΞΔ])
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
    [(_ L:Lang red:expr)
     (syntax/loc stx
       (let*-values ([(rL) (reify-language L)]
                     [(abs-lang rec-addrs abstract-spaces)
                      (abstract-language rL)]
                     [(mfs ΞΔ)
                      (for/fold ([mfs ρ₀] [ΞΔ ρ₀])
                          ([(name mf) (in-hash (reify-metafunctions-of L))])
                        (define mf* (abstract-meta-function rec-addrs ρ₀ mf))
                        (values (hash-set mfs name mf*)
                                (hash-set ΞΔ name (Meta-function-store-interaction mf*))))]
                     [(mfs* ΞΔ*) (stabilize-ΞΔ mfs ΞΔ)])
         (printf "Rec-addrs ~a~%" rec-addrs)
         (printf "Abstract spaces ~a~%" abstract-spaces)
         (values abs-lang
                 mfs*
                 (for/list ([rule (in-list red)])
                   (abstract-rule abs-lang rec-addrs ΞΔ* rule)))))]))
