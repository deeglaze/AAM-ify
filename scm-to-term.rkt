#lang racket
(require "spaces.rkt"
         "unparser.rkt"
         "shared.rkt"
         racket/trace
         (only-in "term-lattices.rkt" apply-reduction-relation*/∇ in-data)
         (submod "aam.rkt" Scheme-abstract)
         (only-in "shared.rkt" set-add* log-thread))
(provide file->term sexp->term run-file)

(define (file->term file)
  (sexp->term (define-ctx->sexp
                (with-input-from-file file
                  (λ () (for/list ([form (in-port read)]) form))))))

(define (split-improper-list l)
  (cond
   [(pair? l)
    (define-values (l* last) (split-improper-list (cdr l)))
    (values (cons (car l) l*) last)]
   [else (values '() l)]))

;; Return a Variant or the number of variants that were in the component
;; before hitting a dead end.
(define (find-nth-variant-in-Component C name n)
  (define (find-in-sequence seq n)
    (for/fold ([n n]) ([c seq])
      (define vn (find-nth-variant-in-Component c name n))
      #:final (Variant? vn)
      (if (Variant? vn)
          vn
          (- n vn))))
  (match C
    [(or (? Space-reference?) (? terminal-component?)) 0]
    [(∪ _ cs) (find-in-sequence (in-list cs) n)]
    [(℘ _ _ c) (find-in-sequence (in-value c) n)]
    [(Map _ _ d r) (find-in-sequence (in-list (list d r)) n)]
    [(Variant _ (== name eq?) comps _ _)
     (if (eq? n 0)
         C
         (find-in-sequence (in-vector comps) (sub1 n)))]
    [(Variant _ _ comps _ _)
     (find-in-sequence (in-vector comps) n)]))

(define (find-nth-variant name n [keys-in-order #f])
  (define spaces (Language-spaces L))
  (define seq
    (if keys-in-order
        (make-do-sequence (λ () (values (λ (lst) (hash-ref spaces (car lst)))
                                        cdr
                                        keys-in-order
                                        pair? #f #f)))
        (in-dict-values spaces)))
  (for/fold ([n n]) ([space seq]
                     #:when (User-Space? space))
      (define vn (find-nth-variant-in-Component (User-Space-component space) name n))
      #:final (Variant? vn)
      (if (Variant? vn)
          vn
          (- n vn))))
(define Scheme-order
  '(BAddr MAddr Variable Number String Char Symbol Variable-List Variable-List-Trusted
          Expr Primitive-name Predicate Numerics Data-operators Primitive Let-Clauses
          Letrec-tuples Expr-List Literal Bool Env Pre-value Value Address-List-Trusted
          Value-List-Trusted Value-List Frame Kont States
          ;; MF tuples unnecessary.
          ))
(define (find-variant name) (find-nth-variant name 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Not even going to attempt being hygienic.

(define (define-ctx->sexp sexp)
  (define (side-effectize exprs rev-clauses)
    (match exprs
      ['() rev-clauses]
      [(cons e exprs)
       (side-effectize exprs
                       (cons (list (gensym 'for-effect) e) rev-clauses))]))
  (let recur ([sexp sexp] [rev-clauses '()] [exprs-since-last-define '()])
    (match sexp
      [`((define (,f . ,rest) ,body) . ,more)
       (recur
        `((define ,f (lambda ,rest ,body)) . ,more)
        rev-clauses
        exprs-since-last-define)]
      [`((define ,f ,body) . ,more)
       (recur more
              (cons (list f body)
                    (side-effectize exprs-since-last-define rev-clauses))
              '())]
      [`(,e . ,more)
       (recur more rev-clauses (cons e exprs-since-last-define))]
      ['()
       (unless (pair? exprs-since-last-define)
         (error 'define-ctx->sexp "Expected an expression in the last position"))
       (define body
         (if (null? (cdr exprs-since-last-define))
             (car exprs-since-last-define)
             `(begin . ,exprs-since-last-define)))
       (if (null? rev-clauses)
           body
           `(letrec ,(reverse rev-clauses) ,body))])))

(define (get-space name) (hash-ref (Language-spaces L) name))
(define (sexp->term sexp)
  (define Variable (get-space 'Variable))
  (define (variable x) (external Variable x))
  (define (list->mono lst cons-variant)
    (match lst
      ['() (Datum '())]
      [(cons v lst) (variant cons-variant (vector v (list->mono lst cons-variant)))]))
  (define LCcons (find-variant 'LCcons))
  (define Econs (find-variant 'Econs))
  (define (self* sexp bound)
    (define (self sexp) (self* sexp bound))
    (define (mk-let-clauses xs rhss bound*)
      (for/fold ([lcclauses (Datum '())]) ([x (in-list (reverse xs))]
                                           [rhs (in-list (reverse rhss))])
        (variant LCcons (vector (variable x) (self* rhs bound*) lcclauses))))
    (match sexp
      [`(,(or 'lambda 'λ) ,formals . ,body)
       (define body* (self* (define-ctx->sexp body)
                            (cond [(list? formals) (set-add* bound formals)]
                                  [(symbol? formals) (set-add bound formals)]
                                  [else
                                   (define-values (mandatory r) (split-improper-list formals))
                                   (set-add* bound (cons r mandatory))])))
       (define VarCons (find-variant 'VarCons))
       (cond
        [(list? formals)
         (variant (find-variant 'Lam)
                  (vector (list->mono (map variable formals) VarCons)
                          body*))]
        [else
         (define RLam (find-variant 'RLam))
         (define-values (mandatory tail)
           (if (symbol? formals)
               (values '() formals)
               (split-improper-list formals)))
         (variant RLam (vector (list->mono (map variable mandatory)
                                           VarCons)
                               (variable tail)
                               body*))])]
      [`(if ,g ,t ,e)
       (variant (find-variant 'sIf) (vector (self g) (self t) (self e)))]
      [`(,(and head (or 'let 'letrec))
         ([,(? symbol? xs) ,rhss] ...) . ,body)
       (define bound-all (set-add* bound xs))
       (define-values (form bound-clauses bound-body)
         (if (eq? head 'let)
             (values (find-variant 'sLet) bound bound-all)
             (values (find-variant 'sLetrec) bound-all bound-all)))
       (variant form
                (vector
                 (mk-let-clauses xs rhss bound-clauses)
                 (self* (define-ctx->sexp body) bound-body)))]
      [`(begin ,e . ,es)
       (variant (find-variant 'Begin)
                (vector
                 (self e)
                 (list->mono (map self es) Econs)))]
      [`(quote ,d)
       (if (pair? d)
           (self `(cons (quote ,(car d)) (quote ,(cdr d))))
           (variant (find-variant 'Quote)
                    (vector (external (get-space (cond [(number? d) 'Number]
                                                       [(string? d) 'String]
                                                       [(char? d) 'Char]
                                                       [(symbol? d) 'Symbol]))
                                      d))))]
      [(or (? number? d) (? string? d) (? char? d))
       (self `(quote ,d))]
      [(? primitive? x) (variant (find-variant 'Prim) (vector (Datum x)))]
      [(? symbol? x)
       (unless (set-member? bound x)
         (error 'sexp->term "Unbound variable ~a" x))
       (variant (find-variant 'Ref) (vector (variable x)))]
      [`(,e . ,es)
       (variant (find-variant 'App)
                (vector (self e)
                        (list->mono (map self es) Econs)))]
      [_ (error 'sexp->term "Bad sexp ~a" sexp)]))
  (dtrace self*)
  (self* sexp ∅))

(define (primitive? x)
  (memq x '(null? string? procedure? vector? boolean? symbol? void? eof-object?
            zero? + - / * sub1
            box unbox set-box! make-vector vector vector-length vector-set! vector-ref
            cons car cdr
            void)))

(define apply-scheme (apply-reduction-relation*/∇ abstract-scheme-eval R))
(define (run-scheme term) (apply-scheme term))
(define (run-file file)
  (unless (procedure? alloc) (error 'run-file "Expected a definition of alloc ~a" alloc))
  (unless (procedure? trace-update) (error 'run-file "Expected a definition of trace-update ~a" trace-update))
  (define tm (file->term file))
  (define ς
    (mk-Abs-State (variant (find-variant 'Ev)
                                     (vector tm
                                             (ffun (User-Space-component (get-space 'Env)) ρ₀)
                                             (variant (find-variant 'Mt) #()))) tm))
  (printf "Starting state ~a~%" ς)
  (run-scheme ς))

(define (pretty-result seen)
  (for/hash ([(τ̂ state) (in-hash seen)])
    (values (unparse-pattern L τ̂)
            (match state
              [(Abs-State t σ μ τ̂)
               `(Abs-State ,(unparse-pattern L t)
                           ,(for/hash ([(space store) (in-hash σ)])
                              (values space
                                      (for/hash ([(a vs) (in-hash store)])
                                        (values a (for/set ([v (in-data vs)])
                                                    (unparse-pattern L v))))))
                           ,μ same-as-key)]))))

(module+ test
  (log-thread 'info #:file "log")

  (pretty-write
   (pretty-result
    (run-file "/home/ianj/projects/oaam/benchmarks/fact.sch"))))
