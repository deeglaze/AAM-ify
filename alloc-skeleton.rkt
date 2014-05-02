#lang racket/base
(require "spaces.rkt" racket/dict racket/match)
(provide alloc-skeleton)

;; Each allocation expression should be qualified with a distinct "hint" for
;; where the allocation is happening. Using the hint as the address itself is
;; too coarse, since every binding in the CESK machine would alias each other.
;; We need an additional piece of information to distinguish addresses based
;; on what is driving allocation, and not just where the allocation is taking place.

;; We can't use any component of ς blindly, since they can contain addresses,
;; which leads to a recursive address space, which leads to non-termination.
;; Instead, ???
;; alloc-skeleton : List[Rule] Map[MF-Name,Meta-function] → (values Alloc-Fn Syntax)
(define (alloc-skeleton abs-rules abs-Ξ)
  (values (λ (ς ρ [hint #f]) hint)
          #`(λ (ς ρ hint)
               (match-define (Abs-State term σ μ) ς)
               (match hint
                 #,@(alloc-hints abs-rules)
                 #,@(for*/list ([mf (in-dict-values abs-Ξ)]
                                #:unless (Meta-function-trusted-implementation/abs mf)
                                [hint (in-list (alloc-hints (Meta-function-rules)))])
                      hint)))))

;; Create all the clauses for a user to fill in with better hints than the hint themselves.
(define (alloc-hints rules)
  (for/list ([hint (in-list (rules-hints rules))])
    ;; quoted hint is the local variable introduced by alloc-skeleton.
    #`[(quasiquote #,(addr->syntax hint)) hint]))

(define (addr->syntax lst)
  (match lst
    ['() '()]
    [(cons (or (? symbol? s) (? pair? s)) lst)
     (cons s (addr->syntax lst))]
    [(cons (Variant-field name idx) lst)
     (cons #`(unquote (Variant-field (quote #,name) #,idx)) (addr->syntax lst))]))

(define (rules-hints rules)
  (hint-map (λ (rule tail)
               (match-define (Rule name lhs rhs bscs si) rule)
               (bscs-hints bscs tail))
            rules '()))

(define (hint-map f lst tail)
  (match lst
    ['() tail]
    [(cons a lst) (f a (hint-map f lst tail))]))

(define (bscs-hints bscs tail) (hint-map bsc-hints bscs tail))

(define (bsc-hints bsc tail)
  (match bsc
    [(or (Binding _ expr) (When expr)) (expression-hints expr tail)]
    [(Store-extend kexpr vexpr _) (expression-hints kexpr (expression-hints vexpr tail))]))

(define (expression-hints expr tail)
  (match expr
    [(or (Choose _ _ expr)
         (Store-lookup _ expr)
         (In-Dom? _ _ expr)
         (Set-empty? _ expr))
     (expression-hints expr tail)]
    [(or (? SAlloc?) (? MAlloc?))
     (error 'expression-hints "Unqualified allocation ~a" expr)]
    [(or (QSAlloc _ _ hint) (QMAlloc _ _ hint)) (cons hint tail)]
    [(or (Equal _ expr0 expr1)
         (Map-lookup _ _ expr0 _ expr1)
         (Map-extend _ _ expr0 expr1 _)
         (In-Set? _ expr0 expr1))
     (expression-hints expr0 (if expr1 (expression-hints expr1 tail) tail))]
    [(If _ g t e)
     (expression-hints g (expression-hints t (expression-hints e tail)))]
    [(Let _ bscs bexpr)
     (bscs-hints bscs (expression-hints bexpr tail))]
    [(or (Set-Union _ expr exprs)
         (Set-Add* _ expr exprs)
         (Set-Remove* _ expr exprs)
         (Set-Subtract _ expr exprs)
         (Set-Intersect _ expr exprs))
     (expression-hints expr (hint-map expression-hints exprs tail))]
    [(or (? Term?) (? Empty-set?) (? Boolean?) (? Meta-function-call?)) tail]
    [_ (error 'expression-hints "Unhandled expression ~a" expr)]))
