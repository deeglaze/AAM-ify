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
               (match-define (Abs-State term σ μ τ̂) ς)
               (match hint
                 #,@(alloc-hints abs-rules)
                 #,@(for*/list ([mf (in-dict-values abs-Ξ)]
                                #:unless (Meta-function-trusted-implementation/abs mf)
                                [hint (in-list (alloc-hints (Meta-function-rules mf)))])
                      hint)))))

;; Create all the clauses for a user to fill in with better hints than the hint themselves.
(define (alloc-hints RR)
  (match RR
    [(or (Reduction-Relation rules _) (? list? rules))
     (for/list ([hint (in-list (rules-hints rules))])
       ;; quoted hint is the local variable introduced by alloc-skeleton.
       #`[#,(addr->syntax hint) hint])]
    [_ (error 'alloc-hints "Bad reduction relation ~a" RR)]))

(define (addr->syntax addr)
  (define (recur addr under-quote? unquoted-since-qq?)
   (match addr
     ['() (if under-quote?
              (values '() unquoted-since-qq?)
              (values #''() #f))]
     [(or (? symbol?) (? number?) (? char?) (? string?))
      (if under-quote?
          (values addr unquoted-since-qq?)
          (values #`(quote #,addr) #f))]
     [(Variant-field name idx)
      (define pat #`(Variant-field '#,name '#,idx))
      (if under-quote?
          (values #`(#,#'unquote #,pat) #t)
          (values pat #f))]
     [(cons addr lst)
      (cond
       [under-quote?
        (define-values (addr-stx unq?) (recur addr #t unquoted-since-qq?))
        (define-values (lst-stx unq?*) (recur lst #t unq?))
        (values (cons addr-stx lst-stx) unq?*)]
       [else
        (define-values (addr-stx unq?) (recur addr #t #f))
        (define-values (lst-stx unq?*) (recur lst #t unq?))
        (if unq?*
            (values #`(quasiquote #,(cons addr-stx lst-stx)) #f)
            (values #`(quote #,(cons addr-stx lst-stx)) #f))])]
     [_ (error 'addr->syntax "Bad address ~a" addr)]))
  (define-values (stx dummy) (recur addr #f #f))
  stx)

(define (rules-hints rules [rtail '()])
  (hint-map (λ (rule tail)
               (match-define (Rule name lhs rhs (BSCS si bscs) _ _) rule)
               (bscs-hints bscs tail))
            rules rtail))

(define (hint-map f lst tail)
  (match lst
    ['() tail]
    [(cons a lst) (f a (hint-map f lst tail))]
    [_ (error 'hint-map "Bad list ~a" lst)]))

(define (bscs-hints bscs tail) (hint-map bsc-hints bscs tail))

(define (bsc-hints bsc tail)
  (match bsc
    [(or (Binding _ expr) (When expr)) (expression-hints expr tail)]
    [(Store-extend kexpr vexpr _) (expression-hints kexpr (expression-hints vexpr tail))]
    [_ (error 'bsc-hints "Bad BSC ~a" bsc)]))

(define (expression-hints expr tail)
  (match expr
    [(or (Choose _ _ _ expr)
         (Store-lookup _ _ expr)
         (In-Dom? _ _ _ expr)
         (Set-empty? _ _ expr))
     (expression-hints expr tail)]
    [(Alloc _ _ _ _ _ hint) (cons hint tail)]
    [(or (Equal _ _ expr0 expr1)
         (Map-lookup _ _ _ expr0 _ expr1)
         (Map-extend _ _ _ expr0 expr1 _)
         (In-Set? _ _ expr0 expr1))
     (expression-hints expr0 (if expr1 (expression-hints expr1 tail) tail))]
    [(If _ _ g t e)
     (expression-hints g (expression-hints t (expression-hints e tail)))]
    [(Let _ _ (BSCS _ bscs) bexpr)
     (bscs-hints bscs (expression-hints bexpr tail))]
    [(Match _ _ expr rules)
     (expression-hints expr (rules-hints rules tail))]
    [(or (Set-Union _ _ expr exprs)
         (Set-Add* _ _ expr exprs)
         (Set-Remove* _ _ expr exprs)
         (Set-Subtract _ _ expr exprs)
         (Set-Intersect _ _ expr exprs))
     (expression-hints expr (hint-map expression-hints exprs tail))]
    [(or (? Term?) (? Empty-set?) (? Meta-function-call?) (? ????)) tail]
    [_ (error 'expression-hints "Unhandled expression ~a" expr)]))
