#lang racket/base
(require "spaces.rkt" "term-lattices.rkt" racket/match racket/dict racket/set racket/sequence)
(provide unparse-semantics unparse-language unparse-Ξ unparse-pattern)

(define (unparse-rule L rule)
  (match rule
    [(Rule name lhs rhs bscs _ _)
    `(Rule ,@(if name (list name) '())
           ,(unparse-pattern L lhs)
           ,(unparse-pattern L rhs)
           ,(unparse-bscs L bscs))]
   [_ (error 'unparse-rule "Bad rule ~a" rule)]))

(define (unparse-semantics L R)
  (match R
    [(Reduction-Relation rules _)
     (for/list ([rule (in-list rules)]) (unparse-rule L rule))]
    [_ (error 'unparse-semantics "Bad reduction relation ~a" R)]))
(define (unparse-language L)
  (match-define (Language spaces refinement-order options) L)
  `(Language ,(for/list ([(name space) (in-hash spaces)])
                (list name (unparse-lang-space space)))))

(define (unparse-Ξ L Ξ)
  (for/list ([mf (in-dict-values Ξ)])
    (unparse-metafunction L mf)))

(define (unparse-metafunction L mf)
  (match mf
    [(Meta-function name rules _ _ _)
     `(define-metafunction ,name . ,(for/list ([rule rules])
                                      (match (unparse-rule L rule)
                                        [`(Rule ,lhs ,rhs ,bscs)
                                         `[,lhs ,rhs ,bscs]])))]))

(define (unparse-pattern L p)
  (define (recur p)
    (match p
      [(Name x pat)
       (if (Anything? pat)
           x
           `(Name ,x ,(recur pat)))]
      [(is-a c) (unparse-Component c)]
      [(or (Rvar x) (Datum x) (external _ x) (Address _ x _ _)) x]
      [(ffun _ x) (for/hash ([(k v) (in-hash x)])
                    (values (recur k) (recur v)))]
      [(fset _ x) (for/set ([v (in-set x)]) (recur v))]
      [(or (? boolean?) (? Address?)) p]
      [(Set-with vpat spat mode _)
       `(Set-with ,(recur vpat) ,(recur spat) ,mode)]
      [(Map-with kpat vpat mpat mode _)
       `(Map-with ,(recur kpat) ,(recur vpat) ,(recur mpat) ,mode)]
      [(variant (Variant _ name _ _ _) pats)
       (cons name (for/list ([p (in-vector pats)]) (recur p)))]
      [(or (== -Anything eq?) (? Anything*?))
       '_]

      [(? Abs-Data? v)
       (cons 'Abs-Data (for/list ([x (in-data v)]) (recur x)))]
      [_ (error 'unparse-pattern "Bad pattern ~a" p)]))
  (recur p))

(define (unparse-bsc L bsc)
  (match bsc
    [(When e) `(when ,(unparse-expression L e))]
    [(Binding pat e) `(where ,(unparse-pattern L pat) ,(unparse-expression L e))]
    [(Store-extend ae ve strong?) `(update ,(unparse-expression L ae) ,(unparse-expression L ve) ,strong?)]
    [_ (error 'unparse-bsc "Bad bsc ~a" bsc)]))

(define (unparse-bscs L bscs)
  (match-define (BSCS _ bindings) bscs)
  (for/list ([bsc (in-list bindings)]) (unparse-bsc L bsc)))

(define (unparse-space L S)
  (match S
    [(? Space-reference?) (Space-reference-name S)]
    [(Address-Space space match-behavior equal-behavior)
     `(Address-Space ,space ,match-behavior ,equal-behavior)]
    [_ (or (for/or ([(name S*) (in-hash (Language-spaces L))]
                    #:when (equal? S S*))
              name)
            `(could-not-unparse ,S))]))

(define (unparse-lang-space S)
  (match S
    [(? Space-reference?) (Space-reference-name S)]
    [(Address-Space space match-behavior equal-behavior)
     `(Address-Space ,space ,match-behavior ,equal-behavior)]
    [(User-Space c _ _)
     `(User-Space . ,(match (unparse-Component c)
                       [`(∪ . ,rest) rest]
                       [other (list other)]))]
    [(External-Space pred card prec ≡ ⊔ enum _)
     `(External-Space ,(object-name pred)
                      ,(and card (object-name card))
                      ,prec
                      ,(and ≡ (object-name ≡))
                      ,(and ⊔ (object-name ⊔))
                      ,(and enum (object-name enum)))]
    [_ (error 'unparse-lang-space "Bad space ~a" S)]))

(define (unparse-Component comp)
  (match comp
    [(? Space-reference?) (Space-reference-name comp)]
    [(Map _ ex dom rng) `(Map ,ex ,(unparse-Component dom) ,(unparse-Component rng))]
    [(℘ _ ex comp) `(℘ ,ex ,(unparse-Component comp))]
    [(∪ _ comps) `(∪ . ,(map unparse-Component comps))]
    [(Variant _ name comps _ _)
     (cons name (for/list ([comp (in-vector comps)])
                  (unparse-Component comp)))]
    [(Anything* c) `(Anything* ,(unparse-Component c))]
    [(? Anything?) '_]
    [(Address-Space space match-behavior equal-behavior)
     `(Address-Space ,space ,match-behavior ,equal-behavior)]
    [(or (Datum atom) (? boolean? atom)) atom]
    [(? Bool?) 'Bool]
    [_ (error 'unparse-Component "Bad component ~a" comp)]))

(define (unparse-expression L e)
  (define (recur e)
    (match e
      [(Let _ _ bscs body) `(Let ,(unparse-bscs L bscs) ,(recur body))]
      [(Match _ _ d rules) `(Match ,(recur d) .
                                 ,(for/list ([rule (in-list rules)])
                                    (match (unparse-rule L rule)
                                      [(or `(Rule ,_ ,lhs ,rhs ,bscs)
                                           `(Rule ,lhs ,rhs ,bscs))
                                       (list* lhs rhs bscs)])))]
      [(Term _ _ pat) `(Term ,(unparse-pattern L pat))]
      [(Store-lookup _ _ k) `(Store-lookup ,(recur k))]
      [(If _ _ g t e) `(If ,(recur g) ,(recur t) ,(recur e))]
      [(Equal _ _ l r) `(Equal ,(recur l) ,(recur r))]
      [(Choose _ _ ℓ e) `(Choose ,ℓ ,(recur e))]
      [(Meta-function-call _ _ name pat) (cons name (unparse-pattern L pat))]
      [(Alloc _ _ space mb eb hint) `(Alloc ,space ,mb ,eb ,hint)]

      [(Map-lookup _ _ mvar k default? d)
       `(Map-lookup ,mvar ,(recur k) . ,(if d
                                                         (list (recur d))
                                                         '()))]
      [(Map-extend _ _ mvar k v strong?)
       `(Map-extend ,mvar ,(recur k) ,(recur v) ,strong?)]
      [(Map-remove _ _ mvar k)
       `(Map-remove ,mvar ,(recur k))]
      [(Empty-map _ mcomp)
       `(Empty-map ,(unparse-Component mcomp))]
      [(In-Dom? _ _ mvar k)
       `(In-Dom? ,mvar ,(recur k))]
      [(Map-empty? _ _ mvar)
       `(Map-empty? ,mvar)]

      [(Empty-set _ vcomp)
       `(Empty-set ,(unparse-Component vcomp))]
      [(Set-empty? _ _ e)
       `(Set-empty? ,(recur e))]
      [(In-Set? _ _ s v)
       `(In-Set? ,(recur s) ,(recur v))]
      [(or (Set-Union _ _ s ss)
            (Set-Add* _ _ s ss)
            (Set-Remove* _ _ s ss)
            (Set-Intersect _ _ s ss)
            (Set-Subtract _ _ s ss))
       `(,(object-name e) ,(recur s) . ,(map recur ss))]
      [(??? _ _ label)
       `(??? ,label)]
      [_ (error 'unparse-expression "Bad expression ~a" e)]))
  (recur e))
