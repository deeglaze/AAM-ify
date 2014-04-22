#lang racket/base

#|
Language forms require extra annotations for performance reasons.
These annotations are easy for a program to perform, but annoying for humans.

This module defines a syntactic front-end to defining languages,
their semantics and associated meta-functions.

A plus to using syntax is that errors can use syntax-location.

Languages are special since they introduce several names that will be
used by rules, expressions, patterns and meta-functions. As such,
not only will parsed languages produce the expected Language value with
maps of symbols to spaces, but also a syntax-time value for associating
identifiers for syntax errors.

TODO?: Add binding arrows using DrRacket's API
|#
(require "spaces.rkt" "shared.rkt" 
         racket/match racket/dict racket/set racket/promise racket/vector
         syntax/parse racket/syntax syntax/id-table
         syntax/parse/experimental/template
         racket/fixnum
         (for-syntax syntax/parse racket/base))
(provide parse-language
         parse-rules)


(struct with-orig-stx (v core surface-stx) #:transparent)

(define/match (unwrap-wos s) [((with-orig-stx s* _ _)) s*] [(_) s])
(define (flatten-space space)  
  (match (unwrap-wos space)
    [(User-Space variants trust-recursion? trust-construction?)
     (User-Space (for/list ([v (in-list variants)])
                   (define v* (unwrap-wos v))
                   (if (Variant? v*)
                       (flatten-Variant v*)
                       (flatten-Component v*)))
                 trust-recursion?
                 trust-construction?)]
    [(or (? External-Space? unw) (? Address-Space? unw)) unw]))

;; Parsed values are comprised of syntax objects.
(define (flatten-pattern pat)
  (define pat* (unwrap-wos pat))
  (define (flatten-map m)
    (for/hash ([(k v) (in-dict map)])
      (values (flatten-pattern k) (flatten-pattern v))))
  (match pat*
    [(Bvar id space)
     (Bvar (syntax-e id) (flatten-space space))]
    [(Rvar id) (Rvar (syntax-e id))]
    [(variant var pats)
     (define pats* (unwrap-wos pats))
     (variant (flatten-Variant var)
              (for/vector #:length (vector-length pats)
                          ([p (in-vector pats)])
                          (flatten-pattern p)))]
    [(abstract-ffun map) (abstract-ffun (flatten-map map))]
    [(discrete-ffun map) (discrete-ffun (flatten-map map))]
    [(? dict? map) (flatten-map map)]
    [(? set? pats)
     (for/set ([p (in-set pats)]) (flatten-pattern p))]
    [(Address-Structural space addr)
     (Address-Structural (syntax-e space) (if (syntax? addr)
                                              (syntax->datum addr)
                                              addr))]
    [(Address-Egal space addr)
     (Address-Egal (syntax-e space) (if (syntax? addr)
                                        (syntax->datum addr)
                                        addr))]
    [atom atom]))

(define (flatten-Variant v)
  (match (unwrap-wos v)
    [(Variant name comps)
     (define comps* (unwrap-wos comps))
     (Variant (syntax-e name)
              (for/vector #:length (vector-length comps)
                          ([comp (in-vector comps)])
                (flatten-Component comp)))]))

(define (flatten-Component c)
  (match (unwrap-wos c)
    [(Space-reference name) (Space-reference (syntax-e name))]
    [(Map dom rng) (Map (flatten-Component dom) (flatten-Component rng))]
    [(℘ comp) (flatten-Component comp)]
    [(or (? Anything? unw) (? Address-Space? unw)) unw]))

(define/match (flatten-language L)
  [((Language name spaces refinement-order))
   (Language (syntax-e name)
             (let loop ([itr (free-id-table-iterate-first spaces)]
                        [h #hash()])
               (if itr
                   (loop (free-id-table-iterate-next spaces itr)
                         (hash-set h
                                   (syntax-e (free-id-table-iterate-key spaces itr))
                                   (flatten-space (free-id-table-iterate-value spaces itr))))
                   h))
             refinement-order)])

(define (choose-best orig-stx order v0 ns0 nl0 v1 ns1 nl1)
  (if
   (error 'choose-best "TODO: add syntax for refinement ordering, and implement max.")
   (values v0 ns0 nl0)
   (values v1 ns1 nl1)))

(define (free-id-table-has-key? t k)
  (not (eq? (free-id-table-ref t k -unmapped) -unmapped)))

(define-syntax-class (Space-ref L)
  #:attributes (value)
  (pattern space-name:id
           #:do [(define spacev (free-id-table-ref (car L) #'space-name -unmapped))]
           #:fail-when (eq? -unmapped spacev) (format "Unknown space ~a" (syntax-e #'space-name))
           #:attr value spacev))

 (define-syntax (Setof stx)
   (raise-syntax-error #f "To be used as Component syntax" stx))

 (define-syntax (Any stx)
   (raise-syntax-error #f "To be used as Component syntax" stx))

(define-literal-set expr-ids
  (Term
   Map-lookup
   Map-extend
   Store-lookup
   If
   Let
   Equal
   In-Dom
   Empty-set
   Set-Union
   Set-Add*
   In-Set
   Meta-function-call
   Store-extend
   SAlloc
   MAlloc
   QSAlloc
   QMAlloc
   Unsafe-store-ref
   Unsafe-store-space-ref))

(define-literal-set component-lits
  (Address-Space ℘ Setof Map Any))

(define-literal-set pat-ids
  (Bvar
   Rvar
   variant))


;; pats are passed in unparsed.
;; If expected-space is non-#f, we check that (vname . pats) matches the given space.
;; Otherwise, we find the most suitable Variant in the language. If multiple Variant values
;; match, we choose the most general one according to the user's specification of a refinement order.
;; If there is no given order, we raise an error.
(define (find-suitable-variant L orig-stx expected-space vname pats pattern? bound-vars)
  (define (check-space s [on-fail (λ () (values #f #f #f))])
    (match-define (User-Space v-or-cs _ _) s)
    (let search ([v-or-cs v-or-cs])
      (match v-or-cs
        ['() (on-fail)]
        [(cons (and v/orig (with-orig-stx (and v (Variant (== vname free-identifier=?) _)) core _))
               v-or-cs)
         (syntax-parse pats
           [(~var ps (Patterns L (vector->list (Variant-Components v)) pattern? bound-vars))
            (values
             (with-orig-stx (variant v/orig (list->vector (attribute ps.values)))
                            #`(variant #,core
                                       (vector #,@(map with-orig-stx-core (attribute ps.values))))
                            orig-stx)
             (attribute ps.new-scope)
             (attribute ps.non-linear?))]
           [_ (search v-or-cs)])]
        [(cons _ v-or-cs) (search v-or-cs)])))
  (cond
   [expected-space
    (define (fail)
      (raise-syntax-error
       #f
       (format "Variant pattern did not match expected space (~a)" expected-space)
       orig-stx))
    (check-space expected-space fail)]
   [else
    (match-define (Language _ spaces order) L)
    (let search ([itr (free-id-table-iterate-first spaces)]
                 [best #f]
                 [best-new-scope #f]
                 [best-non-linear? #f])
      (cond
       [itr
        (define s (free-id-table-iterate-value spaces itr))
        (define-values (v ns nl?) (check-space s))
        (define-values (b* bns* bnl*)
          (cond
           [v
            (cond
             [best
              (choose-best orig-stx order v ns nl? best best-new-scope best-non-linear?)]
             [else (values v ns nl?)])]
           [else (values best best-new-scope best-non-linear?)]))
        (search (free-id-table-iterate-next spaces itr) b* bns* bnl*)]
       [else
        (unless best
          (raise-syntax-error #f "Variant did not match language" orig-stx))
        (values best best-new-scope best-non-linear?)]))]))

(define-syntax-class (Patterns L expected-spaces pattern? bound-vars)
  #:attributes (values non-linear? new-scope)
  (pattern ()
           #:fail-unless (null? expected-spaces) 
           (format "Expected more components ~a" expected-spaces)
           #:attr values '()
           #:attr non-linear? #f
           #:attr new-scope bound-vars)
  (pattern ((~var p (Pattern L (car expected-spaces)
                             pattern? bound-vars))
            .
            (~var ps (Patterns L (cdr expected-spaces)
                               pattern?
                               (attribute p.new-scope))))
           #:attr values (cons (attribute p.value) (attribute ps.values))
           #:attr non-linear? (or (attribute p.non-linear?) (attribute ps.non-linear?))
           #:attr new-scope (attribute ps.new-scope)))

;; Patterns and terms are similar. Rvars are allowed in terms, Bvars in patterns.
(define-syntax-class (Pattern L expected-space pattern? bound-vars)
  #:literal-sets (pat-ids)
  #:attributes (value non-linear? new-scope)
  (pattern (Bvar v:id (~optional (~var S (Space-ref L))))
           #:fail-unless pattern? "Terms may not use Bvar. Not in binding context."
           #:fail-when (and expected-space
                            (attribute S.value)
                            (not (equal? expected-space (attribute S.value))))
           (format "Expected space ~a but binder expects ~a" expected-space (attribute S.value))
           #:attr value (with-orig-stx
                         (Bvar (syntax-e #'v) (attribute S.value))
                         #`(Bvar 'v #,(and (attribute S)
                                           (with-orig-stx-core (attribute S.value))))
                         #'orig-stx)
           #:attr non-linear? (free-id-table-has-key? bound-vars #'v)
           #:attr new-scope (free-id-table-set bound-vars #'v #t))
  (pattern (~and orig-stx (Rvar v:id))
           #:fail-when pattern? "Patterns may not use Rvar. Use Bvar for non-linear patterns"
           #:attr value (with-orig-stx (Rvar (syntax-e #'v))
                                       #'(Rvar 'v)
                                       #'orig-stx)
           #:attr non-linear? #f
           #:attr new-scope bound-vars)

  (pattern (~and orig-stx (vname:id ps:expr ...))
           #:do [(define-values (var found-new-scope found-non-linear?)
                   (find-suitable-variant L #'orig-stx expected-space #'vname (syntax->list #'(ps ...))
                                          pattern?
                                          bound-vars))]
           #:attr value var
           #:attr non-linear? found-non-linear?
           #:attr new-scope found-new-scope))

;; Simple syntax for finite functions / maps
(define-syntax-class mapsto [pattern (~or (~datum ->) (~datum →) (~datum ↦))])

(define-syntax-class (Component-cls Space-names)
  #:attributes (value)
  #:literal-sets (component-lits)
  #:local-conventions ([#rx".*-c$" (Component-cls Space-names)])
  (pattern (~and orig-stx
                 (~or
                  (dom-c arr:mapsto rng-c)
                  ((~or arr:mapsto Map) dom-c rng-c)))
           #:attr value
           (with-orig-stx (Map (attribute dom-c.value) (attribute rng-c.value))
                          #`(Map #,(with-orig-stx-core (attribute dom-c.value))
                                 #,(with-orig-stx-core (attribute rng-c.value)))
                          #'orig-stx))
  (pattern (~and orig-stx (Address-Space space:id))
           #:attr value (with-orig-stx
                         (Address-Space (syntax-e #'space))
                         #'(Address-Space 'space)
                         #'orig-stx))
  (pattern (~and orig-stx ((~or ℘ Setof) s-c))
           #:attr value (with-orig-stx
                         (℘ (attribute s-c.value))
                         #`(℘ #,(with-orig-stx-core (attribute s-c.value)))
                         #'orig-stx))
  (pattern (~and orig-stx (~or (~literal _) Any))
           #:attr value (with-orig-stx -Anything #'-Anything #'orig-stx))
  (pattern space:id
           #:fail-unless (free-id-table-has-key? Space-names #'space)
           (format "Unknown space ~a" (syntax-e #'space))
           #:attr value (with-orig-stx (Space-reference #'space)
                                       #'(Space-reference 'space)
                                       #'space)))

(define-syntax-class (Variant-cls Space-names)
  #:attributes (value)
  (pattern (~and orig-stx (constructor:id (~var cs (Component-cls Space-names)) ...))
           #:attr value 
           (with-orig-stx (Variant #'constructor (list->vector (attribute cs.value)))
                          #`(Variant 'constructor (vector #,@(map with-orig-stx-core (attribute cs.value))))
                          #'orig-stx)))

(define-syntax-class (variant-or-component Space-names)
  #:attributes (value)
  (pattern (~var c (Component-cls Space-names))
           #:attr value (attribute c.value))
  (pattern (~var v (Variant-cls Space-names))
           #:attr value (attribute v.value)))

(define-syntax-class (Space-inhabitants Space-names)
  #:attributes (value)
  ;; A User space is a sequence of variants
  (pattern (~and orig-stx
                 ((~or (~var vcs (variant-or-component Space-names))
                       (~optional (~and #:trust-recursion trust-rec))
                       (~optional (~and #:trust-construction trust-con))
                       ) ...))
           #:attr value
           (with-orig-stx (User-Space (attribute vcs.value)
                                      (syntax? (attribute trust-rec))
                                      (syntax? (attribute trust-con)))
                          #`(User-Space (list #,@(map with-orig-stx-core (attribute vcs.value)))
                                        #,(syntax? (attribute trust-rec))
                                        #,(syntax? (attribute trust-con)))
                          #'orig-stx))
  (pattern (~and orig-stx
                 (#:external-space pred:expr
                                   (~or (~optional (~seq #:cardinality card:expr))
                                        (~optional (~and precision
                                                         (~or #:abstract #:discrete #:concrete)))
                                        (~optional (~seq #:equality equality:expr))) ...))
           #:attr value
           (with-orig-stx
            (External-Space (eval-syntax #'pred)
                            (and (attribute card) (eval-syntax #'card))
                            (if (attribute precision) (syntax-e #'precision) 'abstract)
                            (and (attribute equality) (eval-syntax #'equality)))
            (template
             (External-Space pred (?? card #f) (?? precision 'abstract) (?? equality #f)))
            #'orig-stx))
  (pattern (~and orig-stx (#:address-space tag:id))
           #:attr value (with-orig-stx (Address-Space (syntax-e #'tag))
                                       #'(Address-Space 'tag)
                                       #'orig-stx)))
;; FIXME: add refinement-order parsing
 (define (parse-language stx)
  (syntax-parse stx
    [(_ name:id [space-name:id ss ...] ...
        (~do (define Space-names
               (for/fold ([t (make-immutable-free-id-table)])
                   ([sn (in-list (attribute space-name))])
                 (free-id-table-set t sn #t))))
        (~parse ((~var inh (Space-inhabitants Space-names)) ...) #'((ss ...) ...)))
     (Language #'name
               (for/fold ([t (make-immutable-free-id-table)])
                   ([sn (in-list (attribute space-name))]
                    [space (in-list (attribute inh.value))])
                 (free-id-table-set t sn space))
               #f)]))

(define-syntax (--> stx) (raise-syntax-error #f "For use in Rule form" stx))

(define-syntax-class (Expression L bound-vars)
  #:attributes (value)
  #:literal-sets (expr-ids)
  #:local-conventions ([t (Pattern L #f #f bound-vars)]
                       [#rx".*-e$" (Expression L bound-vars)])
  (pattern (~and orig-stx (Term t))
           #:attr value (with-orig-stx
                         (Term pure (attribute t.value))
                         #`(Term #,pure (with-orig-stx-core (attribute t.value)))
                         #'orig-stx))
  (pattern (~and orig-stx v:boolean)
           #:attr value (with-orig-stx
                         (Boolean pure (syntax-e #'v))
                         #`(Boolean #,pure v)
                         #'orig-stx))
  (pattern (~and orig-stx (Map-lookup m:id k-e (~optional (~seq #:default d-e))))
           #:fail-unless (free-id-table-has-key? bound-vars #'m)
           (format "Unbound map variable ~a" (syntax-e #'m))
           #:do [(define default? (not (not (attribute d-e))))
                 (define tag
                   (add-many ;; approximate domain can lead to many lookups
                    (fxior (expression-store-interaction (attribute k-e.value))
                           (if default?
                               (expression-store-interaction (attribute d-e.value))
                               0))))]
           #:attr value (with-orig-stx
                         (Map-lookup
                          tag
                          (syntax-e #'m) (attribute k-e.value)
                          (not (not (attribute d-e)))
                          (attribute d-e.value))
                         (quasitemplate
                          (Map-lookup #,tag
                                      'm
                                      #,(with-orig-stx-core (attribute k-e.value))
                                      #,(not (not (attribute d-e)))
                                      #,(and (attribute d-e)
                                             (with-orig-stx-core (attribute d-e.value)))))
                         #'orig-stx))
  (pattern (~and orig-stx (Map-extend m:id k-e v-e (~optional (~and #:trust-strong trust))))
           #:fail-unless (free-id-table-has-key? bound-vars #'m)
           (format "Unbound map variable ~a" (syntax-e #'m))
           #:do [(define tag
                   (add-many ;; approximate domain can lead to multiple extensions.
                    (fxior (expression-store-interaction (attribute k-e.value))
                           (expression-store-interaction (attribute v-e.value)))))]
           #:attr value (with-orig-stx
                         (Map-extend tag (syntax-e #'m)
                                     (attribute k-e.value)
                                     (attribute v-e.value)
                                     (syntax? (attribute trust)))
                         #`(Map-extend #,tag
                                       'm
                                       #,(with-orig-stx-core (attribute k-e.value))
                                       #,(with-orig-stx-core (attribute v-e.value))
                                       #,(syntax? (attribute trust)))
                         #'orig-stx))
  (pattern (~and orig-stx (Store-lookup k-e))
           #:do [(define tag (add-reads (expression-store-interaction (attribute k-e.value))))]
           #:attr value (with-orig-stx
                         (Store-lookup tag (attribute k-e.value))
                         #`(Store-lookup #,tag #,(with-orig-stx-core (attribute k-e.value)))
                         #'orig-stx))
  (pattern (~and orig-stx (If g-e t-e e-e))
           #:do [(define tag (fxior (expression-store-interaction (attribute g-e))
                                    (fxior (expression-store-interaction (attribute t-e))
                                           (expression-store-interaction (attribute e-e)))))]
           #:attr value (with-orig-stx
                         (If tag (attribute g-e.value) (attribute t-e.value) (attribute e-e.value))
                         #`(If #,tag
                               #,(with-orig-stx-core (attribute g-e.value))
                               #,(with-orig-stx-core (attribute t-e.value))
                               #,(with-orig-stx-core (attribute e-e.value)))
                         #'orig-stx))
  (pattern (~and orig-stx (Let (~var bscs (Bindings L bound-vars))
                               (~var body (Expression L (attribute bscs.new-scope)))))
           #:do [(define tag (fxior (attribute bscs.interaction)
                                    (expression-store-interaction (attribute body.value))))]
           #:attr value
           (with-orig-stx (Let tag (attribute bscs.value) (attribute body.value))
                          #`(Let #,tag
                                 #,(with-orig-stx-core (attribute bscs.value))
                                 #,(with-orig-stx-core (attribute body.value)))
                          #'orig-stx))
  (pattern (~and orig-stx (Equal l-e r-e))
           #:do [(define tag ;; can fail and can be approximate.
                   (fxior 9  ;; read/many
                          (fxior (expression-store-interaction (attribute l-e.value))
                                 (expression-store-interaction (attribute r-e.value)))))]
           #:attr value
           (with-orig-stx
            (Equal tag (attribute l-e.value) (attribute r-e.value))
            #`(Equal #,tag
                     #,(with-orig-stx-core (attribute l-e.value))
                     #,(with-orig-stx-core (attribute r-e.value)))
            #'orig-stx))
  (pattern (~and orig-stx (Empty-set))
           #:attr value (with-orig-stx (Empty-set pure)
                                       #`(Empty-set #,pure)
                                       #'orig-stx))
  (pattern (~and orig-stx (Set-Union s-e ...))
           #:do [(define tag
                   (let get-tag ([tag 0] [exprs (attribute s-e.value)])
                     (if (pair? exprs)
                         (get-tag
                          (fxior tag (expression-store-interaction (car exprs)))
                          (cdr exprs))
                         tag)))]
           #:attr value
           (with-orig-stx (Set-Union tag (attribute s-e.value))
                          #`(Set-Union #,tag (list #,@(map with-orig-stx-core (attribute s-e.value))))
                          #'orig-stx))
  (pattern (~and orig-stx (Set-Add* s-e v-e ...))
           #:do [(define tag
                   (let get-tag ([tag (expression-store-interaction (attribute s-e.value))]
                                 [exprs (attribute v-e.value)])
                     (if (pair? exprs)
                         (get-tag (fxior tag (expression-store-interaction (car exprs)))
                                  (cdr exprs))
                         tag)))]
           #:attr value
           (with-orig-stx
            (Set-Add* tag (attribute s-e.value) (attribute v-e.value))
            #`(Set-Add* #,tag
                        #,(with-orig-stx-core (attribute s-e.value))
                        (list #,@(map with-orig-stx-core (attribute v-e.value))))
            #'orig-stx))
  (pattern (~and orig-stx (In-Set s-e v-e))
           #:do [(define tag
                   (fxior ;; can be approximate, and may indirect through store to check equality
                    9     ;; read/many
                    (fxior (expression-store-interaction (attribute s-e.value))
                           (expression-store-interaction (attribute v-e.value)))))]
           #:attr value
           (with-orig-stx
            (In-Set tag (attribute s-e.value) (attribute v-e.value))
            #`(In-Set #,tag
                      #,(with-orig-stx-core (attribute s-e.value))
                      #,(with-orig-stx-core (attribute v-e.value)))
            #'orig-stx))
  (pattern (~and orig-stx
                 ((~and alloc-stx
                        (~or (~and SAlloc (~bind [allocer SAlloc]))
                             (~and MAlloc (~bind [allocer MAlloc])))) space:id))
           #:attr value
           (with-orig-stx
            ((attribute allocer) alloc (syntax-e #'space))
            #`(alloc-stx #,alloc 'space)
            #'orig-stx))
  (pattern (~and orig-stx
                 ((~and alloc-stx
                        (~or (~and QSAlloc (~bind [allocer QSAlloc]))
                             (~and QMAlloc (~bind [allocer QMAlloc])))) space:id hint:expr))
           #:attr value
           (with-orig-stx
            ((attribute allocer) alloc (syntax-e #'space) (eval-syntax #'hint))
            #`(alloc-stx #,alloc 'space hint)
            #'orig-stx))
  (pattern (~and orig-stx Unsafe-store-space-ref)
           #:attr value (with-orig-stx (Unsafe-store-space-ref pure)
                                       #'Unsafe-store-space-ref
                                       #'orig-stx))
  (pattern (~and orig-stx (Unsafe-store-ref space:id))
           #:attr value (with-orig-stx
                         (Unsafe-store-ref pure (syntax-e #'space))
                         #`(Unsafe-store-ref #,pure 'space)
                         #'orig-stx)))

(define-syntax-class (BSC L bound-vars)
  #:attributes (value new-scope interaction)
  #:literals (where when update)
  #:local-conventions ([#rx".*-e$" (Expression L bound-vars)])
  (pattern (~and orig-stx (where (~var p (Pattern L #f #t bound-vars))
                                 let-e))
           #:attr value
           (with-orig-stx (Binding (attribute p.value) (attribute let-e.value))
                          #`(Binding #,(with-orig-stx-core (attribute p.value))
                                     #,(with-orig-stx-core (attribute let-e.value)))
                          #'orig-stx)
           #:attr new-scope (attribute p.new-scope)
           #:attr interaction (let ([si (expression-store-interaction (attribute let-e.value))])
                                (if (attribute p.non-linear?)
                                    ;; Can possibly fail, so that makes set representation necessary.
                                    (fxior si 9) ;; read/many
                                    si)))
  (pattern (~and orig-stx (when sc-e))
           #:attr value (with-orig-stx (When (attribute sc-e.value))
                                       #`(When #,(with-orig-stx-core (attribute sc-e.value)))
                                       #'orig-stx)
           #:attr new-scope bound-vars
           #:attr interaction (add-many (expression-store-interaction (attribute sc-e.value))))
  (pattern (~and orig-stx (update k-e v-e (~optional (~and #:trust-strong trust-strong))))
           #:attr value
           (with-orig-stx
            (Store-extend (attribute k-e.value)
                          (attribute v-e.value)
                          (syntax? (attribute trust-strong)))
            #`(Store-extend
               #,(with-orig-stx-core (attribute k-e.value))
               #,(with-orig-stx-core (attribute v-e.value))
               #,(syntax? (attribute trust-strong)))
            #'orig-stx)
           #:attr new-scope bound-vars
           #:attr interaction
           (add-writes (fxior (expression-store-interaction (attribute k-e.value))
                              (expression-store-interaction (attribute v-e.value))))))

(define-syntax-class (Bindings L bound-vars)
  #:attributes (new-scope value interaction)
  (pattern (~and orig-stx ()) #:attr new-scope bound-vars
           #:attr value (with-orig-stx '() #'() #'orig-stx)
           #:attr interaction pure)
  (pattern (~and orig-stx
                 ((~var bsc (BSC L bound-vars)) .
                  (~var bscs (Bindings L (attribute bsc.new-scope)))))
           #:attr value
           (with-orig-stx (cons (attribute bsc.value) (attribute bscs.value))
                          (cons (with-orig-stx-core (attribute bsc.value))
                                (with-orig-stx-core (attribute bscs.value)))
                          #'orig-stx)
           #:attr new-scope (attribute bscs.new-scope)
           #:attr interaction (fxior (attribute bsc.interaction)
                                     (attribute bscs.interaction))))

(define (parse-rules stx)
  (syntax-parse stx
    #:literals (-->)
    [(_ lang
        (~do (define langv (syntax-local-value #'lang)))
        [--> (~optional (~seq #:name name))
             (~var lhs (Pattern langv #f #t (make-immutable-free-id-table)))
             rhs-raw
             .
             (~and (~var bscs (Bindings langv (attribute lhs.new-scope)))
                   (~parse (~var rhs (Pattern langv #f #f (attribute bscs.new-scope)))
                           #'rhs-raw))]
        ...)
     (for/list ([l (in-list (attribute lhs.value))]
                [r (in-list (attribute rhs.value))]
                [bsc (in-list (attribute bscs.value))]
                [n (in-list (attribute name))])
       (Rule n l r bsc))]))

(define (parse-meta-function stx)
  (syntax-parse stx
    [(_ lang
        mf-name:id
        (~do (define langv (syntax-local-value #'lang)))
        (~or (~optional (~seq #:concrete conc:expr))
             (~optional (~seq #:abstract abs:expr))) ...
        [(~var lhs (Pattern langv #f #t (make-immutable-free-id-table)))
         rhs-raw
         .
         (~and (~var bscs (Bindings langv (attribute lhs.new-scope)))
               (~parse (~var rhs (Pattern langv #f #f (attribute bscs.new-scope)))
                       #'rhs-raw))]
        ...)
     #:fail-unless (implies (null? (attribute lhs)) (and (attribute conc) (attribute abs)))
     "Must supply rules unless both concrete and abstract implementations are trusted."
     (with-orig-stx
      (Meta-function #'mf-name
                     (for/list ([l (in-list (attribute lhs.value))]
                                [r (in-list (attribute rhs.value))]
                                [bsc (in-list (attribute bscs.value))])
                       (Rule #f l r bsc))
                     (and (attribute conc) (eval-syntax #'conc))
                     (and (attribute abs) (eval-syntax #'abs)))
      (quasitemplate
       (Meta-function 'mf-name
                      (list #,@(for/list ([l (in-list (attribute lhs.value))]
                                          [r (in-list (attribute rhs.value))]
                                          [bsc (in-list (attribute bscs.value))])
                                 #`(Rule #f
                                         #,(with-orig-stx-core l)
                                         #,(with-orig-stx-core r)
                                         #,(with-orig-stx-core bsc))))
                      (?? conc #f)
                      (?? abs #f)))
      stx)]))

(flatten-language
 (parse-language
  #'(Lang CESK
          [BAddrs #:address-space bindings]
          [Variable #:external-space symbol? #:cardinality (λ (e) 1)]
          [Env (Variable → (Address-Space bindings))]
          [Expr (Ref Variable) (App Expr Expr) Pre-value #:trust-recursion]
          [Pre-value (Lam Variable Expr) #:trust-recursion]
          [With-env (Closure Expr Env)]
          [Value (Closure Pre-value Env)]
          [Frame (Ar Expr Env) (Fn Value)]
          [Kont (Mt) (Kcons Frame Kont)]
          [States (State With-env Kont)])))

#;
(define (parse-expression L stx)
  (syntax-parse stx
    [(Term pat)]))
