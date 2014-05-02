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
         (for-syntax

          racket/pretty racket/trace

          racket/base "spaces.rkt"
          racket/list
          racket/match racket/dict racket/set racket/promise racket/vector
          syntax/parse racket/syntax syntax/id-table
          syntax/parse/experimental/template
          (only-in racket/bool implies)
          racket/fixnum))
(provide define-language
         reduction-relation
         define-metafunctions
         reify-language reify-metafunctions-of
         --> Setof Any where update
         (for-syntax Lang))

(define-syntax (--> stx) (raise-syntax-error #f "For use in Rule form" stx))

(define-syntax (Setof stx)
  (raise-syntax-error #f "To be used as Component syntax" stx))

(define-syntax (Any stx)
  (raise-syntax-error #f "To be used as Component syntax" stx))

(define-syntax (update stx)
  (raise-syntax-error #f "To be used as binding syntax" stx))

(define-syntax (where stx)
  (raise-syntax-error #f "To be used as binding syntax" stx))

(begin-for-syntax
 (define language-info (make-free-id-table))
 ;; Associate language id with free-id-table of metafunction names to mf values.
 (define language-meta-functions (make-free-id-table))
 (struct with-orig-stx (v core surface-stx) #:transparent)

 (define/match (unwrap-wos s) [((with-orig-stx s* _ _)) s*] [(_) s])
 (define (quine-space space)
   (match space
    [(with-orig-stx v core stx)
     (define v*
       (match v
         [(User-Space variants trust-recursion? trust-construction?)
          #`(User-Space (list #,@(for/list ([v-or-c (in-list variants)])
                                   (if (Variant? (unwrap-wos v-or-c))
                                       (quine-Variant v-or-c)
                                       (quine-Component v-or-c))))
                        #,trust-recursion?
                        #,trust-construction?)]
         [(or (? External-Space?) (? Address-Space?)) core]
         [other (error 'quine-space "Bad space ~a" other)]))
      #`(with-orig-stx #,v* #'#,core #'#,stx)]
    [_ (error 'quine-space "Bad wos ~a" space)]))

 ;;; FIXME: ensure type aliases don't cycle and make this diverge.
 (define (resolve-space spaces space fuel)
   (if (eq? 0 fuel)
       (raise-syntax-error #f "Circular space alias" space)
       (match space
         [(with-orig-stx v _ _)
          (match v
            [(Space-reference id) (resolve-space spaces (free-id-table-ref spaces id) (sub1 fuel))]
            [(or (? User-Space?) (? External-Space?) (? Address-Space?)) space]
            ;; non-reference components are unchecked.
            [_ #f])]
         [#f #f])))

 ;; Parsed values are comprised of syntax objects.
 (define (quine-pattern pat)
   (match pat
     [(with-orig-stx v core stx)
      (define (quine-map m)
        (reverse
         (for/fold ([kvs '()]) ([(k v) (in-dict map)])
           (list* (quine-pattern v) (quine-pattern k) kvs))))
      (define v*
        (match v
          [(Name id pat)
           #`(Name #'#,id #,(quine-pattern pat))]
          [(Rvar id)
           #`(with-orig-stx (Rvar #'#,id) #'#,core #'#,stx)]
          [(variant var pats)
           #`(variant #,(quine-Variant var)
                      (vector #,@(for/list ([p (in-vector pats)])
                                   (quine-pattern p))))]
          [(Set-with vpat spat mode)
           #`(Set-with #,(quine-pattern vpat) #,(quine-pattern spat) '#,mode)]
          [(Map-with kpat vpat mpat mode)
           #`(Map-with #,(quine-pattern kpat)
                       #,(quine-pattern vpat)
                       #,(quine-pattern mpat)
                       '#,mode)]

          [(abstract-ffun map) #`(abstract-ffun (hash #,@(quine-map map)))]
          [(discrete-ffun map) #`(discrete-ffun (hash #,@(quine-map map)))]
          [(? dict? map) #`(hash #,@(quine-map map))]
          [(? set? pats)
           #`(set #,@(for/list ([p (in-set pats)]) (quine-pattern p)))]
          [(Address-Structural space addr)
           #`(Address-Structural #'#,space #,(if (syntax? addr)
                                                 #`(syntax #,addr)
                                                 addr))]
          [(Address-Egal space addr)
           #`(Address-Egal #'#,space (if (syntax? addr)
                                         #`(syntax #,addr)
                                         addr))]
          [atom #`'#,atom]))
      #`(with-orig-stx #,v* #'#,core #'#,stx)]
     [_ (error 'quine-pat "Bad wos ~a" pat)]))

 (define (quine-Variant var)
   (match var
     [(with-orig-stx v core stx)
      (define v*
        (match v
          [(Variant name comps)
           #`(Variant #'#,name
                      (vector #,@(for/list ([comp (in-vector comps)])
                                   (quine-Component comp))))]
          [other (error 'quine-Variant "Bad variant ~a" other)]))
      #`(with-orig-stx #,v* #'#,core #'#,stx)]
     [_ (error 'quine-Variant "Bad wos ~a" var)]))

 (define (quine-Component c)
   (match c
     [(with-orig-stx v core stx)
      (define v*
        (match v
          [(Space-reference name) #`(Space-reference #'#,name)]
          [(Map dom rng) #`(Map #,(quine-Component dom) #,(quine-Component rng))]
          [(℘ comp) #`(℘ #,(quine-Component comp))]
          [(or (? Anything?) (? Address-Space?)) core]
          [other (error 'quine-Component "Bad component ~a" c)]))
      #`(with-orig-stx #,v* #'#,core #'#,stx)]
     [_ (error 'quine-Component "Bad wos ~a" c)]))

(define (quine-expression e)
  (match e
    [(with-orig-stx v core stx)
     (define do quine-expression)
     (define v*
       (match v
         [(Term si p) #`(Term #,si #,(quine-pattern p))]
         [(or (? Boolean?) (? Map-empty??)
              (? Unsafe-store-ref?) (? Unsafe-store-space-ref?)
              (? SAlloc?) (? MAlloc?) (? QSAlloc?) (? QMAlloc?))
          core]

         [(Empty-map si container)
          #`(Empty-map #,si #,(match container
                                [(== values eq?) #'values]
                                [(== abstract-ffun eq?) #'abstract-ffun]
                                [(== discrete-ffun eq?) #'discrete-ffun]
                                [_ (quine-expression container)]))]
         [(Map-lookup si m k d? d)
          #`(Map-lookup #,si '#,m #,(do k) #,d? #,(and d? (do d)))]
         [(Map-extend si m k v strong?)
          #`(Map-extend #,si '#,m #,(do k) #,(do v) #,strong?)]
         [(Map-remove si m k)
          #`(Map-remove #,si '#,m #,(do k))]
         [(In-Dom? si m k) #`(In-Dom? #,si '#,m #,(do k))]

         [(Store-lookup si k) #`(Store-lookup #,si #,(do k))]

         [(If si g t e) #`(If #,si #,(do g) #,(do t) #,(do e))]
         [(Let si bscs body) #`(Let #,si (list #,@(map quine-bsc bscs)) #,(do body))]
         [(Equal si l r) #`(Equal #,si #,(do l) #,(do r))]

         [(Set-Union si es) #`(Set-Union #,si (list #,@(map do es)))]
         [(Set-Add* si s vs) #`(Set-Add* #,si #,(do s) (list #,@(map do vs)))]
         [(Set-Remove* si s vs) #`(Set-Remove* #,si #,(do s) (list #,@(map do vs)))]
         [(Set-Subtract si s vs) #`(Set-Subtract #,si #,(do s) (list #,@(map do vs)))]
         [(Set-Intersect si s ss) #`(Set-Intersect #,si #,(do s) (list #,@(map do ss)))]
         [(In-Set? si s v) #`(In-Set? #,si #,(do s) #,(do v))]
         [(Set-empty? si s) #`(Set-empty? #,si #,(do s))]
         [(Empty-set si container)
          #`(Empty-set #,si #,(match container
                                [(== values eq?) #'values]
                                [(== abstract-set eq?) #'abstract-set]
                                [(== discrete-set eq?) #'discrete-set]
                                [_ (quine-expression container)]))]

         [(Meta-function-call si name p)
          #`(Meta-function-call #,si #'#,name #,(quine-pattern p))]
         [other (error 'quine-expression "Bad expression ~a" other)]))
     #`(with-orig-stx #,v* #'#,core #'#,stx)]
    [_ (error 'quine-expression "Bad wos ~a" e)]))

 (define (quine-bsc bsc)
   (match bsc
     [(with-orig-stx v core stx)
      (define v*
        (match v
          [(When e)
           #`(When #,(quine-expression e))]
          [(Binding pat e)
           #`(Binding #,(quine-pattern pat) #,(quine-expression e))]
          [(Store-extend k v strong?)
           #`(Store-extend #,(quine-expression k)
                           #,(quine-expression v)
                           #,strong?)]
          [other (error 'quine-bsc "Bad bsc ~a" other)]))
      #`(with-orig-stx #,v* #'#,core #'#,stx)]
     [_ (error 'quine-bsc "Bad wos ~a" bsc)]))

 (define (list-order< lst v0 v1 [cmp equal?])
   (match lst
     ['() (error 'list-order< "Expected elements to be in list ~a ~a" v0 v1)]
     [(cons v lst)
      (cond [(cmp v v0) #t]
            [(cmp v v1) #f]
            [else (list-order< lst v0 v1 cmp)])]))

 (define (choose-best orig-stx order v0 ns0 nl0 v1 ns1 nl1)
   (define name (Variant-name (with-orig-stx-v
                               (variant-vpointer (with-orig-stx-v v0)))))
   (if (list-order<
        (free-id-table-ref
         order name
         )
        v0 v1)
       (values v0 ns0 nl0)
       (values v1 ns1 nl1)))

 (define (free-id-table-has-key? t k)
   (not (eq? (free-id-table-ref t k -unmapped) -unmapped)))

 (define-syntax-class (Space-ref L)
   #:attributes (value)
   (pattern space-name:id
            #:do [(define spacev (free-id-table-ref (Language-spaces L) #'space-name -unmapped))]
            #:fail-when (eq? -unmapped spacev) (format "Unknown space ~a" (syntax-e #'space-name))
            #:attr value spacev))

 (define-literal-set expr-ids
   (Term ;;
    If ;;
    Let ;;
    Equal ;;
    Meta-function-call ;;
    Choose ;;

    ;; Map expressions
    Map-lookup ;;
    Map-extend ;;
    Map-remove ;;
    Map-empty? ;;
    In-Dom? ;;
    Empty-map ;;

    ;; Set expressions
    Set-empty? ;;
    Empty-set ;;
    Set-Union ;;
    Set-Add* ;;
    Set-Intersect ;;
    Set-Subtract ;;
    Set-Remove* ;;
    In-Set? ;;

    ;; Store expressions
    Store-lookup ;;
    SAlloc ;;
    MAlloc ;;
    QSAlloc ;;
    QMAlloc ;;
    Unsafe-store-ref ;;
    Unsafe-store-space-ref ;;
    ))

 (define-literal-set component-lits
   (Address-Space ℘ Setof Map Any))

(define-literal-set pat-ids
  (Name
   Space
   Rvar
   variant
   Map-with
   Set-with))
(define pat-reserved? (literal-set->predicate pat-ids))
(define comp-reserved? (literal-set->predicate component-lits))

;; pats are passed in unparsed.
;; If expected-space is non-#f, we check that (vname . pats) matches the given space.
;; Otherwise, we find the most suitable Variant in the language. If multiple Variant values
;; match, we choose the most general one according to the user's specification of a refinement order.
;; If there is no given order, we raise an error.
(define (find-suitable-variant L orig-stx expected-space vname pats pattern? bound-vars pun-space?)
  (define (check-space s [on-fail (λ () (values #f #f #f))])
    (match s
      [(User-Space v-or-cs _ _)
       (let search ([v-or-cs v-or-cs])
         (match v-or-cs
           ['() (on-fail)]
           [(cons (and v/orig
                       (with-orig-stx
                        (and v (Variant (== vname free-identifier=?) _))
                        core _))
                  v-or-cs)
            (syntax-parse pats
              [(~var ps (Patterns L (vector->list (Variant-Components v)) pattern? bound-vars
                                  pun-space?))
               (values
                (with-orig-stx (variant v/orig (list->vector (attribute ps.values)))
                               #`(variant #,core
                                          (vector #,@(map with-orig-stx-core (attribute ps.values))))
                               orig-stx)
                (attribute ps.new-scope)
                (attribute ps.non-linear?))]
              [_ (search v-or-cs)])]
           [(cons _ v-or-cs) (search v-or-cs)]))]
      [_ (on-fail)]))
  (cond
   [expected-space
    (define expected-space*
      (if (with-orig-stx? expected-space)
          (with-orig-stx-v expected-space)
          expected-space))
    (define (fail)
      (raise-syntax-error
       #f
       (format "Variant pattern did not match expected space (~a)" expected-space*)
       orig-stx))
    (check-space expected-space* fail)]
   [else
    (match-define (Language spaces order) L)
    (let search ([itr (free-id-table-iterate-first spaces)]
                 [best-space #f]
                 [best #f]
                 [best-new-scope #f]
                 [best-non-linear? #f])
      (cond
       [itr
        (define s (with-orig-stx-v (free-id-table-iterate-value spaces itr)))
        (define-values (v ns nl?) (check-space s))
        (define-values (bs* b* bns* bnl*)
          (cond
           [v
            (define space-name (free-id-table-iterate-key spaces itr))
            (cond
             [best
              (define vname (Variant-name
                             (with-orig-stx-v
                              (variant-vpointer (with-orig-stx-v v)))))
              (if (list-order<
                   (free-id-table-ref
                    order vname
                    (λ () (raise-syntax-error
                           #f
                           (format "Expected language to define refinement order for ~a"
                                   (syntax-e vname))
                           orig-stx)))
                   best-space space-name free-identifier=?)
                  (values best-space best best-new-scope best-non-linear?)
                  (values space-name v ns nl?))]
             [else (values space-name v ns nl?)])]
           [else (values best-space best best-new-scope best-non-linear?)]))
        (search (free-id-table-iterate-next spaces itr) bs* b* bns* bnl*)]
       [else
        (unless best
          (raise-syntax-error #f "Variant did not match language" orig-stx))
        (values best best-new-scope best-non-linear?)]))]))

(define-syntax-class (Patterns L expected-spaces/components pattern? bound-vars pun-space?)
  #:attributes (values non-linear? new-scope)
  (pattern ()
           #:fail-unless (null? expected-spaces/components)
           (format "Expected more components ~a" expected-spaces/components)
           #:attr values '()
           #:attr non-linear? #f
           #:attr new-scope bound-vars)
  (pattern ((~fail #:when (null? expected-spaces/components)
                   "Expected fewer components")
            (~var p (Pattern L (and (not pattern?) ;; FIXME: what about the pattern case?
                                    (car expected-spaces/components))
                             pattern? bound-vars pun-space?))
            .
            (~var ps (Patterns L (cdr expected-spaces/components)
                               pattern?
                               (attribute p.new-scope)
                               pun-space?)))
           #:attr values (cons (attribute p.value) (attribute ps.values))
           #:attr non-linear? (or (attribute p.non-linear?) (attribute ps.non-linear?))
           #:attr new-scope (attribute ps.new-scope)))

;; TODO
(define (expectations-agree? L exp-space/component space)
  #t)

(define-splicing-syntax-class match-mode
  #:attributes (mode)
  (pattern #:first #:attr mode 'first)
  (pattern #:all #:attr mode 'all)
  (pattern #:best #:attr mode 'best)
  (pattern (~seq) #:attr mode #f))

;; Patterns and terms are similar. Rvars are allowed in terms, Name/Space in patterns.
(define-syntax-class (Pattern L expected-space/component pattern? bound-vars pun-space?)
  #:literal-sets (pat-ids)
  #:attributes (value non-linear? new-scope)
  (pattern (~and orig-stx (Space (~var S (Space-ref L))))
           #:fail-unless (implies (attribute S.value)
                                  (expectations-agree?
                                   L
                                   expected-space/component
                                   (attribute S.value)))
           (format "Expected space ~a but binder expects ~a"
                   expected-space/component
                   (attribute S.value))
           #:attr value (with-orig-stx (Space (attribute S.value))
                                       #`(Space #,(with-orig-stx-core (attribute S.value)))
                                       #'orig-stx)
           #:attr non-linear? #f
           #:attr new-scope bound-vars)
  (pattern (~and orig-stx
                 (Name v:id (~var p (Pattern L expected-space/component #t bound-vars pun-space?))))
           #:fail-unless pattern? "Terms may not use Name. Not in binding context."

           #:attr value (with-orig-stx
                         (Name #'v (attribute p.value))
                         #`(Name 'v #,(with-orig-stx-core (attribute p.value)))
                         #'orig-stx)
           #:attr non-linear? (or (attribute p.non-linear?)
                                  (free-id-table-has-key? bound-vars #'v))
           #:attr new-scope (free-id-table-set (attribute p.new-scope) #'v #t))
  (pattern (~and orig-stx (Rvar v:id))
           #:fail-when pattern? "Patterns may not use Rvar. Use Name for non-linear patterns"
           #:attr value (with-orig-stx (Rvar #'v)
                                       #'(Rvar 'v)
                                       #'orig-stx)
           #:attr non-linear? #f
           #:attr new-scope bound-vars)

  (pattern (~and orig-stx (Map-with ~! (~fail #:unless pattern?
                                              "Map-with for use only in pattern position")
                                    (~var k (Pattern L #f #t bound-vars pun-space?))
                                    (~var v (Pattern L #f #t (attribute k.new-scope) pun-space?))
                                    (~var m (Pattern L #f #t (attribute v.new-scope) pun-space?))
                                    mode:match-mode))
           #:attr value (with-orig-stx
                         (Map-with (attribute k.value)
                                   (attribute v.value)
                                   (attribute m.value)
                                   (attribute mode.mode))
                         (quasitemplate
                          (Map-with #,(with-orig-stx-core (attribute m.value))
                                    #,(with-orig-stx-core (attribute k.value))
                                    #,(with-orig-stx-core (attribute v.value))
                                    '#,(attribute mode.mode)))
                         #'orig-stx)
           #:attr non-linear? (or (attribute m.non-linear?)
                                  (attribute k.non-linear?)
                                  (attribute v.non-linear?))
           #:attr new-scope (attribute m.new-scope))

  (pattern (~and orig-stx (Set-with ~! (~fail #:unless pattern?
                                              "Set-with for use only in pattern position")
                                    (~var v (Pattern L #f #t bound-vars pun-space?))
                                    (~var s (Pattern L #f #t (attribute v.new-scope) pun-space?))
                                    mode:match-mode))
           #:attr value (with-orig-stx
                         (Set-with (attribute v.value)
                                   (attribute s.value)
                                   (attribute mode.mode))
                         #`(Set-with #,(with-orig-stx-core (attribute s.value))
                                     #,(with-orig-stx-core (attribute v.value))
                                     '#,(attribute mode.mode))
                         #'orig-stx)
           #:attr non-linear? (or (attribute s.non-linear?)
                                  (attribute v.non-linear?))
           #:attr new-scope (attribute s.new-scope))

  (pattern (~and orig-stx ((~optional variant) vname:id ps:expr ...))
           #:do [(define es (resolve-space (Language-spaces L) expected-space/component
                                           (dict-count (Language-spaces L))))]
           #:fail-when (and es
                            (not (User-Space? (with-orig-stx-v es))))
           "Expected non-user space. Got a variant."
           #:do [(define-values (var found-new-scope found-non-linear?)
                   (find-suitable-variant L #'orig-stx
                                          es
                                          #'vname
                                          (syntax->list #'(ps ...))
                                          pattern?
                                          bound-vars
                                          pun-space?))]
           #:attr value var
           #:attr non-linear? found-non-linear?
           #:attr new-scope found-new-scope)

  (pattern v:id
           #:do [(define the-space
                   (and pun-space?
                        ;; not shadowed by an explicit name?
                        (not (free-id-table-has-key? bound-vars #'v))
                        (free-id-table-ref (Language-spaces L) #'v #f)))]
           #:fail-unless (or pattern? (free-id-table-has-key? bound-vars #'v))
           (format "Unbound variable reference ~a" (syntax-e #'v))
           #:attr value (if pattern?
                            (if the-space
                                (with-orig-stx (Space the-space)
                                               #`(Space #,(with-orig-stx-core the-space))
                                               #'v)
                                (with-orig-stx (Name #'v (with-orig-stx -Anything
                                                                        #'-Anything
                                                                        #'v))
                                               #`(Name 'v -Anything)
                                               #'v))
                            (with-orig-stx (Rvar #'v) #`(Rvar 'v) #'v))
           #:attr non-linear? (free-id-table-has-key? bound-vars #'v)
           #:attr new-scope (free-id-table-set bound-vars #'v #t)))

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
           #:fail-when (pat-reserved? #'constructor)
           (format "Name reserved for the pattern language ~a" (syntax-e #'constructor))
           #:fail-when (comp-reserved? #'constructor)
           (format "Name reserved for the component language ~a" (syntax-e #'constructor))
           #:attr value
           (with-orig-stx (Variant #'constructor (list->vector (attribute cs.value)))
                          #`(Variant 'constructor (vector #,@(map with-orig-stx-core (attribute cs.value))))
                          #'orig-stx)))

(define-syntax-class (variant-or-component Space-names)
  #:attributes (value)
  #:description "A variant declaration or a component"
  (pattern (~var c (Component-cls Space-names))
           #:attr value (attribute c.value))
  (pattern (~var v (Variant-cls Space-names))
           #:attr value (attribute v.value)))

(define-syntax-class (Space-inhabitants Space-names)
  #:attributes (value)
  (pattern (~and orig-stx
                 (#:external-space ~! pred:expr
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
  (pattern (~and orig-stx (#:address-space ~! tag:id))
           #:attr value (with-orig-stx (Address-Space (syntax-e #'tag))
                                       #'(Address-Space 'tag)
                                       #'orig-stx))

  ;; A User space is a sequence of variants
  (pattern (~and orig-stx
                 ((~or (~and (~var vcs (variant-or-component Space-names)) ~!)
                       (~optional (~and #:trust-recursion trust-rec))
                       (~optional (~and #:trust-construction trust-con)))
                  ...))
           #:attr value
           (with-orig-stx (User-Space (attribute vcs.value)
                                      (syntax? (attribute trust-rec))
                                      (syntax? (attribute trust-con)))
                          #`(User-Space (list #,@(map with-orig-stx-core (attribute vcs.value)))
                                        #,(syntax? (attribute trust-rec))
                                        #,(syntax? (attribute trust-con)))
                          #'orig-stx)))

(define-syntax-rule (pesi p)
  (expression-store-interaction (with-orig-stx-v (attribute p))))

(define-syntax-class (Expression L bound-vars Ξ pun-space?)
  #:attributes (value)
  #:literal-sets (expr-ids)
  #:local-conventions ([t (Pattern L #f #f bound-vars pun-space?)]
                       [#rx".*-e$" (Expression L bound-vars Ξ pun-space?)])
  (pattern (~and orig-stx (Term t))
           #:attr value (with-orig-stx
                         (Term pure (attribute t.value))
                         #`(Term #,pure #,(with-orig-stx-core (attribute t.value)))
                         #'orig-stx))
  (pattern (~and orig-stx v:boolean)
           #:attr value (with-orig-stx
                         (Boolean pure (syntax-e #'v))
                         #`(Boolean #,pure v)
                         #'orig-stx))

  ;;; Map expressions
  (pattern (~and orig-stx (Map-lookup ~! m:id k-e (~optional (~seq #:default d-e))))
           #:fail-unless (free-id-table-has-key? bound-vars #'m)
           (format "Unbound map variable ~a" (syntax-e #'m))
           #:do [(define default? (not (not (attribute d-e))))
                 (define tag
                   (add-many ;; approximate domain can lead to many lookups
                    (fxior (pesi k-e.value)
                           (if default?
                               (pesi d-e.value)
                               pure))))]
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
  (pattern (~and orig-stx (Map-extend ~! m:id k-e v-e (~optional (~and #:trust-strong trust))))
           #:fail-unless (free-id-table-has-key? bound-vars #'m)
           (format "Unbound map variable ~a" (syntax-e #'m))
           #:do [(define tag
                   (add-many ;; approximate domain can lead to multiple extensions.
                    (fxior (pesi k-e.value) (pesi v-e.value))))]
           #:attr value (with-orig-stx
                         (Map-extend tag #'m
                                     (attribute k-e.value)
                                     (attribute v-e.value)
                                     (syntax? (attribute trust)))
                         #`(Map-extend #,tag
                                       'm
                                       #,(with-orig-stx-core (attribute k-e.value))
                                       #,(with-orig-stx-core (attribute v-e.value))
                                       #,(syntax? (attribute trust)))
                         #'orig-stx))
  (pattern (~and orig-stx (Map-remove ~! m:id k-e))
           #:fail-unless (free-id-table-has-key? bound-vars #'m)
           (format "Unbound map variable ~a" (syntax-e #'m))
           #:do [(define tag
                   (fxior read/many ;; approximate domain can lead to many removals, equality ⇒ read
                          (pesi k-e.value)))]
           #:attr value (with-orig-stx
                         (Map-remove tag #'m (attribute k-e.value))
                         (quasitemplate
                          (Map-remove #,tag
                                      'm
                                      #,(with-orig-stx-core (attribute k-e.value))))
                         #'orig-stx))
  (pattern (~and orig-stx (In-Dom? ~! m:id k-e))
           #:fail-unless (free-id-table-has-key? bound-vars #'m)
           (format "Unbound map variable ~a" (syntax-e #'m))
           #:do [(define tag
                   (fxior read/many ;; approximate domain can lead to ⦃b.⊤⦄, equality ⇒ read
                          (pesi k-e.value)))]
           #:attr value (with-orig-stx
                         (In-Dom? tag #'m (attribute k-e.value))
                         (quasitemplate
                          (In-Dom? #,tag
                                   'm
                                   #,(with-orig-stx-core (attribute k-e.value))))
                         #'orig-stx))
  (pattern (~and orig-stx (Map-empty? ~! m:id))
           #:fail-unless (free-id-table-has-key? bound-vars #'m)
           (format "Unbound map variable ~a" (syntax-e #'m))
           #:attr value (with-orig-stx
                         (Map-empty? many #'m)
                         (quasitemplate (Map-empty? #,many 'm))
                         #'orig-stx))
  (pattern (~and orig-stx (Empty-map ~! (~or (~optional (~and #:discrete discrete))
                                          (~optional (~and #:concrete concrete))
                                          ;; for symmetry.
                                          (~optional #:abstract)
                                          (~optional (~seq #:abstraction-of abs-of-e)))))
           #:do [(define-values (fn stx)
                   (cond [(syntax? (attribute discrete))
                          (values discrete-ffun #'discrete-ffun)]
                         [(syntax? (attribute concrete))
                          (values values #'values)]
                         [(attribute abs-of-e)
                          (define v (attribute abs-of-e.value))
                          (values v (with-orig-stx-core v))]
                         [else (values abstract-ffun #'abstract-ffun)]))]
           #:attr value (with-orig-stx (Empty-map pure fn)
                                       #`(Empty-map #,pure #,stx)
                                       #'orig-stx))

  ;;; Generic expressions

  (pattern (~and orig-stx (If ~! g-e t-e e-e))
           #:do [(define tag (fxior (pesi g-e.value)
                                    (fxior (pesi t-e.value)
                                           (pesi e-e.value))))]
           #:attr value (with-orig-stx
                         (If tag (attribute g-e.value) (attribute t-e.value) (attribute e-e.value))
                         #`(If #,tag
                               #,(with-orig-stx-core (attribute g-e.value))
                               #,(with-orig-stx-core (attribute t-e.value))
                               #,(with-orig-stx-core (attribute e-e.value)))
                         #'orig-stx))
  (pattern (~and orig-stx (Let ~! (~var bscs (Bindings L bound-vars Ξ pun-space?))
                               (~var body (Expression L (attribute bscs.new-scope) Ξ pun-space?))))
           #:do [(define tag (fxior (attribute bscs.interaction)
                                    (pesi body.value)))]
           #:attr value
           (with-orig-stx (Let tag (attribute bscs.value) (attribute body.value))
                          #`(Let #,tag
                                 (list . #,(map with-orig-stx-core (attribute bscs.value)))
                                 #,(with-orig-stx-core (attribute body.value)))
                          #'orig-stx))
  (pattern (~and orig-stx (Equal ~! l-e r-e))
           #:do [(define tag ;; can fail and can be approximate.
                   (fxior read/many
                          (fxior (pesi l-e.value) (pesi r-e.value))))]
           #:attr value
           (with-orig-stx
            (Equal tag (attribute l-e.value) (attribute r-e.value))
            #`(Equal #,tag
                     #,(with-orig-stx-core (attribute l-e.value))
                     #,(with-orig-stx-core (attribute r-e.value)))
            #'orig-stx))
  (pattern (~and orig-stx (Choose ~! (~or (~optional (~and #:label ℓ:id)) (~once s-e)) ...))
           #:do [(define tag (add-many (pesi s-e.value)))]
           #:attr value
           (with-orig-stx
            (Choose tag (if (attribute ℓ) (syntax-e #'ℓ) (gensym)) (attribute s-e.value))
            (quasitemplate
             (Choose #,tag (?? 'ℓ (gensym)) #,(with-orig-stx-core (attribute s-e.value))))
            #'orig-stx))

  ;;; Set expressions

  (pattern (~and orig-stx (Empty-set ~! (~or (~optional (~and #:discrete discrete))
                                             (~optional (~and #:concrete concrete))
                                             ;; for symmetry.
                                             (~optional #:abstract)
                                             (~optional (~seq #:abstraction-of abs-of-e)))))
           #:do [(define-values (fn stx)
                   (cond [(syntax? (attribute discrete))
                          (values discrete-set #'discrete-set)]
                         [(syntax? (attribute concrete))
                          (values values #'values)]
                         [(attribute abs-of-e)
                          (define v (attribute abs-of-e.value))
                          (values v (with-orig-stx-core v))]
                         [else (values abstract-set #'abstract-set)]))]
           #:attr value (with-orig-stx (Empty-set pure fn)
                                       #`(Empty-set #,pure #,stx)
                                       #'orig-stx))
  (pattern (~and orig-stx (Set-Union ~! s-e ...))
           #:do [(define tag
                   (let get-tag ([tag pure] [exprs (attribute s-e.value)])
                     (match exprs
                       [(cons e exprs)
                        (get-tag (fxior tag (expression-store-interaction (with-orig-stx-v e)))
                                 exprs)]
                       ['() tag])))]
           #:attr value
           (with-orig-stx (Set-Union tag (attribute s-e.value))
                          #`(Set-Union #,tag (list #,@(map with-orig-stx-core (attribute s-e.value))))
                          #'orig-stx))
  (pattern (~and orig-stx ((~and head
                                 (~or (~and Set-Add*
                                            (~bind [constr Set-Add*]))
                                      (~and Set-Remove*
                                            (~bind [constr Set-Remove*] [tagx many]))
                                      (~and Set-Subtract
                                            (~bind [constr Set-Subtract] [tagx many]))
                                      (~and Set-Intersect
                                            (~bind [constr Set-Intersect] [tagx many]))))
                           ~! s-e v-e ...))
           #:do [(define tag
                   (let get-tag ([tag (pesi s-e.value)]
                                 [exprs (attribute v-e.value)])
                     (match exprs
                       [(cons e exprs)
                        (get-tag (fxior tag (expression-store-interaction (with-orig-stx-v e)))
                                   exprs)]
                       ['()
                        (if (attribute tagx)
                            (fxior (attribute tagx) tag)
                            tag)])))]
           #:attr value
           (with-orig-stx
            ((attribute constr) tag (attribute s-e.value) (attribute v-e.value))
            #`(head #,tag
                    #,(with-orig-stx-core (attribute s-e.value))
                    (list #,@(map with-orig-stx-core (attribute v-e.value))))
            #'orig-stx))
  (pattern (~and orig-stx (In-Set? ~! s-e v-e))
           #:do [(define tag
                   (fxior ;; can be approximate, and may indirect through store to check equality
                    read/many
                    (fxior (pesi s-e.value) (pesi v-e.value))))]
           #:attr value
           (with-orig-stx
            (In-Set? tag (attribute s-e.value) (attribute v-e.value))
            #`(In-Set? #,tag
                      #,(with-orig-stx-core (attribute s-e.value))
                      #,(with-orig-stx-core (attribute v-e.value)))
            #'orig-stx))
  (pattern (~and orig-stx (Set-empty? ~! s-e))
           #:do [(define tag
                   (add-many ;; can be approximate, and may indirect through store to check equality
                    (pesi s-e.value)))]
           #:attr value
           (with-orig-stx
            (Set-empty? tag (attribute s-e.value))
            #`(Set-empty? #,tag #,(with-orig-stx-core (attribute s-e.value)))
            #'orig-stx))

  ;;; Store expressions
  (pattern (~and orig-stx (Store-lookup ~! k-e))
           #:do [(define tag (add-reads (pesi k-e.value)))]
           #:attr value (with-orig-stx
                         (Store-lookup tag (attribute k-e.value))
                         #`(Store-lookup #,tag #,(with-orig-stx-core (attribute k-e.value)))
                         #'orig-stx))
  (pattern (~and orig-stx
                 ((~and alloc-stx
                        (~or (~and SAlloc (~bind [allocer SAlloc]))
                             (~and MAlloc (~bind [allocer MAlloc])))) ~!
                  space:id))
           #:attr value
           (with-orig-stx
            ((attribute allocer) allocs (syntax-e #'space))
            #`(alloc-stx #,allocs 'space)
            #'orig-stx))
  (pattern (~and orig-stx
                 ((~and alloc-stx
                        (~or (~and QSAlloc (~bind [allocer QSAlloc]))
                             (~and QMAlloc (~bind [allocer QMAlloc])))) space:id hint:expr))
           #:attr value
           (with-orig-stx
            ((attribute allocer) allocs (syntax-e #'space) (eval-syntax #'hint))
            #`(alloc-stx #,allocs 'space hint)
            #'orig-stx))
  (pattern (~and orig-stx Unsafe-store-space-ref)
           #:attr value (with-orig-stx (Unsafe-store-space-ref pure)
                                       #'Unsafe-store-space-ref
                                       #'orig-stx))
  (pattern (~and orig-stx (Unsafe-store-ref space:id))
           #:attr value (with-orig-stx
                         (Unsafe-store-ref pure (syntax-e #'space))
                         #`(Unsafe-store-ref #,pure 'space)
                         #'orig-stx))

  (pattern (~and orig-stx (mf:id t))
           #:fail-unless (free-id-table-has-key? Ξ #'mf)
           (format "Meta-function not in scope ~a" (syntax-e #'mf))
           #:attr value (with-orig-stx
                         (Meta-function-call read/write/alloc/many #'mf (attribute t.value))
                         #`(Meta-function-call #,read/write/alloc/many
                                               'mf #,(with-orig-stx-core (attribute t.value)))
                         #'orig-stx))
  ;; Common case is just referencing pattern variables, so make the term wrapping automatic.
  (pattern v:id
           #:fail-unless (free-id-table-has-key? bound-vars #'v)
           (format "Variable not in scope ~a" (syntax-e #'v))
           #:attr value (with-orig-stx (Term pure (with-orig-stx
                                                   (Rvar #'v)
                                                   #`(Rvar 'v)
                                                   #'v))
                                 #`(Term #,pure (Rvar 'v))
                                 #'v)))

(define-syntax-class (BSC L bound-vars Ξ pun-space?)
  #:attributes (value new-scope interaction)
  #:literals (where when update)
  #:description "A binding/side-condition/store-update"
  #:commit
  #:local-conventions ([#rx".*-e$" (Expression L bound-vars Ξ pun-space?)])
  (pattern (~and orig-stx (where ~!
                                 (~var p (Pattern L #f #t bound-vars pun-space?))
                                 let-e))
           #:attr value
           (with-orig-stx (Binding (attribute p.value) (attribute let-e.value))
                          #`(Binding #,(with-orig-stx-core (attribute p.value))
                                     #,(with-orig-stx-core (attribute let-e.value)))
                          #'orig-stx)
           #:attr new-scope (attribute p.new-scope)
           #:attr interaction (let ([si (pesi let-e.value)])
                                (if (attribute p.non-linear?)
                                    ;; Can possibly fail, so that makes set representation necessary.
                                    (fxior si read/many)
                                    si)))
  (pattern (~and orig-stx (when ~! sc-e))
           #:attr value (with-orig-stx (When (attribute sc-e.value))
                                       #`(When #,(with-orig-stx-core (attribute sc-e.value)))
                                       #'orig-stx)
           #:attr new-scope bound-vars
           #:attr interaction (add-many (pesi sc-e.value)))
  (pattern (~and orig-stx (update ~! k-e v-e (~optional (~and #:trust-strong trust-strong))))
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
           (add-writes (fxior (pesi k-e.value) (pesi v-e.value)))))

(define-syntax-class (Bindings L bound-vars Ξ pun-space?)
  #:attributes (new-scope value interaction)
  #:commit
  (pattern (~and orig-stx ()) #:attr new-scope bound-vars
           #:attr value '()
           #:attr interaction pure)
  (pattern (~and orig-stx
                 ((~var bsc (BSC L bound-vars Ξ pun-space?)) .
                  (~var bscs (Bindings L (attribute bsc.new-scope) Ξ pun-space?))))
           #:attr value (cons (attribute bsc.value) (attribute bscs.value))
           #:attr new-scope (attribute bscs.new-scope)
           #:attr interaction (fxior (attribute bsc.interaction)
                                     (attribute bscs.interaction))))

(define-syntax-class Lang
  #:attributes (langv id)
  (pattern L:id
           #:do [(define v (free-id-table-ref language-info #'L -unmapped))]
           #:fail-unless (Language? v)
           (format "Not associated with language info: ~a" (syntax-e #'L))
           #:attr id #'L
           #:attr langv v))

(define (get-variant-in-space spaces c s)
  (match (resolve-space spaces (free-id-table-ref spaces s) (dict-count spaces))
    [(with-orig-stx (User-Space vars _ _) _ _)
     (for/or ([v-or-c (in-list vars)])
       (match (with-orig-stx-v v-or-c)
         [(Variant name _)
          (and (free-identifier=? c name)
               v-or-c)]
         [(Space-reference s) (get-variant-in-space spaces c s)]
         [_ #f]))]
    [_ #f])))

(define-syntax (define-language stx)
  (syntax-parse stx
    [(_ name:id ~! (~or [space-name:id ss ...]
                        (~seq #:refinement ([constructor:id (refining-spaces:id ...)] ...))) ...)
     #:do [;; refinements are broken into chunks, so glom together before checking.
           (define constructor* (append* (attribute constructor)))
           (define refining-spaces* (append* (attribute refining-spaces)))
           (define duplicate
             (check-duplicate-identifier constructor*))]
     #:fail-when duplicate
     (format "Cannot re-specify refinement order of ~a" duplicate)

     #:do [(define Space-names
             (for/fold ([t (make-immutable-free-id-table)])
                 ([sn (in-list (attribute space-name))])
               (free-id-table-set t sn #t)))
           (define not-a-space
             (for*/list ([rss (in-list refining-spaces*)]
                         [rs (in-list rss)]
                         #:unless (free-id-table-has-key? Space-names rs))
               rs))]
     #:fail-unless (null? not-a-space)
     (format "Names given in refinement ordering not space names ~a" not-a-space)

     (syntax-parse #'((ss ...) ...)
        [((~var inh (Space-inhabitants Space-names)) ...)
         #:do [(define inh-table
                 (for/fold ([t (make-immutable-free-id-table)])
                     ([sn (in-list (attribute space-name))]
                      [space (in-list (attribute inh.value))])
                   (free-id-table-set t sn space)))
               ;; check that the spaces associated with a constructor actually
               ;; have a variant with that name.
               (define CS
                 (for/fold ([bad '()]) ([c (in-list constructor*)]
                                        [rss (in-list refining-spaces*)])
                   (define do-not-define-c
                     (for/list ([rs (in-list rss)]
                                #:unless (get-variant-in-space inh-table c rs))
                       rs))
                   (if (null? do-not-define-c)
                       bad
                       (cons (list c do-not-define-c) bad))))]
         #:fail-unless (null? CS)
         (format "Variants not defined by spaces ~a" CS)

         (define refinement-order
           (for/fold ([tstx #'(make-immutable-free-id-table)])
               ([c (in-list constructor*)]
                [rss (in-list refining-spaces*)])
             (with-syntax ([(rs ...) rss])
              #`(free-id-table-set #,tstx #'#,c (list #'rs ...)))))

         #`(begin-for-syntax
            (free-id-table-set!
             language-info
             #'name
             (Language #,(for/fold ([tstx #'(make-immutable-free-id-table)])
                             ([sn (in-list (attribute space-name))]
                              [space (in-list (attribute inh.value))])
                           #`(free-id-table-set #,tstx #'#,sn #,(quine-space space)))
                       #,refinement-order))
            (free-id-table-set! language-meta-functions #'name (make-free-id-table)))])]))

(define-syntax (reify-language stx)
  (syntax-parse stx
    [(_ i:Lang)
     (match-define (Language spaces refinement-order) (attribute i.langv))
     #`(Language (hash #,@(reverse
                           (for/fold ([kvs '()]) ([(name space) (in-free-id-table spaces)])
                             (list* (with-orig-stx-core space) #`(quote #,name) kvs))))
                 #,refinement-order)]))

(define-syntax (reify-metafunctions-of stx)
  (syntax-parse stx
    [(_ L:Lang)
     (define rev-vks
       (for/fold ([acc '()])
           ([(name mf) (in-free-id-table (free-id-table-ref language-meta-functions #'L.id))])
         (list* (with-orig-stx-core mf) #`'#,name acc)))
     #`(hash #,@(reverse rev-vks))]))

(define-syntax (reduction-relation stx)
  (syntax-parse stx
    #:literals (-->)
    [(_ lang:Lang ~!
        (~optional (~and #:pun-space-names pun-space))
        (~do (define Ξ (free-id-table-ref language-meta-functions #'lang.id))
             (define langv (attribute lang.langv))
             (define pun-space? (syntax? (attribute pun-space))))
        [--> (~optional (~seq #:name name))
             (~var lhs (Pattern langv #f #t (make-immutable-free-id-table) pun-space?)) ~!
             rhs-raw ~!
             .
             (~var bscs (Bindings langv (attribute lhs.new-scope) Ξ pun-space?))]
        ...)
     (define rhss
       (for/list ([rhs (in-list (attribute rhs-raw))]
                  [bscsns (in-list (attribute bscs.new-scope))])
         (syntax-parse rhs
           [(~var rhs (Pattern langv #f #f bscsns pun-space?))
            (attribute rhs.value)])))
     #`(list .
             #,(for/list ([l (in-list (attribute lhs.value))]
                          [r (in-list rhss)]
                          [bsc (in-list (attribute bscs.value))]
                          [n (in-list (attribute name))]
                          [si (in-list (attribute bscs.interaction))])
                 (quasitemplate
                  (Rule (?? 'n #f)
                        #,(with-orig-stx-core l)
                        #,(with-orig-stx-core r)
                        (list . #,(map with-orig-stx-core bsc))
                        #,si))))]))

(begin-for-syntax
 (define (name-is-constructor? L id)
   (for*/or ([space (in-dict-values (Language-spaces L))]
             [spacev (in-value (with-orig-stx-v space))]
             #:when (User-Space? spacev)
             [v-or-c (in-list (User-Space-variants spacev))]
             #:when (Variant? v-or-c))
     (free-identifier=? (Variant-name v-or-c) id)))

 (define (parse-meta-function stx Ξ L pun-space?)
   (syntax-parse stx
     [(mf-name:id
       (~optional lang:Lang)
       (~do (define langv (or L (attribute lang.langv))))
       (~fail #:unless (Language? langv) "Language not supplied.")
       (~or (~optional (~seq #:concrete conc:expr))
            (~optional (~seq #:abstract abs:expr (~or (~optional (~and #:reads tr-reads))
                                                      (~optional (~and #:writes tr-writes))
                                                      (~optional (~and #:allocs tr-allocs))
                                                      (~optional (~and #:many tr-many))) ...))) ...
       [(~var lhs (Pattern langv #f #t (make-immutable-free-id-table) pun-space?))
        rhs-raw
        .
        (~var bscs (Bindings langv (attribute lhs.new-scope) Ξ pun-space?))]
       ...)
      ;; At this point, components won't show up, so we can overwrite those.
      #:fail-when (pat-reserved? #'mf-name)
      (format "Name reserved for pattern language ~a" (syntax-e #'mf-name))
      #:fail-when (name-is-constructor? langv #'mf-name)
      (format "Meta-function name already defined as a variant constructor ~a" (syntax-e #'mf-name))
      #:fail-unless (implies (null? (attribute lhs)) (and (attribute conc) (attribute abs)))
      "Must supply rules unless both concrete and abstract implementations are trusted."
      (define rhss
        (for/list ([rhs-stx (in-list (syntax->list #'(rhs-raw ...)))]
                   [ns (in-list (attribute bscs.new-scope))])
          (syntax-parse rhs-stx
            [(~var rhs (Pattern langv #f #f ns pun-space?)) (attribute rhs.value)])))

      (define-values (rev-rules si)
        (for/fold ([rev-rules '()] [overall-si pure])
            ([l (in-list (attribute lhs.value))]
             [r (in-list rhss)]
             [bsc (in-list (attribute bscs.value))]
             [si (in-list (attribute bscs.interaction))])
          (values (cons #`(Rule #f
                                #,(quine-pattern l)
                                #,(quine-pattern r)
                                (list #,@(map quine-bsc bsc))
                                #,si)
                        rev-rules)
                  (fxior si overall-si))))
      (define trusted-si
        (if (attribute abs)
            (for/fold ([si pure])
                ([syn (in-list (list (attribute tr-reads)
                                     (attribute tr-writes)
                                     (attribute tr-allocs)
                                     (attribute tr-many)))]
                 [quality (in-list (list reads writes allocs many))])
              (if syn (fxior si quality) syn))
            si))
      (quasitemplate
       (with-orig-stx
         (Meta-function #'mf-name
                        (list . #,(reverse rev-rules))
                        ;; collect up the store interactions given by the syntax.
                        #,trusted-si
                        (?? conc #f)
                        (?? abs #f))
         (syntax
          (Meta-function 'mf-name
                         (list .
                               #,(for/list ([l (in-list (attribute lhs.value))]
                                            [r (in-list rhss)]
                                            [bsc (in-list (attribute bscs.value))]
                                            [si (in-list (attribute bscs.interaction))])
                                   #`(Rule #f
                                           #,(with-orig-stx-core l)
                                           #,(with-orig-stx-core r)
                                           (list . #,(map with-orig-stx-core bsc))
                                           #,si)))
                         #,trusted-si
                         (?? conc #f)
                         (?? abs #f)))
         #'#,stx))])))

;; Set up the environment that says which meta-functions are in scope.
(define-syntax (define-metafunctions stx)
  (syntax-parse stx
    [(_ L:Lang (~optional (~and #:pun-space-names pun-space))
        (~and mfs (mf-name:id ~! . rest)) ...)
     (define Ξ (make-free-id-table))
     (define other-mfs (free-id-table-ref language-meta-functions #'L))
     (for ([name (in-list (append (attribute mf-name) (dict-keys other-mfs)))])
       (free-id-table-set! Ξ name #t))
     #`(begin-for-syntax
        (let ([other-mfs (free-id-table-ref language-meta-functions #'L)])
          #,@(for/list ([name (in-list (attribute mf-name))]
                        [mf (in-list (attribute mfs))])
               #`(free-id-table-set!
                  other-mfs #'#,name
                  #,(parse-meta-function mf Ξ (attribute L.langv)
                                         (syntax? (attribute pun-space)))))))]))
