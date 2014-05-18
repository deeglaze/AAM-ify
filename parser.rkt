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
(require "spaces.rkt" "space-ops.rkt" "shared.rkt" racket/match
         "syntax-classes.rkt"
         (for-syntax
          (only-in "lattices.rkt" pc⊔)
          "typecheck.rkt"
          racket/pretty racket/trace
          racket/base "spaces.rkt" "space-ops.rkt"
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
         -->
         Setof Any where update
         (for-syntax Lang Options-cls quine-Options))

(define-syntax (--> stx) (raise-syntax-error #f "For use in Rule form" stx))

(begin-for-syntax
 (define language-info (make-free-id-table))
 ;; Associate language id with free-id-table of metafunction names to mf values.
 (define language-meta-functions (make-free-id-table))

 (define (quine-space space)
   (match space
    [(with-orig-stx v core stx)
     (define v*
       (match v
         [(User-Space c trust-recursion? trust-construction?)
          #`(User-Space #,(quine-Component c)
                        #,trust-recursion?
                        #,trust-construction?)]
         [(or (? External-Space?) (? Address-Space?)) core]
         [other (error 'quine-space "Bad space ~a" other)]))
      #`(with-orig-stx #,v* #'#,core #'#,stx)]
    [_ (error 'quine-space "Bad wos ~a" space)]))

(define (quine-Options options)
  (match options
    [(Options pun-space? externalize? raise? missing? mb eb)
     #`(Options #,pun-space? #,externalize? #,raise? #,missing? '#,mb '#,eb)]
    [_ (error 'quine-Options "Bad options ~a" options)]))

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
           #`(variant #,(quine-Component var)
                      (vector #,@(for/list ([p (in-vector pats)])
                                   (quine-pattern p))))]
          [(Set-with vpat spat mode spointer)
           #`(Set-with #,(quine-pattern vpat) #,(quine-pattern spat) '#,mode
                       #,(and spointer (quine-Component spointer)))]
          [(Map-with kpat vpat mpat mode mpointer)
           #`(Map-with #,(quine-pattern kpat)
                       #,(quine-pattern vpat)
                       #,(quine-pattern mpat)
                       '#,mode
                       #,(and mpointer (quine-Component mpointer)))]
          [(Anything* c) #`(Anything* #,(quine-Component c))]
          [(? Anything?) #'-Anything]
          [(is-a name) #`(is-a #'#,name)]
          [(Datum atom) #`(Datum '#,atom)]
          [(? boolean? b) #`#,b]

          ;; DPatterns
          [(Address space addr match-behavior equal-behavior)
           #`(Address #'#,space
                      #,(if (syntax? addr) #`(syntax #,addr) addr)
                      '#,match-behavior
                      '#,equal-behavior)]
          [(external E v) ;; FIXME: external spaces need a quine.
           (define equine (External-Space-quine (with-orig-stx-v E)))
           (unless equine
             (error 'quine-pattern "Partially specified space requires a quine ~a" E))
           #`(external #,(quine-space E) #,(equine v))]

          [(Abs-Data Eh S)
           #`(Abs-Data (hash . #,(for/fold ([acc '()]) ([(E ev) (in-hash Eh)])
                                  (list* (quine-space E) (quine-pattern ev) acc)))
                       #,(if (user-set? S)
                             #`(mk-user-set . #,(for/list ([v (in-set S)]) (quine-pattern v)))
                             (quine-pattern S)))]

          [_ (error 'quine-pattern "Bad pattern ~a" pat)]))
      #`(with-orig-stx #,v* #'#,core #'#,stx)]
     [_ (error 'quine-pattern "Bad wos ~a" pat)]))

 (define (quine-rule rule)
   (match rule
     [(with-orig-stx v core stx)
      (define v*
        (match v
          [(Rule name lhs rhs (BSCS si bscs) lexpect rexpect)
           #`(Rule #,(and name #`#'#,name) #,(quine-pattern lhs) #,(quine-pattern rhs)
                   (BSCS
                    #,si
                    (list . #,(map quine-bsc bscs)))
                   #,(and lexpect (quine-Component lexpect))
                   #,(and rexpect (quine-Component rexpect)))]
          [_ (error 'quine-rule "Bad rule ~a" v)]))
      #`(with-orig-stx #,v* #'#,core #'#,stx)]
     [_ (error 'quine-rule "Bad wos ~a" rule)]))

 (define (quine-Component c)
   (match c
     [(with-orig-stx v core stx)
      (define v*
        (match v
          [(Map pc ex dom rng) #`(Map '#,pc #,ex #,(quine-Component dom) #,(quine-Component rng))]
          [(℘ pc ex? comp) #`(℘ '#,pc #,ex? #,(quine-Component comp))]
          [(∪ pc comps)
           #`(∪ '#,pc
                (list . #,(for/list ([c (in-list comps)]) (quine-Component c))))]
          [(Variant pc name comps tr? tc?)
           #`(Variant '#,pc #'#,name
                      (vector . #,(for/list ([c (in-vector comps)])
                                    (quine-Component c)))
                      #,tr? #,tc?)]
          [(Space-reference pc emb eeb name) #`(Space-reference '#,pc '#,emb '#,eeb #'#,name)]
          [(Anything* c) #`(Anything* #,(quine-Component c))]
          [(or (? Anything?) (? Address-Space?) (? Datum?) (? boolean?) (? Bool?)) core]
          [other (error 'quine-Component "Bad component ~a" c)]))
      #`(with-orig-stx #,v* #'#,core #'#,stx)]
     [_ (error 'quine-Component "Bad wos ~a" c)]))

(define (quine-expression e)
  (match e
    [(with-orig-stx v core stx)
     (define do quine-expression)
     (define v*
       (match v
         [(Term si c p) #`(Term #,si #,(and c (quine-Component c)) #,(quine-pattern p))]
         [(or (? Map-empty??)
              (? Unsafe-store-ref?) (? Unsafe-store-space-ref?)
              (? Alloc?) (? ????))
          core]

         [(Empty-map si c)
          #`(Empty-map #,si #,(quine-Component c))]
         [(Map-lookup si c m k d? d)
          #`(Map-lookup #,si #,(and c (quine-Component c))
                        '#,m #,(do k) #,d? #,(and d? (do d)))]
         [(Map-extend si c m k v strong?)
          #`(Map-extend #,si #,(and c (quine-Component c))
                        '#,m #,(do k) #,(do v) #,strong?)]
         [(Map-remove si c m k)
          #`(Map-remove #,si #,(and c (quine-Component c)) '#,m #,(do k))]
         [(In-Dom? si c m k)
          #`(In-Dom? #,si -Bool '#,m #,(do k))]

         [(Store-lookup si c k)
          #`(Store-lookup #,si #,(and c (quine-Component c)) #,(do k))]

         [(If si c g t e)
          #`(If #,si #,(and c (quine-Component c))
                #,(do g) #,(do t) #,(do e))]
         [(Let si c bscs body)
          #`(Let #,si #,(and c (quine-Component c)) #,(quine-bscs bscs) #,(do body))]
         [(Match si c d rules)
          #`(Match #,si #,(and c (quine-Component c))
                   #,(do d) (list . #,(map quine-rule rules)))]
         [(Equal si c l r)
          #`(Equal #,si -Bool #,(do l) #,(do r))]

         [(or (Set-Union si c s vs)
              (Set-Add* si c s vs)
              (Set-Remove* si c s vs)
              (Set-Subtract si c s vs)
              (Set-Intersect si c s vs))
          (define head
            (cond
             [(Set-Union? v) #'Set-Union]
             [(Set-Add*? v) #'Set-Add*]
             [(Set-Remove*? v) #'Set-Remove*]
             [(Set-Subtract? v) #'Set-Subtract]
             [(Set-Intersect? v) #'Set-Intersect]))
          #`(#,head #,si #,(and c (quine-Component c))
                    #,(do s) (list #,@(map do vs)))]
         [(In-Set? si c s v) #`(In-Set? #,si -Bool #,(do s) #,(do v))]
         [(Set-empty? si c s) #`(Set-empty? #,si -Bool #,(do s))]
         [(Empty-set si comp)
          #`(Empty-set #,si #,(quine-Component comp))]

         [(Meta-function-call si c name p)
          #`(Meta-function-call #,si #,(and c (quine-Component c))
                                #'#,name #,(quine-pattern p))]
         [other (error 'quine-expression "Bad expression ~a" other)]))
     #`(with-orig-stx #,v* #'#,core #'#,stx)]
    [_ (error 'quine-expression "Bad wos ~a" e)]))

(define (quine-bscs bscs)
  (match bscs
    [(with-orig-stx v core stx)
     (define v*
       (match v
         [(BSCS si bindings)
          (define bindings* (map quine-bsc bindings))
          #`(BSCS #,si (list . #,bindings*))]
         [_ (error 'quine-bscs "Bad BSCS ~a" v)]))
     #`(with-orig-stx #,v* #'#,core #'#,stx)]))

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

(define-syntax-class Lang
  #:attributes (langv id)
  (pattern L:id
           #:do [(define v (free-id-table-ref language-info #'L -unmapped))]
           #:fail-unless (Language? v)
           (format "Not associated with language info: ~a" (syntax-e #'L))
           #:attr id #'L
           #:attr langv v))

(define-splicing-syntax-class (Options-cls lang-ops)
  #:attributes (value)
  (pattern (~seq
            (~or (~optional (~or (~and #:pun-space-names pun-space)
                                 (~and #:no-pun-space-names no-pun-space)))
                 (~optional (~or (~and #:report-type-errors type-errors)
                                 (~and #:silence-type-errors no-type-errors)))
                 (~optional (~or (~and #:report-missing-expect missing)
                                 (~and #:silence-missing-expect no-missing)))
                 (~optional x:Externalize)
                 (~optional (~seq #:default-behaviors [behaviors:Behaviors]))) ...)
           #:attr value
           (Options (cond
                     [(syntax? (attribute pun-space)) #t]
                     [(syntax? (attribute no-pun-space)) #f]
                     [lang-ops (Options-pun-space? lang-ops)]
                     [else core-pun-spaces-default])
                    (cond
                     [(attribute x) (attribute x.externalize?)]
                     [lang-ops (Options-externalize? lang-ops)]
                     [else core-externalize-default])
                    (cond
                     [(syntax? (attribute type-errors)) #t]
                     [(syntax? (attribute no-type-errors)) #f]
                     [lang-ops (Options-raise-type-errors? lang-ops)]
                     [else core-raise-type-errors-default])
                    (cond
                     [(syntax? (attribute missing)) #t]
                     [(syntax? (attribute no-missing)) #f]
                     [lang-ops (Options-error-on-missing-expect? lang-ops)]
                     [else core-error-on-missing-expect-default])
                    (or (attribute behaviors.match-behavior)
                        (and lang-ops (Options-match-default lang-ops))
                        core-match-default)
                    (or (attribute behaviors.equal-behavior)
                        (and lang-ops (Options-equal-default lang-ops))
                        core-equal-default))))

(define (get-variant-in-space spaces c s)
  (unless (identifier? s)
    (error 'get-variant-in-space "Bad space name (~a) given ~a and ~a" s spaces c))
  (match (resolve-space spaces (free-id-table-ref spaces s))
    [(with-orig-stx (User-Space comp _ _) _ _)
     (let search ([comp comp])
       (match (with-orig-stx-v comp)
         [(? Variant? v) (and (free-identifier=? c (Variant-name v))
                            comp)]
         [(∪ _ comps) (ormap search comps)]
         [(? Space-reference? sr)
          (get-variant-in-space spaces c (Space-reference-name sr))]
         [_ #f]))]
    [_ #f])))

(define-syntax (define-language stx)
  (syntax-parse stx
    [(_ name:id ~!
        (~var op (Options-cls #f))
        (~or [space-name:id ss ...]
             (~seq #:refinement ([constructor:id (refining-spaces:id ...)] ...))) ...)
     #:do [;; refinements are broken into chunks, so glom together before checking.
           (define constructor* (append* (attribute constructor)))
           (define refining-spaces* (append* (attribute refining-spaces)))
           (define duplicate
             (check-duplicate-identifier constructor*))]
     #:fail-when duplicate
     (format "Cannot re-specify refinement order of ~a" duplicate)

     #:do [(define Space-names (get-space-names (attribute space-name)))
           (define not-a-space
             (for*/list ([rss (in-list refining-spaces*)]
                         [rs (in-list rss)]
                         #:unless (free-id-table-has-key? Space-names rs))
               rs))]
     #:fail-unless (null? not-a-space)
     (format "Names given in refinement ordering not space names ~a" not-a-space)

     (syntax-parse #'((ss ...) ...)
        [((~var inh (Space-inhabitants Space-names (attribute op.value))) ...)
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
                       #,refinement-order
                       #,(quine-Options (attribute op.value))))
            (free-id-table-set! language-meta-functions #'name (make-free-id-table)))])]))

(define-syntax (reduction-relation stx)
  (syntax-parse stx
    #:literals (-->)
    [(_ lang:Lang ~!
        (~do (define Ξ (free-id-table-ref language-meta-functions #'lang.id))
             (define langv (attribute lang.langv)))
        (~var op (Options-cls (Language-options langv)))
        (~optional (~seq #:state-space
                         (~var ss (Component-cls
                                   (get-space-names langv)
                                   ;; FIXME?: probably shouldn't dismiss recursive states
                                   #f #f
                                   (Language-options langv)))))
        (~and
         rule-stx
         [--> (~optional (~seq #:name name))
              (~var lhs (Pattern langv #f #t #t (make-immutable-free-id-table)
                                 (attribute op.value))) ~!
              rhs-raw ~!
              .
              (~var bscs (Bindings langv #t (attribute lhs.new-scope) Ξ (attribute op.value)))])
        ...)
     ;; Parse right-hand-sides after the fact since the binding-side-conditions extend the scope
     ;; positionally after the RHS.
     (define rhss
       (for/list ([rhs (in-list (attribute rhs-raw))]
                  [bscsns (in-list (attribute bscs.new-scope))])
         (syntax-parse rhs
           [(~var rhs (Pattern langv #f #f #t bscsns (attribute op.value)))
            (attribute rhs.value)])))
     
     (define ssv (attribute ss.value))
     (define rule-woss
       (for/list ([rstx (in-list (attribute rule-stx))]
                  [l (in-list (attribute lhs.value))]
                  [r (in-list rhss)]
                  [bsc-stx (in-list (attribute bscs))]
                  [bsc (in-list (attribute bscs.value))]
                  [n (in-list (attribute name))]
                  [si (in-list (attribute bscs.interaction))])
         (define BSCS-wos
           (with-orig-stx
            (BSCS si bsc)
            #`(BSCS #,si (list . #,(map with-orig-stx-core bsc)))
            bsc-stx))
         (with-orig-stx
          (Rule n l r BSCS-wos ssv ssv)
          #`(Rule #,(and n #`'#,n)
                  #,(with-orig-stx-core l)
                  #,(with-orig-stx-core r)
                  #,(with-orig-stx-core BSCS-wos)
                  #,(and ssv (with-orig-stx-core ssv))
                  #,(and ssv (with-orig-stx-core ssv)))
          rstx)))
     (define wos
       (with-orig-stx
        (Reduction-Relation rule-woss ssv)
        #`(Reduction-Relation
           (list . #,(map with-orig-stx-core rule-woss))
           #,(and ssv (with-orig-stx-core ssv)))
        stx))
     (define wos*
       (if (Options-raise-type-errors? (attribute op.value))
           (typecheck-RR langv Ξ wos)
           wos))
     (with-orig-stx-core wos*)]))

(begin-for-syntax
 (define (name-is-constructor? L id)
   (for*/or ([space (in-dict-values (Language-spaces L))]
             [spacev (in-value (with-orig-stx-v space))]
             #:when (User-Space? spacev))
     (let search ([c (User-Space-component spacev)])
       (match c
         [(∪ _ cs) (ormap search cs)]
         [(? Variant?) (free-identifier=? (Variant-name c) id)]
         [_ #f]))))

 (define-syntax-class funto [pattern (~or (~datum ->) (~datum →))])

 (define-splicing-syntax-class (MF-type space-names options)
   #:attributes (dom rng)
   (pattern (~seq (~datum :)
                  (~or (~seq (~var dom-c (Component-cls space-names #f #f options))
                             _:funto
                             (~var rng-c (Component-cls space-names #f #f options)))
                       (_:funto
                        (~var dom-c (Component-cls space-names #f #f options))
                        (~var rng-c (Component-cls space-names #f #f options)))))
            #:attr dom (attribute dom-c.value)
            #:attr rng (attribute rng-c.value)))

 (define (parse-meta-function stx Ξ L options)
   (syntax-parse stx
     [(mf-name:id
       (~optional lang:Lang)
       (~do (define langv (or L (attribute lang.langv))))
       (~fail #:unless (Language? langv) "Language not supplied.")
       (~optional (~var mf-type (MF-type (get-space-names langv)
                                         (Language-options langv))))
       (~or (~optional (~seq #:concrete conc:expr))
            (~optional (~seq #:abstract abs:expr (~or (~optional (~and #:reads tr-reads))
                                                      (~optional (~and #:writes tr-writes))
                                                      (~optional (~and #:allocs tr-allocs))
                                                      (~optional (~and #:many tr-many))) ...))) ...
       (~do (define-values (domv rngv)
              (if (attribute mf-type)
                  (values (with-orig-stx-v (attribute mf-type.dom))
                          (with-orig-stx-v (attribute mf-type.rng)))
                  (values #f #f))))
       [(~var lhs (Pattern langv domv #t #t (make-immutable-free-id-table) options))
        rhs-raw
        .
        (~var bscs (Bindings langv #t (attribute lhs.new-scope) Ξ options))]
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
            [(~var rhs (Pattern langv rngv #f #t ns options)) (attribute rhs.value)])))

      (define-values (rev-rules si)
        (for/fold ([rev-rules '()] [overall-si pure])
            ([l (in-list (attribute lhs.value))]
             [r (in-list rhss)]
             [bsc (in-list (attribute bscs.value))]
             [si (in-list (attribute bscs.interaction))])
          (values (cons #`(Rule #f
                                #,(quine-pattern l)
                                #,(quine-pattern r)
                                (BSCS #,si
                                      (list . #,(map quine-bsc bsc)))
                                no-comp-yet no-comp-yet)
                        rev-rules)
                  (fxior si overall-si))))
      (define rules (reverse rev-rules))
      (define trusted-si
        (if (attribute abs)
            (for/fold ([si pure])
                ([syn (in-list (list (attribute tr-reads)
                                     (attribute tr-writes)
                                     (attribute tr-allocs)
                                     (attribute tr-many)))]
                 [quality (in-list (list reads writes allocs many))]
                 #:when syn)
              (fxior si quality))
            si))
      (with-orig-stx
       (with-orig-stx
        (Meta-function #'mf-name
                       rules
                       ;; collect up the store interactions given by the syntax.
                       trusted-si
                       (and (attribute conc) (eval-syntax #'conc))
                       (and (attribute abs) (eval-syntax #'abs)))
        (quasitemplate
         (Meta-function 'mf-name
                        (list .
                              #,(for/list ([l (in-list (attribute lhs.value))]
                                           [r (in-list rhss)]
                                           [bsc (in-list (attribute bscs.value))]
                                           [si (in-list (attribute bscs.interaction))])
                                  #`(Rule #f
                                          #,(with-orig-stx-core l)
                                          #,(with-orig-stx-core r)
                                          (BSCS
                                           #,si
                                           (list . #,(map with-orig-stx-core bsc)))
                                          no-comp-yet no-comp-yet)))
                        #,trusted-si
                        (?? conc #f)
                        (?? abs #f)))
        stx)
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
                                           (BSCS
                                            #,si
                                            (list . #,(map with-orig-stx-core bsc)))
                                           no-comp-yet no-comp-yet)))
                         #,trusted-si
                         (?? conc #f)
                         (?? abs #f)))
         #'#,stx))
       stx)]))
 )

;; Set up the environment that says which meta-functions are in scope.
(define-syntax (define-metafunctions stx)
  (syntax-parse stx
    [(_ L:Lang
        (~var op (Options-cls (Language-options (attribute L.langv))))
        (~and mfs (mf-name:id ~!
                              (~optional (~var mf-type
                                               (MF-type
                                                (get-space-names (attribute L.langv))
                                                (Language-options (attribute L.langv))))) . rest))
        ...)
     (define other-mfs (free-id-table-ref language-meta-functions #'L))
     (define Ξ (make-free-id-table))
     ;; XXX: would really rather use dict-copy, but it's not implemented.
     (for ([(k v) (in-dict other-mfs)])
       (free-id-table-set! Ξ k v))
     (for ([name (in-list (attribute mf-name))]
           [mfd (in-list (attribute mf-type.dom))]
           [mfr (in-list (attribute mf-type.rng))])
       (free-id-table-set! Ξ name (and mfd mfr (cons mfd mfr))))
     (define new-mfs
       (for/list ([mf (in-list (attribute mfs))]
                  [mfd (in-list (attribute mf-type.dom))]
                  [mfr (in-list (attribute mf-type.rng))])
         (define mfwos
           (parse-meta-function mf Ξ (attribute L.langv)
                                (attribute op.value)))
         (if (Options-raise-type-errors? (attribute op.value))
             (typecheck-MF (attribute L.langv) Ξ mfwos mfd mfr)
             mfwos)))
     #`(begin-for-syntax
        (let ([other-mfs (free-id-table-ref language-meta-functions #'L)])
          #,@(for/list ([name (in-list (attribute mf-name))]
                        [mfwos (in-list new-mfs)])
               #`(free-id-table-set!
                  other-mfs #'#,name #,(with-orig-stx-core mfwos)))))]))

(define-syntax (reify-language stx)
  (syntax-parse stx
    [(_ L:Lang)
     (match-define (Language spaces refinement-order options) (attribute L.langv))
     #`(Language (hash #,@(reverse
                           (for/fold ([kvs '()]) ([(name space) (in-dict spaces)])
                             (list* (with-orig-stx-core space) #`(quote #,name) kvs))))
                 #,refinement-order
                 #,(quine-Options options))]))

(define-syntax (reify-metafunctions-of stx)
  (syntax-parse stx
    [(_ L:Lang)
     (define rev-vks
       (for/fold ([acc '()])
           ([(name mf) (in-dict (free-id-table-ref language-meta-functions #'L.id))])
         (list* (with-orig-stx-core mf) #`'#,name acc)))
     #`(hash #,@(reverse rev-vks))]))
