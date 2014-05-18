#lang racket/base

(require "spaces.rkt" "space-ops.rkt"
         (for-syntax
          racket/trace
          racket/base racket/match racket/fixnum (only-in racket/bool implies)
          "spaces.rkt" "space-ops.rkt"
          (only-in "lattices.rkt" pc⊔ for/pc⊔)
          syntax/parse syntax/parse/experimental/template
          racket/dict syntax/id-table))
(provide Setof update where Any
         (for-syntax
          pat-reserved? get-space-names resolve-space free-id-table-has-key?
          Space-inhabitants
          Pattern Bindings Component-cls
          Externalize Behaviors))

(define-for-syntax comp-stx
  (λ (stx) (raise-syntax-error #f "To be used as Component syntax" stx)))
(define-syntax Any comp-stx)
(define-syntax Setof comp-stx)
(define-syntax U comp-stx)
(define-syntax Union comp-stx)

(define-syntax (update stx)
  (raise-syntax-error #f "To be used as binding syntax" stx))

(define-syntax (where stx)
  (raise-syntax-error #f "To be used as binding syntax" stx))

(begin-for-syntax
 (define (resolve-space spaces space
                        #:fuel [fuel (dict-count spaces)]
                        #:expect-component [expect-component? #f])
   (if (eq? 0 fuel)
       (raise-syntax-error #f "Circular space alias" space)
       (match space
         [(with-orig-stx v _ _)
          (cond
           [(Space-reference? v)
            (define name (Space-reference-name v))
            (unless (identifier? name)
              (error 'resolve-space "Bad space reference ~a resolving ~a" name space))
            (resolve-space spaces
                           (free-id-table-ref spaces name)
                           #:fuel (sub1 fuel)
                           #:expect-component expect-component?)]
           [expect-component?
            (match v
              [(User-Space (and C (not (? ∪?))) _ _) C]
              [_ #f])]
           [(or (User-Space? v) (External-Space? v) (Address-Space? v)) space]
           ;; non-reference components are unchecked.
           [else #f])]
         [#f #f])))

 (define (list-order< lst v0 v1 [cmp equal?])
   (match lst
     ['() (error 'list-order< "Expected elements to be in list ~a ~a" v0 v1)]
     [(cons v lst)
      (cond [(cmp v v0) #t]
            [(cmp v v1) #f]
            [else (list-order< lst v0 v1 cmp)])]))

 (define (free-id-table-has-key? t k)
   (not (eq? (free-id-table-ref t k -unmapped) -unmapped)))

 (define-syntax-rule (pesi p)
   (expression-store-interaction (with-orig-stx-v (attribute p))))

 (define (get-space-names L-or-list)
   (define seq
     (match L-or-list
       [(? Language?) (in-dict-keys (Language-spaces L-or-list))]
       [(? list? l) (in-list l)]
       [_ (error 'get-space-names "Bad input ~a" L-or-list)]))
   (for/fold ([t (make-immutable-free-id-table)]) ([name seq])
     (free-id-table-set t name #t)))

 (define-syntax-class (Space-ref L)
   #:attributes (value)
   (pattern (~literal Bool) #:attr value (with-orig-stx -Bool #'-Bool #'-Bool))
   (pattern space-name:id
            #:do [(define spacev (free-id-table-ref (Language-spaces L) #'space-name -unmapped))]
            #:fail-when (eq? -unmapped spacev) (format "Unknown space ~a" (syntax-e #'space-name))
            #:attr value spacev))

 (define-literal-set expr-ids
   (Term               ;;
    If                 ;;
    Let                ;;
    Equal              ;;
    Meta-function-call ;;
    Choose             ;;
    Match              ;;

    ;; Map expressions
    Map-lookup ;;
    Map-extend ;;
    Map-remove ;;
    Map-empty? ;;
    In-Dom?    ;;
    Empty-map  ;;

    ;; Set expressions
    Set-empty?    ;;
    Empty-set     ;;
    Set-Union     ;;
    Set-Add*      ;;
    Set-Intersect ;;
    Set-Subtract  ;;
    Set-Remove*   ;;
    In-Set?       ;;

    ;; Store expressions
    Store-lookup           ;;
    Alloc                  ;;
    Unsafe-store-ref       ;;
    Unsafe-store-space-ref ;;
    ???
    ))

 (define-literal-set pat-ids
   (Name
    is-a
    Rvar
    variant
    Map-with
    Set-with
    Any))

 (define-literal-set component-lits
   (Address-Space ℘ Setof Map Any ∪ U Union Bool))

 (define pat-reserved? (literal-set->predicate pat-ids))
 (define comp-reserved? (literal-set->predicate component-lits))

 (define-syntax-class atomic
   #:attributes (value)
   (pattern n:number #:attr value (syntax-e #'n))
   (pattern s:str #:attr value (syntax-e #'s))
   (pattern c:char #:attr value (syntax-e #'c)))

 (define-syntax-class literal-data
   #:attributes (value stx)
   (pattern (~and orig-stx
                  (~or a:atomic
                       ((~literal quote) to-quote:expr)))
            #:attr value (or (and (attribute a) (attribute a.value))
                             (and (attribute to-quote)
                                  (syntax->datum #'to-quote)))
            #:attr stx #'orig-stx))

 ;; pats are passed in unparsed.
 ;; If expected-space is non-#f, we check that (vname . pats) matches the given space.
 ;; Otherwise, we find the most suitable Variant in the language. If multiple Variant values
 ;; match, we choose the most general one according to the user's specification of a refinement order.
 ;; If there is no given order, we raise an error.
 (define (find-suitable-variant L orig-stx expected-space
                                vname pats pattern? variance bound-vars options)
   (define (check-space s [on-fail (λ () (values #f #f #f))])
     (match s
       [(User-Space c _ _)
        (define-values (v ns nl?)
          (let search ([c c])
            (match-define (with-orig-stx v core _) c)
            (match v
              [(Variant _ (== vname free-identifier=?) _ _ _)
               (syntax-parse pats
                 [(~var ps (Patterns L (vector->list (Variant-Components v)) pattern? variance
                                     bound-vars options))
                  (values
                   (with-orig-stx (variant c (list->vector (attribute ps.values)))
                                  #`(variant #,core
                                             (vector . #,(map with-orig-stx-core
                                                              (attribute ps.values))))
                                  orig-stx)
                   (attribute ps.new-scope)
                   (attribute ps.non-linear?))]
                 [_ (values #f #f #f)])]
              [(∪ _ cs) (let exists ([cs cs])
                          (match cs
                            ['() (values #f #f #f)]
                            [(cons c cs)
                             (define-values (v ns nl?) (search c))
                             (if v
                                 (values v ns nl?)
                                 (exists cs))]))]
              [_ (values #f #f #f)])))
        (if v
            (values v ns nl?)
            (on-fail))]
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
     (match-define (Language spaces order options) L)
     (define (search itr best-space best best-new-scope best-non-linear?)
       (cond
        [itr
         (define s (with-orig-stx-v (free-id-table-iterate-value spaces itr)))
         (define-values (v ns nl?) (check-space s))
         ;; Look for all matching definitions of the Variant name,
         ;; and choose the tightest match (smallest in the refinement order)
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
         (values best best-new-scope best-non-linear?)]))
     (search (free-id-table-iterate-first spaces) #f #f #f #f)]))

 (define-syntax-class (Patterns L ex-components pattern? variance bound-vars options)
   #:attributes (values non-linear? new-scope)
   (pattern ()
            #:fail-unless (or (null? ex-components)
                              (not ex-components))
            (format "Expected more components ~a" ex-components)
            #:attr values '()
            #:attr non-linear? #f
            #:attr new-scope bound-vars)
   (pattern ((~fail #:when (null? ex-components)
                    "Expected fewer components")
             (~var p (Pattern L (and (not pattern?) ;; FIXME: what about the pattern case?
                                     (car ex-components))
                              pattern? variance bound-vars options))
             .
             (~var ps (Patterns L (and (not pattern?) (cdr ex-components))
                                pattern? variance
                                (attribute p.new-scope)
                                options)))
            #:attr values (cons (attribute p.value) (attribute ps.values))
            #:attr non-linear? (or (attribute p.non-linear?) (attribute ps.non-linear?))
            #:attr new-scope (attribute ps.new-scope)))

 ;; TODO
 (define (expectations-agree? L exp-space/component space variance)
   #t)

 (define-splicing-syntax-class match-mode
   #:attributes (mode)
   (pattern #:first #:attr mode 'first)
   (pattern #:all #:attr mode 'all)
   (pattern #:best #:attr mode 'best)
   (pattern (~seq) #:attr mode #f))

 ;; Patterns and terms are similar. Rvars are allowed in terms, Name/Space in patterns.
 (define-syntax-class (Pattern L expected pattern? variance bound-vars options)
   #:literal-sets (pat-ids)
   #:attributes (value non-linear? new-scope)
   #:local-conventions ([#rx".*-c$" (Component-cls (get-space-names L) #f #f options)])
   (pattern (~and orig-stx (~or b:boolean ((~literal quote) b:boolean)))
            #:attr value (with-orig-stx (syntax-e #'b) #'b #'orig-stx)
            #:attr non-linear? #f
            #:attr new-scope bound-vars)
   (pattern (~and orig-stx l:literal-data)
            #:attr value (with-orig-stx
                          (Datum (attribute l.value))
                          #`(Datum l.stx)
                          #'orig-stx)
            #:attr non-linear? #f
            #:attr new-scope bound-vars)
   (pattern (~and orig-stx (is-a e-c))
            #:fail-unless (implies expected
                                   (expectations-agree?
                                    L
                                    expected
                                    (attribute e-c.value)
                                    variance))
            (format "Expected space ~a but binder expects ~a"
                    expected
                    (syntax->datum (with-orig-stx-core (attribute e-c.value))))
            #:attr value (with-orig-stx (is-a (attribute e-c.value))
                                        #`(is-a #,(with-orig-stx-core (attribute e-c.value)))
                                        #'orig-stx)
            #:attr non-linear? #f
            #:attr new-scope bound-vars)
   (pattern (~and orig-stx
                  (Name v:id (~var p (Pattern L expected #t variance bound-vars options))))
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
                                     (~var k (Pattern L #f #t (not variance) bound-vars options))
                                     (~var v (Pattern L #f #t variance (attribute k.new-scope) options))
                                     (~var m (Pattern L #f #t variance (attribute v.new-scope) options))
                                     mode:match-mode
                                     (~optional
                                      (~seq #:expect
                                            (~var m-c
                                                  (Component-cls (get-space-names L) #f #f
                                                                 options))))))
            #:do [(define resolved
                    (and (attribute m-c)
                         (resolve-space
                          (Language-spaces L)
                          (with-orig-stx-v (attribute m-c.value))
                          #:expect-component #t)))]
            #:fail-when (and resolved
                             (not (Map? (with-orig-stx-v resolved))))
            (format "Expected a Map component, got ~a" (syntax->datum (with-orig-stx-core resolved)))
            #:do [(define mpointer
                    (or expected
                        (attribute m-c.value)))]
            #:attr value (with-orig-stx
                          (Map-with (attribute k.value)
                                    (attribute v.value)
                                    (attribute m.value)
                                    (attribute mode.mode)
                                    (or resolved expected))
                          #`(Map-with #,(with-orig-stx-core (attribute m.value))
                                      #,(with-orig-stx-core (attribute k.value))
                                      #,(with-orig-stx-core (attribute v.value))
                                      '#,(attribute mode.mode)
                                      #,(and resolved (with-orig-stx-core resolved)))
                          #'orig-stx)
            #:attr non-linear? (or (attribute m.non-linear?)
                                   (attribute k.non-linear?)
                                   (attribute v.non-linear?))
            #:attr new-scope (attribute m.new-scope))

   (pattern (~and orig-stx (Set-with ~! (~fail #:unless pattern?
                                               "Set-with for use only in pattern position")
                                     (~var v (Pattern L #f #t variance bound-vars options))
                                     (~var s (Pattern L #f #t variance (attribute v.new-scope) options))
                                     mode:match-mode
                                     (~optional
                                      (~seq #:expect
                                            (~var s-c
                                                  (Component-cls (get-space-names L) #f #f
                                                                 options))))))
            #:do [(define resolved
                    (and (attribute s-c)
                         (resolve-space
                          (Language-spaces L)
                          (with-orig-stx-v (attribute s-c.value))
                          #:expect-component #t)))]
            #:fail-when (and resolved
                             (not (℘? (with-orig-stx-v resolved))))
            (format "Expected a ℘ component, got ~a" (syntax->datum (with-orig-stx-core resolved)))
            #:attr value (with-orig-stx
                          (Set-with (attribute v.value)
                                    (attribute s.value)
                                    (attribute mode.mode)
                                    (or resolved expected))
                          #`(Set-with #,(with-orig-stx-core (attribute s.value))
                                      #,(with-orig-stx-core (attribute v.value))
                                      '#,(attribute mode.mode)
                                      #,(and resolved (with-orig-stx-core resolved)))
                          #'orig-stx)
            #:attr non-linear? (or (attribute s.non-linear?)
                                   (attribute v.non-linear?))
            #:attr new-scope (attribute s.new-scope))

   (pattern (~and orig-stx ((~optional variant) vname:id ps:expr ...))
            #:do [(define es (resolve-space (Language-spaces L) expected))]
            #:fail-when (and es
                             (not (User-Space? (with-orig-stx-v es))))
            "Expected non-user space. Got a variant."
            #:do [(define-values (var found-new-scope found-non-linear?)
                    (find-suitable-variant L #'orig-stx
                                           es
                                           #'vname
                                           (syntax->list #'(ps ...))
                                           pattern? variance
                                           bound-vars
                                           options))]
            #:attr value var
            #:attr non-linear? found-non-linear?
            #:attr new-scope found-new-scope)

   (pattern (~and orig-stx (~or (~literal _) Any))
            #:attr value (with-orig-stx -Anything #'-Anything #'orig-stx)
            #:attr non-linear? #f
            #:attr new-scope bound-vars)

   (pattern (~and orig-stx [#:external name:id v:expr])
            #:do [(define E
                    (match (free-id-table-ref (Language-spaces L) #'name #f)
                      [(and wos (with-orig-stx (? External-Space?) _ _))
                       wos]
                      [_ #f]))]
            #:fail-unless E
            (format "Expected the name of an external space, got ~a" (syntax-e #'name))
            #:attr value (with-orig-stx
                          (external E (eval-syntax #'v))
                          #`(external #,(with-orig-stx-core E) v)
                          #'orig-stx)
            #:attr non-linear? #f
            #:attr new-scope bound-vars)

   ;; Unwrapped names (say, v) are treated as (Name x _) if in matching position.
   ;; If space names are punned, in matching position, and the name coincides with a
   ;; space name in the language, then x is instead (is-a x).
   ;; If not in matching position, x is always (Rvar x).
   (pattern v:id
            #:do [(define the-space
                    (and 
                     ;; Space names are to be replaced with (is-a Space-name)?
                     (Options-pun-space? options)
                     ;; not shadowed by an explicit name?
                     (not (free-id-table-has-key? bound-vars #'v))
                     ;; is an actual space name? (otherwise it's just a binder)
                     (free-id-table-has-key? (Language-spaces L) #'v)
                     (with-orig-stx
                      (Space-reference 'concrete #f #f #'v)
                      #`(Space-reference 'concrete #f #f 'v)
                      #'v)))]
            #:fail-unless (or pattern? the-space
                              (free-id-table-has-key? bound-vars #'v))
            (format "Unbound variable reference ~a" (syntax-e #'v))
            #:attr value (if pattern?
                             (if the-space
                                 (with-orig-stx
                                  (is-a the-space)
                                  #`(is-a #,(with-orig-stx-core the-space))
                                  #'v)
                                 (with-orig-stx
                                  (Name #'v (with-orig-stx -Anything #'-Anything #'v))
                                  #`(Name 'v -Anything)
                                  #'v))
                             (with-orig-stx (Rvar #'v) #`(Rvar 'v) #'v))
            #:attr non-linear? (free-id-table-has-key? bound-vars #'v)
            #:attr new-scope (free-id-table-set bound-vars #'v #t)))

 ;; Simple syntax for finite functions / maps
 (define-syntax-class mapsto [pattern (~or (~datum ->) (~datum →) (~datum ↦))])

 (define-syntax-class Externalize
   #:attributes (externalize?)
   (pattern #:do-not-externalize #:attr externalize? #f)
   (pattern #:externalize #:attr externalize? #t))

 (define-syntax-class (Component-cls Space-names trust-rec? trust-con? options)
   #:attributes (value)
   #:literal-sets (component-lits)
   #:local-conventions ([#rx".*-c$" (Component-cls Space-names trust-rec? trust-con? options)])
   (pattern (~and orig-stx
                  (~or
                   (dom-c _:mapsto rng-c)
                   ((~or _:mapsto Map) dom-c rng-c)
                   [(~or ((~or arr:mapsto Map) dom-c rng-c)
                         (dom-c arr:mapsto rng-c))
                    x:Externalize]))
            #:do [(define domv (attribute dom-c.value))
                  (define rngv (attribute rng-c.value))
                  (define pc (pc⊔ (Component-pc (with-orig-stx-v domv))
                                  (Component-pc (with-orig-stx-v rngv))))
                  (define ex (if (attribute x)
                                 (attribute x.externalize?)
                                 (Options-externalize? options)))]
            #:attr value
            (with-orig-stx (Map pc ex domv rngv)
                           #`(Map '#,pc
                                  #,ex
                                  #,(with-orig-stx-core (attribute dom-c.value))
                                  #,(with-orig-stx-core (attribute rng-c.value)))
                           #'orig-stx))
   (pattern (~and orig-stx (Address-Space space:id
                                          behaviors:Behaviors))
            #:do [(define match-behavior
                    (or (attribute behaviors.match-behavior)
                        (or (attribute behaviors.equal-behavior)
                            (Options-match-default options))))
                  (define equal-behavior
                    (or (attribute behaviors.equal-behavior)
                        (Options-equal-default options)))]
            #:attr value (with-orig-stx
                          (Address-Space (syntax-e #'space) match-behavior equal-behavior)
                          #`(Address-Space 'space '#,match-behavior '#,equal-behavior)
                          #'orig-stx))
   (pattern (~and orig-stx (~or ((~or ℘ Setof) ~! s-c)
                                [((~or ℘ Setof) ~! s-c) x:Externalize]))
            #:do [(define pc (Component-pc (with-orig-stx-v (attribute s-c.value))))
                  (define ex (if (attribute x)
                                 (attribute x.externalize?)
                                 (Options-externalize? options)))]
            #:attr value (with-orig-stx
                          (℘ pc ex (attribute s-c.value))
                          #`(℘ '#,pc #,ex #,(with-orig-stx-core (attribute s-c.value)))
                          #'orig-stx))
   (pattern (~and orig-stx Bool)
            #:attr value (with-orig-stx -Bool #'-Bool #'orig-stx))
   (pattern (~and orig-stx ((~or ∪ U Union) ~! (~between cs-c 1 +inf.0) ...))
            #:do [(define pc
                    (for/pc⊔ ([c (in-list (attribute cs-c.value))])
                             (Component-pc (with-orig-stx-v c))))]
            #:attr value
            (if (null? (cdr (attribute cs-c.value)))
                (car (attribute cs-c.value))
                (with-orig-stx
                 (∪ pc (attribute cs-c.value))
                 #`(∪ '#,pc (list . #,(map with-orig-stx-core (attribute cs-c.value))))
                 #'orig-stx)))
   (pattern (~and orig-stx (constructor:id cs-c ...))
            #:fail-when (pat-reserved? #'constructor)
            (format "Name reserved for the pattern language ~a" (syntax-e #'constructor))
            #:fail-when (comp-reserved? #'constructor)
            (format "Name reserved for the component language ~a" (syntax-e #'constructor))
            #:do [(define pc
                    (for/pc⊔ ([c (in-list (attribute cs-c.value))])
                             (Component-pc (with-orig-stx-v c))))]
            #:attr value
            (with-orig-stx
             (Variant pc
                      #'constructor
                      (list->vector (attribute cs-c.value))
                      trust-rec? trust-con?)
             #`(Variant '#,pc
                        'constructor
                        (vector #,@(map with-orig-stx-core (attribute cs-c.value)))
                        #,trust-rec?
                        #,trust-con?)
             #'orig-stx))
   (pattern (~and orig-stx (~or (~literal _) Any))
            #:attr value (with-orig-stx -Anything #'-Anything #'orig-stx))
   (pattern (~and orig-stx
                  (~or space:id
                       [space:id
                        behaviors:Behaviors
                        (~fail #:unless (or (attribute behaviors.match-behavior)
                                            (attribute behaviors.equal-behavior)))]
                       [behaviors:Behaviors
                        space:id
                        (~fail #:unless (or (attribute behaviors.match-behavior)
                                            (attribute behaviors.equal-behavior)))]))
            #:fail-unless (free-id-table-has-key? Space-names #'space)
            (format "Unknown space ~a" (syntax-e #'space))
            #:attr value (with-orig-stx
                          (Space-reference
                           'concrete
                           (attribute behaviors.match-behavior)
                           (attribute behaviors.equal-behavior)
                           #'space)
                          #`(Space-reference
                             'concrete
                             '#,(attribute behaviors.match-behavior)
                             '#,(attribute behaviors.equal-behavior)
                             'space)
                          #'orig-stx))
   (pattern (~and orig-stx (~or b:boolean ((~literal quote) b:boolean)))
            #:attr value (with-orig-stx (syntax-e #'b) #'b #'orig-stx))
   (pattern (~and orig-stx l:literal-data)
            #:attr value (with-orig-stx
                          (Datum (attribute l.value))
                          #'(Datum l.stx)
                          #'orig-stx)))

 ;; Right hand side of a space definition [Space . space-inhabitants]
 (define-syntax-class (Space-inhabitants Space-names options)
   #:attributes (value)
   (pattern (~and orig-stx
                  (#:external-space ~! pred:expr
                                    (~or (~optional (~seq #:cardinality card:expr))
                                         (~optional (~and precision
                                                          (~or #:abstract #:discrete #:concrete)))
                                         (~optional (~seq #:equality equality:expr))
                                         (~optional (~seq #:combine combine:expr))
                                         (~optional (~seq #:enumerate enum:expr))
                                         (~optional (~seq #:quine quine:expr))) ...))
            #:do [(define precision*
                    (if (attribute precision)
                        (string->symbol (keyword->string (syntax-e #'precision)))
                        'abstract))
                  (define auto-functions?
                    (not (or (attribute card) (attribute equality) (attribute combine)
                             (attribute enum) (attribute quine))))
                  (define-values (pred* card* equality* combine* enum* quine*)
                    (if auto-functions?
                        (if (eq? 'abstract precision*)
                            (values #'(add-⊤ pred) #'flat-card #'flat-≡ #'flat-⊔ #'in-value #'flat-quine)
                            (values #'(add-℘ pred) #'set-card #'set-≡ #'external-set-⊔ #'in-external-set #'set-quine))
                        (values (attribute pred)
                                (attribute card)
                                (attribute equality)
                                (attribute combine)
                                (attribute enum)
                                (attribute quine))))]
            #:attr value
            (with-orig-stx
             ;; If no combiner is given, the default is non-equal? values go to ⊤.
             ;; Add ⊤ to the predicate.
             (External-Space (eval-syntax pred*)
                             (and card* (eval-syntax card*))
                             precision*
                             (and equality* (eval-syntax equality*))
                             (and combine* (eval-syntax combine*))
                             (and enum* (eval-syntax enum*))
                             (and quine* (eval-syntax quine*)))
             (quasitemplate
              (External-Space #,pred* #,card* '#,precision* #,equality* #,combine* #,enum* #,quine*))
             #'orig-stx))

   ;; A User space is a sequence of components silently composed into a ∪
   (pattern (~and orig-stx
                  ((~or (~optional (~and #:trust-recursion trust-rec))
                        (~optional (~and #:trust-construction trust-con))
                        (~between blah:expr 1 +inf.0))
                   ...)
                  ((~or _:keyword
                        (~var cs (Component-cls Space-names
                                                (syntax? (attribute trust-rec))
                                                (syntax? (attribute trust-con))
                                                options)))
                   ...))
            #:do [(define pc
                    (for/pc⊔ ([c (in-list (attribute cs.value))])
                             (Component-pc (with-orig-stx-v c))))
                  (define ucomp
                    (if (null? (cdr (attribute cs.value)))
                        (car (attribute cs.value))
                        (with-orig-stx
                         (∪ pc (attribute cs.value))
                         #`(∪ '#,pc (list . #,(map with-orig-stx-core (attribute cs.value))))
                         (attribute blah))))]
            #:attr value
            (with-orig-stx (User-Space ucomp
                                       (syntax? (attribute trust-rec))
                                       (syntax? (attribute trust-con)))
                           #`(User-Space #,(with-orig-stx-core ucomp)
                                         #,(syntax? (attribute trust-rec))
                                         #,(syntax? (attribute trust-con)))
                           #'orig-stx)))

 (define-splicing-syntax-class Behaviors
   #:attributes (match-behavior equal-behavior)
   (pattern (~seq
             (~or (~optional (~or (~and #:choose (~bind [match-behavior 'Choose]))
                                  (~and #:deref (~bind [match-behavior 'Deref]))
                                  (~and #:delay (~bind [match-behavior 'Delay]))))
                  (~optional (~or (~and #:structural (~bind [equal-behavior 'Deref]))
                                  (~and #:egal (~bind [equal-behavior 'Identity])))))
             ...)))

 (define-syntax-class (Expression L variance bound-vars Ξ options)
   #:attributes (value)
   #:literal-sets (expr-ids)
   #:local-conventions ([t (Pattern L #f #f variance bound-vars options)]
                        [#rx".*-e$" (Expression L variance bound-vars Ξ options)])
   (pattern (~and orig-stx (Term t))
            #:attr value (with-orig-stx
                          (Term pure no-comp-yet (attribute t.value))
                          #`(Term #,pure no-comp-yet #,(with-orig-stx-core (attribute t.value)))
                          #'orig-stx))
   (pattern (~and orig-stx (~or b:boolean ((~literal quote) b:boolean)))
            #:attr value (with-orig-stx
                          (Term pure (with-orig-stx -Bool #'-Bool #'-Bool)
                                (with-orig-stx (syntax-e #'b) #'b #'orig-stx))
                          #`(Term #,pure -Bool b)
                          #'orig-stx))
   (pattern v:literal-data
            #:attr value (with-orig-stx
                          (Term pure
                                no-comp-yet
                                (with-orig-stx
                                 (Datum (attribute v.value))
                                 #'(Datum v.stx)
                                 #'v.stx))
                          #`(Term #,pure no-comp-yet (Datum v.stx))
                          #'v.stx))

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
                           no-comp-yet
                           (syntax-e #'m) (attribute k-e.value)
                           (not (not (attribute d-e)))
                           (attribute d-e.value))
                          (quasitemplate
                           (Map-lookup #,tag no-comp-yet
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
                          (Map-extend tag no-comp-yet #'m
                                      (attribute k-e.value)
                                      (attribute v-e.value)
                                      (syntax? (attribute trust)))
                          #`(Map-extend #,tag no-comp-yet
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
                          (Map-remove tag no-comp-yet #'m (attribute k-e.value))
                          (quasitemplate
                           (Map-remove #,tag no-comp-yet
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
                          (In-Dom? tag -Bool #'m (attribute k-e.value))
                          (quasitemplate
                           (In-Dom? #,tag -Bool
                                    'm
                                    #,(with-orig-stx-core (attribute k-e.value))))
                          #'orig-stx))

   (pattern (~and orig-stx (Map-empty? ~! m:id))
            #:fail-unless (free-id-table-has-key? bound-vars #'m)
            (format "Unbound map variable ~a" (syntax-e #'m))
            #:attr value (with-orig-stx
                          (Map-empty? many -Bool #'m)
                          (quasitemplate (Map-empty? #,many -Bool 'm))
                          #'orig-stx))

   (pattern (~and
             orig-stx
             (Empty-map
              ~!
              (~var m (Component-cls (get-space-names L) #f #f options))))
            #:do [(define resolved
                    (resolve-space (Language-spaces L)
                                   (attribute m.value)
                                   #:expect-component #t))]
            #:fail-unless (Map? (with-orig-stx-v resolved))
            (format "Expected a map component, got ~a" (syntax->datum (with-orig-stx-core resolved)))
            #:attr value (with-orig-stx (Empty-map pure (attribute m.value))
                                        #`(Empty-map #,pure
                                                     #,(with-orig-stx-core (attribute m.value)))
                                        #'orig-stx))

;;; Generic expressions

   (pattern (~and orig-stx (If ~! g-e t-e e-e))
            #:do [(define tag (fxior (pesi g-e.value)
                                     (fxior (pesi t-e.value)
                                            (pesi e-e.value))))]
            #:attr value (with-orig-stx
                          (If tag no-comp-yet
                              (attribute g-e.value) (attribute t-e.value) (attribute e-e.value))
                          #`(If #,tag no-comp-yet
                                #,(with-orig-stx-core (attribute g-e.value))
                                #,(with-orig-stx-core (attribute t-e.value))
                                #,(with-orig-stx-core (attribute e-e.value)))
                          #'orig-stx))
   (pattern (~and orig-stx
                  (Let ~! (~var bscs (Bindings L variance bound-vars Ξ options))
                       (~var body (Expression L variance (attribute bscs.new-scope) Ξ options))))
            #:do [(define tag (fxior (attribute bscs.interaction)
                                     (pesi body.value)))
                  (define bscs-v
                    (with-orig-stx
                     (BSCS (attribute bscs.interaction) (attribute bscs.value))
                     #`(BSCS #,(attribute bscs.interaction)
                             (list . #,(map with-orig-stx-core (attribute bscs.value))))
                     (map with-orig-stx-surface-stx (attribute bscs.value))))]
            #:attr value
            (with-orig-stx (Let tag no-comp-yet bscs-v (attribute body.value))
                           #`(Let #,tag no-comp-yet
                                  #,(with-orig-stx-core bscs-v)
                                  #,(with-orig-stx-core (attribute body.value)))
                           #'orig-stx))
   (pattern (~and orig-stx
                  (Match ~! d-e
                         (~and rule-stxs
                               [(~var p (Pattern L #f #t variance bound-vars options))
                                rhs-raw .
                                (~var bscs (Bindings L variance (attribute p.new-scope) Ξ options))])
                         ...))
            #:do [(define-values (rev-rhs si)
                    (for/fold ([rev-rhs '()] [si (pesi d-e.value)])
                        ([rhs (in-list (attribute rhs-raw))]
                         [bscsns (in-list (attribute bscs.new-scope))]
                         [bscssi (in-list (attribute bscs.interaction))])
                      (syntax-parse rhs
                        [(~var rhs (Pattern L #f #f variance bscsns options))
                         (values (cons (attribute rhs.value) rev-rhs)
                                 (fxior si bscssi))])))
                  (define rhss (reverse rev-rhs))
                  (define rules
                    (for/list ([rule-stx (in-list (attribute rule-stxs))]
                               [pat (in-list (attribute p.value))]
                               [rhs (in-list rhss)]
                               [bscsv (in-list (attribute bscs.value))]
                               [bscssi (in-list (attribute bscs.interaction))])
                      (with-orig-stx
                       (Rule #f pat rhs (BSCS bscssi bscsv) no-comp-yet no-comp-yet)
                       #`(Rule #f
                               #,(with-orig-stx-core pat)
                               #,(with-orig-stx-core rhs)
                               (BSCS
                                #,bscssi
                                (list . #,(map with-orig-stx-core bscsv)))
                               no-comp-yet
                               no-comp-yet)
                       rule-stx)))]
            #:attr value (with-orig-stx (Match si no-comp-yet (attribute d-e.value) rules)
                                        #`(Match #,si no-comp-yet
                                                 #,(with-orig-stx-core (attribute d-e.value))
                                                 (list . #,(map with-orig-stx-core rules)))
                                        #'orig-stx))
   (pattern (~and orig-stx (Equal ~! l-e r-e))
            #:do [(define tag ;; can fail and can be approximate.
                    (fxior read/many
                           (fxior (pesi l-e.value) (pesi r-e.value))))]
            #:attr value
            (with-orig-stx
             (Equal tag -Bool (attribute l-e.value) (attribute r-e.value))
             #`(Equal #,tag -Bool
                      #,(with-orig-stx-core (attribute l-e.value))
                      #,(with-orig-stx-core (attribute r-e.value)))
             #'orig-stx))
   (pattern (~and orig-stx (Choose ~! (~or (~optional (~and #:label ℓ:id)) (~once s-e)) ...))
            #:do [(define tag (add-many (pesi s-e.value)))
                  (define label (if (attribute ℓ) (syntax-e #'ℓ) (gensym)))]
            #:attr value
            (with-orig-stx
             (Choose tag no-comp-yet label (attribute s-e.value))
             #`(Choose #,tag no-comp-yet '#,label
                       #,(with-orig-stx-core (attribute s-e.value)))
             #'orig-stx))

;;; Set expressions

   (pattern (~and orig-stx (Empty-set ~! (~var c (Component-cls (get-space-names L) #f #f options))))
            #:do [(define resolved
                    (resolve-space (Language-spaces L)
                                   (attribute c.value)
                                   #:expect-component #t))]
            #:fail-unless (℘? (with-orig-stx-v resolved))
            (format "Expected a ℘ component, got ~a" (syntax->datum (with-orig-stx-core resolved)))
            #:attr value (with-orig-stx (Empty-set pure (attribute c.value))
                                        #`(Empty-set #,pure
                                                     #,(with-orig-stx-core (attribute c.value)))
                                        #'orig-stx))

   (pattern (~and orig-stx ((~and head
                                  (~or (~and Set-Union
                                             (~bind [constr Set-Union]))
                                       (~and Set-Add*
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
             ((attribute constr) tag no-comp-yet (attribute s-e.value) (attribute v-e.value))
             #`(head #,tag no-comp-yet
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
             (In-Set? tag -Bool (attribute s-e.value) (attribute v-e.value))
             #`(In-Set? #,tag -Bool
                        #,(with-orig-stx-core (attribute s-e.value))
                        #,(with-orig-stx-core (attribute v-e.value)))
             #'orig-stx))
   (pattern (~and orig-stx (Set-empty? ~! s-e))
            #:do [(define tag
                    (add-many ;; can be approximate, and may indirect through store to check equality
                     (pesi s-e.value)))]
            #:attr value
            (with-orig-stx
             (Set-empty? tag -Bool (attribute s-e.value))
             #`(Set-empty? #,tag -Bool #,(with-orig-stx-core (attribute s-e.value)))
             #'orig-stx))

;;; Store expressions
   (pattern (~and orig-stx (Store-lookup ~! k-e))
            #:do [(define tag (add-reads (pesi k-e.value)))]
            #:attr value (with-orig-stx
                          (Store-lookup tag no-comp-yet (attribute k-e.value))
                          #`(Store-lookup #,tag no-comp-yet
                                          #,(with-orig-stx-core (attribute k-e.value)))
                          #'orig-stx))
   (pattern (~and orig-stx
                  (Alloc space:id
                         (~or (~once behaviors:Behaviors)
                              (~optional hint:expr)) ...))
            #:do [(define match-behavior
                    (or (attribute behaviors.match-behavior)
                        (Options-match-default options)))
                  (define equal-behavior
                    (or (attribute behaviors.equal-behavior)
                        (Options-equal-default options)))
                  (define AS-stx
                    (with-orig-stx
                     (Address-Space (syntax-e #'space) match-behavior equal-behavior)
                     #`(Address-Space 'space '#,match-behavior '#,equal-behavior)
                     #'orig-stx))]
            #:attr value
            (with-orig-stx
             (Alloc allocs AS-stx (syntax-e #'space)
                    match-behavior equal-behavior
                    (if (attribute hint) (eval-syntax #'hint) -unmapped))
             (quasitemplate (Alloc #,allocs
                                   #,(with-orig-stx-core AS-stx)
                                   'space '#,match-behavior '#,equal-behavior
                                   (?? hint -unmapped)))
             #'orig-stx))
   (pattern (~and orig-stx Unsafe-store-space-ref)
            #:attr value (with-orig-stx
                          (Unsafe-store-ref pure -Anything)
                          #`(Unsafe-store-ref #,pure -Anything)
                          #'orig-stx))
   (pattern (~and orig-stx (Unsafe-store-ref space:id))
            #:attr value (with-orig-stx
                          (Unsafe-store-space-ref pure -Anything (syntax-e #'space))
                          #`(Unsafe-store-space-ref #,pure -Anything 'space)
                          #'orig-stx))

   (pattern (~and orig-stx
                  (~or (~and ??? (~bind [label-stx #'"TODO"]))
                       (??? label-stx:expr)))
            #:attr value (with-orig-stx
                          (??? pure -Anything (eval-syntax #'label-stx))
                          #`(??? #,pure -Anything label-stx)
                          #'orig-stx))

   (pattern (~and orig-stx (mf:id t))
            #:fail-unless (free-id-table-has-key? Ξ #'mf)
            (format "Meta-function not in scope ~a" (syntax-e #'mf))
            #:attr value (with-orig-stx
                          (Meta-function-call read/write/alloc/many no-comp-yet
                                              #'mf (attribute t.value))
                          #`(Meta-function-call #,read/write/alloc/many no-comp-yet
                                                'mf #,(with-orig-stx-core (attribute t.value)))
                          #'orig-stx))

   ;; Common case is just referencing pattern variables, so make the term wrapping automatic.
   (pattern v:id
            #:fail-unless (free-id-table-has-key? bound-vars #'v)
            (format "Variable not in scope ~a" (syntax-e #'v))
            #:attr value (with-orig-stx (Term pure
                                              no-comp-yet
                                              (with-orig-stx
                                               (Rvar #'v)
                                               #`(Rvar 'v)
                                               #'v))
                                        #`(Term #,pure no-comp-yet (Rvar 'v))
                                        #'v)))

 (define-syntax-class (BSC L variance bound-vars Ξ options)
   #:attributes (value new-scope interaction)
   #:literals (where when update)
   #:description "A binding/side-condition/store-update"
   #:commit
   #:local-conventions ([#rx".*-e$" (Expression L variance bound-vars Ξ options)])
   (pattern (~and orig-stx (where ~!
                                  (~var p (Pattern L #f #t variance bound-vars options))
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

 (define-syntax-class (Bindings L variance bound-vars Ξ options)
   #:attributes (new-scope value interaction)
   #:commit
   (pattern (~and orig-stx ()) #:attr new-scope bound-vars
            #:attr value '()
            #:attr interaction pure)
   (pattern (~and orig-stx
                  ((~var bsc (BSC L variance bound-vars Ξ options)) .
                   (~var bscs (Bindings L variance (attribute bsc.new-scope) Ξ options))))
            #:attr value (cons (attribute bsc.value) (attribute bscs.value))
            #:attr new-scope (attribute bscs.new-scope)
            #:attr interaction (fxior (attribute bsc.interaction)
                                      (attribute bscs.interaction))))
 )
